//! Reads GQL source text back into derivation trees of the ISO grammar, so sentences we did
//! not generate (an engine's own tests, another suite) can be verified and measured with the
//! same coverage as ours.
//!
//! Two levels, as 21.3 defines them: the lexical definitions over characters make tokens, the
//! syntactic definitions over tokens make the tree. Both run on libmarpa (Kegler's Earley
//! parser), which takes any context-free grammar, ambiguous ones included, and tokens of any
//! length at any position. So lexing never decides what only the syntax can: every token that
//! can start at a position is offered, and the syntactic grammar keeps the ones it can use
//! (`->` against `-` `>`, `TYPE` as a keyword or an identifier). Lexing applies only the rules
//! that are about tokens:
//!
//! - 21.3 SR 14: a <non-delimiter token> is followed by a <delimiter token> or a <separator>,
//!   so `RETURN1` is one identifier, not `RETURN 1`
//! - 21.3 SR 18: a <non-delimited identifier> is no <reserved word>
//! - 21.3 SR 25: keywords are read with simple Latin lower-case letters as upper-case
//! - prose leaves ("!! See the Syntax Rules") are read by the verifier's own rule for them
//!
//! What the parser does not decide is ambiguity the ISO grammar leaves to its Syntax Rules (a
//! `<value expression>` is several things at once until types say which). It returns the
//! first tree the verifier accepts and says how many it looked at.

use crate::cfg::{Cfg, Lit, LitId, NtId, ProdId, Sym};
use crate::tokens::Grammar as Tokens;
use crate::tree::Node;
use crate::verify::{Span, leaf_rule, leaf_span};
use anyhow::{Result, anyhow};
use marpa_asf::thin::{Bocage, Event, Grammar, Order, Recognizer, Rule, Step, Symbol, Tree};
use std::collections::{HashMap, HashSet};

/// What a terminal symbol of either level reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Terminal {
    /// Syntactic: a keyword or other literal token.
    Lit(LitId),
    /// Syntactic: a token of a lexical definition.
    Token(NtId),
    /// Syntactic: a <separator>.
    Separator,
    /// Lexical: one character.
    Char(char),
    /// Lexical: one simple Latin letter, either case (21.3 SR 25).
    Letter(char),
    /// Lexical: a prose leaf, any length its Syntax Rule allows.
    Prose(LitId),
}

/// What a rule of either level builds.
#[derive(Debug, Clone, Copy)]
enum Built {
    /// A production of the ISO grammar.
    Prod(ProdId),
    /// A literal spelled out in characters.
    Spelled(LitId),
    /// A wrapper whose tree is its last child: `t`, `<separator> t`, the start with a trailing
    /// separator, or the lexical start over its alternatives.
    Last,
    /// The start followed by a separator.
    First,
}

/// One libmarpa grammar over part of the ISO grammar.
struct Level {
    grammar: Grammar,
    built: HashMap<Rule, Built>,
    terminals: HashMap<Symbol, Terminal>,
    symbols: HashMap<Terminal, Symbol>,
    /// Back from symbols to the nonterminals they stand for, for nulled ones.
    nts: HashMap<Symbol, NtId>,
}

impl Level {
    fn new() -> Result<Level> {
        Ok(Level {
            grammar: Grammar::new()?,
            built: HashMap::new(),
            terminals: HashMap::new(),
            symbols: HashMap::new(),
            nts: HashMap::new(),
        })
    }

    fn terminal(&mut self, t: Terminal) -> Result<Symbol> {
        if let Some(&s) = self.symbols.get(&t) {
            return Ok(s);
        }
        let s = self.grammar.new_symbol()?;
        self.symbols.insert(t, s);
        self.terminals.insert(s, t);
        Ok(s)
    }

    /// Adds a rule unless the same one is there, which libmarpa refuses: the ISO grammar
    /// has a few alternatives that desugar alike.
    fn rule(
        &mut self,
        seen: &mut HashSet<(Symbol, Vec<Symbol>)>,
        lhs: Symbol,
        rhs: Vec<Symbol>,
        built: Built,
    ) -> Result<()> {
        if seen.insert((lhs, rhs.clone())) {
            let r = self.grammar.new_rule(lhs, &rhs)?;
            self.built.insert(r, built);
        }
        Ok(())
    }
}

/// A token found at a position.
#[derive(Debug, Clone)]
struct Token {
    terminal: Terminal,
    len: usize,
    tree: Node,
}

/// What the lexical grammar finds starting at one position.
#[derive(Debug, Default, Clone)]
struct Lexed {
    /// Tokens of the lexical definitions syntactic rules use, and separators.
    tokens: Vec<Token>,
    /// Lengths of a <non-delimiter token> and of a <delimiter token> starting here.
    non_delimiter: HashSet<usize>,
    delimiter: HashSet<usize>,
    /// Whether a <delimiter token> or a <separator> starts here (21.3 SR 14).
    delimits: bool,
}

/// A parsed sentence.
#[derive(Debug)]
pub struct Parsed {
    pub tree: Node,
    /// Trees looked at before one passed `accept`, or all of them up to the limit.
    pub trees: usize,
    /// Whether the returned tree passed `accept`.
    pub accepted: bool,
    /// Whether the sentence has more than one tree.
    pub ambiguous: bool,
}

pub struct Parser<'c> {
    cfg: &'c Cfg,
    syntactic: Level,
    syntactic_start: NtId,
    lexical: Level,
    lexical_start: Symbol,
    separator: NtId,
    non_delimiter: NtId,
    delimiter: NtId,
    /// Lexical definitions syntactic rules name, read as one token.
    boundary: HashSet<NtId>,
    /// Literals of syntactic rules, read as one token.
    literals: Vec<LitId>,
    reserved: HashSet<String>,
    /// For each nullable nonterminal, an empty derivation.
    empty: HashMap<NtId, Node>,
    /// Trees to look at per sentence for one `accept` takes.
    pub limit: usize,
}

impl<'c> Parser<'c> {
    pub fn new(cfg: &'c Cfg, tokens: &Tokens, start: &str) -> Result<Parser<'c>> {
        let start = cfg.require(start)?;
        let separator = cfg.require("separator")?;
        let non_delimiter = cfg.require("non-delimiter token")?;
        let delimiter = cfg.require("delimiter token")?;
        let lexical = |nt: NtId| cfg.nts[nt as usize].lexical;

        // The syntactic definitions: reachable from the start without entering a token.
        let mut syntactic_nts = Vec::new();
        let mut seen = vec![false; cfg.nts.len()];
        let mut stack = vec![start];
        let mut boundary = HashSet::new();
        let mut literals = HashSet::new();
        while let Some(nt) = stack.pop() {
            if std::mem::replace(&mut seen[nt as usize], true) {
                continue;
            }
            syntactic_nts.push(nt);
            for &p in &cfg.nts[nt as usize].prods {
                for &sym in &cfg.prod(p).rhs {
                    match sym {
                        Sym::Nt(x) if lexical(x) => {
                            boundary.insert(x);
                        }
                        Sym::Nt(x) => stack.push(x),
                        Sym::Lit(l) => {
                            literals.insert(l);
                        }
                    }
                }
            }
        }

        let mut syn = Level::new()?;

        let mut nt_sym = HashMap::new();
        let mut rules = HashSet::new();
        for &nt in &syntactic_nts {
            let s = syn.grammar.new_symbol()?;
            nt_sym.insert(nt, s);
            syn.nts.insert(s, nt);
        }
        let separator_sym = syn.terminal(Terminal::Separator)?;
        // Each token may be preceded by a separator: `t'` is `t` or `<separator> t`.
        let mut wrapped: HashMap<Terminal, Symbol> = HashMap::new();
        let mut wrap = |syn: &mut Level, rules: &mut HashSet<_>, t: Terminal| -> Result<Symbol> {
            if let Some(&w) = wrapped.get(&t) {
                return Ok(w);
            }
            let s = syn.terminal(t)?;
            let w = syn.grammar.new_symbol()?;
            syn.rule(rules, w, vec![s], Built::Last)?;
            syn.rule(rules, w, vec![separator_sym, s], Built::Last)?;
            wrapped.insert(t, w);
            Ok(w)
        };
        for &nt in &syntactic_nts {
            for &p in &cfg.nts[nt as usize].prods {
                let mut rhs = Vec::new();
                for &sym in &cfg.prod(p).rhs {
                    rhs.push(match sym {
                        Sym::Nt(x) if lexical(x) => wrap(&mut syn, &mut rules, Terminal::Token(x))?,
                        Sym::Nt(x) => nt_sym[&x],
                        Sym::Lit(l) => wrap(&mut syn, &mut rules, Terminal::Lit(l))?,
                    });
                }
                syn.rule(&mut rules, nt_sym[&nt], rhs, Built::Prod(p))?;
            }
        }
        // A sentence may end in a separator.
        let top = syn.grammar.new_symbol()?;
        syn.rule(&mut rules, top, vec![nt_sym[&start]], Built::Last)?;
        syn.rule(
            &mut rules,
            top,
            vec![nt_sym[&start], separator_sym],
            Built::First,
        )?;
        syn.grammar.set_start_symbol(top)?;
        syn.grammar.precompute()?;

        // The lexical definitions, over characters.
        let mut lex = Level::new()?;

        let mut nt_sym = HashMap::new();
        let mut rules = HashSet::new();
        let lexical_nts: Vec<NtId> = (0..cfg.nts.len() as NtId).filter(|&n| lexical(n)).collect();
        for &nt in &lexical_nts {
            let s = lex.grammar.new_symbol()?;
            nt_sym.insert(nt, s);
            lex.nts.insert(s, nt);
        }
        let mut spelled: HashMap<LitId, Symbol> = HashMap::new();
        for &nt in &lexical_nts {
            for &p in &cfg.nts[nt as usize].prods {
                let mut rhs = Vec::new();
                for &sym in &cfg.prod(p).rhs {
                    rhs.push(match sym {
                        Sym::Nt(x) => *nt_sym.get(&x).ok_or_else(|| {
                            anyhow!("<{}> is lexical but <{}> is not", cfg.name(nt), cfg.name(x))
                        })?,
                        Sym::Lit(l) => match &cfg.lits[l as usize] {
                            Lit::Opaque(_) => lex.terminal(Terminal::Prose(l))?,
                            Lit::Kw(text) | Lit::Term(text) => {
                                if let Some(&s) = spelled.get(&l) {
                                    s
                                } else {
                                    let keyword = matches!(cfg.lits[l as usize], Lit::Kw(_));
                                    let mut chars = Vec::new();
                                    for c in text.chars() {
                                        let t = if keyword && c.is_ascii_alphabetic() {
                                            Terminal::Letter(c.to_ascii_uppercase())
                                        } else {
                                            Terminal::Char(c)
                                        };
                                        chars.push(lex.terminal(t)?);
                                    }
                                    let s = lex.grammar.new_symbol()?;
                                    lex.rule(&mut rules, s, chars, Built::Spelled(l))?;
                                    spelled.insert(l, s);
                                    s
                                }
                            }
                        },
                    });
                }
                lex.rule(&mut rules, nt_sym[&nt], rhs, Built::Prod(p))?;
            }
        }
        let lexical_start = lex.grammar.new_symbol()?;
        for &nt in boundary
            .iter()
            .chain(&[separator, non_delimiter, delimiter])
        {
            lex.rule(&mut rules, lexical_start, vec![nt_sym[&nt]], Built::Last)?;
        }
        lex.grammar.set_start_symbol(lexical_start)?;
        lex.grammar
            .symbol_is_completion_event_set(lexical_start, true)?;
        lex.grammar.precompute()?;

        let mut literals: Vec<LitId> = literals.into_iter().collect();
        literals.sort();
        Ok(Parser {
            cfg,
            syntactic: syn,
            syntactic_start: start,
            lexical: lex,
            lexical_start,
            separator,
            non_delimiter,
            delimiter,
            boundary,
            literals,
            reserved: tokens.reserved_words(),
            empty: empty_derivations(cfg),
            limit: 64,
        })
    }

    /// The first tree of `text` that `accept` takes, or the first tree when none does.
    pub fn parse(&self, text: &str, accept: impl Fn(&Node) -> bool) -> Result<Parsed> {
        let chars: Vec<char> = text.chars().collect();
        let mut lexed: Vec<Option<Lexed>> = vec![None; chars.len() + 1];
        let mut offered: Vec<Token> = Vec::new();
        let mut r = Recognizer::new(self.syntactic.grammar.clone())?;
        r.start_input()?;
        for at in 0..chars.len() {
            let set = r.latest_earley_set()?;
            if r.earleme(set)? == at as i32 {
                let expected: HashSet<Terminal> = r
                    .terminals_expected()?
                    .into_iter()
                    .map(|s| self.syntactic.terminals[&s])
                    .collect();
                let tokens = self.tokens_at(&chars, at, &mut lexed, &expected)?;
                for token in tokens {
                    let Some(&sym) = self.syntactic.symbols.get(&token.terminal) else {
                        continue;
                    };
                    if r.terminal_is_expected(sym)? {
                        offered.push(token);
                        r.alternative(
                            sym,
                            offered.len() as i32,
                            offered[offered.len() - 1].len as i32,
                        )?;
                    }
                }
            }
            if r.earleme_complete().is_err() || r.is_exhausted() && at + 1 < chars.len() {
                return Err(self.stuck(&chars, &r));
            }
        }
        let bocage = Bocage::new(&r).map_err(|_| self.stuck(&chars, &r))?;
        let order = Order::new(&bocage)?;
        let ambiguous = order.ambiguity_metric()? > 1;
        let mut first = None;
        let mut trees = 0;
        for value in Tree::new(order)?.take(self.limit) {
            trees += 1;
            let node = self.build(&self.syntactic, value, &offered)?;
            if accept(&node) {
                return Ok(Parsed {
                    tree: node,
                    trees,
                    accepted: true,
                    ambiguous,
                });
            }
            first.get_or_insert(node);
        }
        let tree = first.ok_or_else(|| anyhow!("no tree"))?;
        Ok(Parsed {
            tree,
            trees,
            accepted: false,
            ambiguous,
        })
    }

    fn stuck(&self, chars: &[char], r: &Recognizer) -> anyhow::Error {
        let at = r
            .latest_earley_set()
            .and_then(|s| r.earleme(s))
            .map_or(0, |e| e.max(0) as usize);
        let before: String = chars[..at.min(chars.len())].iter().collect();
        let after: String = chars[at.min(chars.len())..].iter().take(30).collect();
        anyhow!("no iso parse past {at}: {before:?} | {after:?}")
    }

    /// Every token the syntactic level may read at `at`.
    fn tokens_at(
        &self,
        chars: &[char],
        at: usize,
        lexed: &mut [Option<Lexed>],
        expected: &HashSet<Terminal>,
    ) -> Result<Vec<Token>> {
        let here = self.lexed(chars, at, lexed)?.clone();
        let mut out = here.tokens.clone();
        for &l in self
            .literals
            .iter()
            .filter(|&&l| expected.contains(&Terminal::Lit(l)))
        {
            match &self.cfg.lits[l as usize] {
                Lit::Kw(k) | Lit::Term(k) => {
                    let n = k.chars().count();
                    let keyword = matches!(self.cfg.lits[l as usize], Lit::Kw(_));
                    let matches = at + n <= chars.len()
                        && chars[at..at + n].iter().zip(k.chars()).all(|(&c, k)| {
                            c == k
                                || keyword && c.is_ascii_alphabetic() && c.to_ascii_uppercase() == k
                        });
                    if matches {
                        out.push(Token {
                            terminal: Terminal::Lit(l),
                            len: n,
                            tree: Node {
                                sym: Sym::Lit(l),
                                prod: None,
                                text: Some(k.clone()),
                                children: Vec::new(),
                            },
                        });
                    }
                }
                Lit::Opaque(def) => {
                    for text in prose(def, &chars[at..]) {
                        out.push(Token {
                            terminal: Terminal::Lit(l),
                            len: text.chars().count(),
                            tree: Node {
                                sym: Sym::Lit(l),
                                prod: None,
                                text: Some(text),
                                children: Vec::new(),
                            },
                        });
                    }
                }
            }
        }
        // 21.3 SR 14: a non-delimiter token is followed by a delimiter token or a separator.
        let mut kept = Vec::new();
        for token in out {
            let end = at + token.len;
            let non_delimiter =
                here.non_delimiter.contains(&token.len) && !here.delimiter.contains(&token.len);
            if non_delimiter
                && token.terminal != Terminal::Separator
                && end < chars.len()
                && !self.lexed(chars, end, lexed)?.delimits
            {
                continue;
            }
            kept.push(token);
        }
        Ok(kept)
    }

    /// The lexical grammar from `at`, memoized.
    fn lexed<'l>(
        &self,
        chars: &[char],
        at: usize,
        lexed: &'l mut [Option<Lexed>],
    ) -> Result<&'l Lexed> {
        if lexed[at].is_none() {
            lexed[at] = Some(self.lex(chars, at)?);
        }
        Ok(lexed[at].as_ref().unwrap())
    }

    fn lex(&self, chars: &[char], at: usize) -> Result<Lexed> {
        let mut out = Lexed::default();
        let mut r = Recognizer::new(self.lexical.grammar.clone())?;
        r.start_input()?;
        // Token values index (start, length) of what each terminal read.
        let mut read: Vec<(usize, usize)> = Vec::new();
        let mut e = at;
        while e < chars.len() && !r.is_exhausted() {
            let set = r.latest_earley_set()?;
            if r.earleme(set)? == (e - at) as i32 {
                for sym in r.terminals_expected()? {
                    match self.lexical.terminals[&sym] {
                        Terminal::Char(c) if chars[e] == c => {
                            read.push((e, 1));
                            r.alternative(sym, read.len() as i32, 1)?;
                        }
                        Terminal::Letter(c)
                            if chars[e].is_ascii_alphabetic()
                                && chars[e].to_ascii_uppercase() == c =>
                        {
                            read.push((e, 1));
                            r.alternative(sym, read.len() as i32, 1)?;
                        }
                        Terminal::Prose(l) => {
                            let Lit::Opaque(def) = &self.cfg.lits[l as usize] else {
                                unreachable!()
                            };
                            for text in prose(def, &chars[e..]) {
                                let len = text.chars().count();
                                read.push((e, len));
                                r.alternative(sym, read.len() as i32, len as i32)?;
                            }
                        }
                        _ => {}
                    }
                }
            }
            if r.earleme_complete().is_err() {
                break;
            }
            e += 1;
            let completed = r
                .events()?
                .any(|ev| matches!(ev, Event::SymbolCompleted(s) if s == self.lexical_start));
            if !completed {
                continue;
            }
            let set = r.latest_earley_set()?;
            let bocage = Bocage::new_at_set(&r, set)?;
            let len = e - at;
            let mut seen = HashSet::new();
            for value in Tree::new(Order::new(&bocage)?)?.take(self.limit) {
                let node = self.build_lexical(value, &read, chars)?;
                let Sym::Nt(nt) = node.sym else { continue };
                if !seen.insert(nt) {
                    continue;
                }
                if nt == self.non_delimiter {
                    out.non_delimiter.insert(len);
                } else if nt == self.delimiter {
                    out.delimiter.insert(len);
                    out.delimits = true;
                } else if nt == self.separator {
                    out.delimits = true;
                    out.tokens.push(Token {
                        terminal: Terminal::Separator,
                        len,
                        tree: node,
                    });
                } else if self.boundary.contains(&nt) && !self.reserved_identifier(&node) {
                    out.tokens.push(Token {
                        terminal: Terminal::Token(nt),
                        len,
                        tree: node,
                    });
                }
            }
        }
        Ok(out)
    }

    /// 21.3 SR 18: whether a non-delimited identifier in `node` spells a reserved word.
    fn reserved_identifier(&self, node: &Node) -> bool {
        if let Sym::Nt(nt) = node.sym {
            let base = self.cfg.base(nt);
            if base == "regular identifier" || base == "extended identifier" {
                let text = node.render(self.cfg).to_uppercase();
                return self.reserved.contains(&text);
            }
        }
        node.children.iter().any(|c| self.reserved_identifier(c))
    }

    fn build_lexical(
        &self,
        value: marpa_asf::thin::Value,
        read: &[(usize, usize)],
        chars: &[char],
    ) -> Result<Node> {
        let tokens: Vec<Token> = read
            .iter()
            .map(|&(start, len)| Token {
                terminal: Terminal::Separator,
                len,
                tree: Node {
                    sym: Sym::Lit(0),
                    prod: None,
                    text: Some(chars[start..start + len].iter().collect()),
                    children: Vec::new(),
                },
            })
            .collect();
        self.build(&self.lexical, value, &tokens)
    }

    /// A tree from libmarpa's evaluation steps, over the stack they describe.
    fn build(
        &self,
        level: &Level,
        value: marpa_asf::thin::Value,
        tokens: &[Token],
    ) -> Result<Node> {
        let mut stack: Vec<Option<Node>> = Vec::new();
        let put = |stack: &mut Vec<Option<Node>>, i: i32, n: Node| {
            let i = i as usize;
            if stack.len() <= i {
                stack.resize(i + 1, None);
            }
            stack[i] = Some(n);
        };
        for step in value {
            match step {
                Step::Token(sym, at, v) => {
                    let token = &tokens[(v - 1) as usize];
                    let node = match level.terminals[&sym] {
                        // Lexical terminals carry their characters; the rule above them
                        // decides what they are.
                        Terminal::Prose(l) => Node {
                            sym: Sym::Lit(l),
                            ..token.tree.clone()
                        },
                        _ => token.tree.clone(),
                    };
                    put(&mut stack, at, node);
                }
                Step::NullingSymbol(sym, at) => {
                    let nt = level.nts[&sym];
                    put(&mut stack, at, self.empty[&nt].clone());
                }
                Step::Rule(rule, at, last) => {
                    let children: Vec<Node> = (at..=last)
                        .map(|i| {
                            stack[i as usize]
                                .take()
                                .ok_or_else(|| anyhow!("missing child {i}"))
                        })
                        .collect::<Result<_>>()?;
                    let node = match level.built[&rule] {
                        Built::Prod(p) => Node {
                            sym: Sym::Nt(self.cfg.prod(p).lhs),
                            prod: Some(p),
                            text: None,
                            children,
                        },
                        Built::Spelled(l) => Node {
                            sym: Sym::Lit(l),
                            prod: None,
                            text: Some(match &self.cfg.lits[l as usize] {
                                Lit::Kw(k) | Lit::Term(k) => k.clone(),
                                Lit::Opaque(_) => unreachable!(),
                            }),
                            children: Vec::new(),
                        },
                        Built::Last => children
                            .into_iter()
                            .last()
                            .ok_or_else(|| anyhow!("empty wrapper"))?,
                        Built::First => children
                            .into_iter()
                            .next()
                            .ok_or_else(|| anyhow!("empty wrapper"))?,
                    };
                    put(&mut stack, at, node);
                }
                _ => {}
            }
        }
        stack
            .into_iter()
            .next()
            .flatten()
            .ok_or_else(|| anyhow!("empty evaluation"))
    }

    pub fn start(&self) -> NtId {
        self.syntactic_start
    }
}

/// Every prefix of `rest` that is a valid prose leaf of `def`.
fn prose(def: &str, rest: &[char]) -> Vec<String> {
    let mut out = Vec::new();
    let mut text = String::new();
    for &c in rest {
        text.push(c);
        let valid = leaf_rule(def, &text).is_ok();
        if valid {
            out.push(text.clone());
        }
        match leaf_span(def) {
            Span::One => break,
            Span::Run if !valid => break,
            _ => {}
        }
    }
    out
}

/// For each nullable nonterminal, the shortest derivation of the empty string.
fn empty_derivations(cfg: &Cfg) -> HashMap<NtId, Node> {
    let mut empty: HashMap<NtId, Node> = HashMap::new();
    loop {
        let mut grew = false;
        for (p, prod) in cfg.prods.iter().enumerate() {
            if empty.contains_key(&prod.lhs) {
                continue;
            }
            let children: Option<Vec<Node>> = prod
                .rhs
                .iter()
                .map(|s| match s {
                    Sym::Nt(x) => empty.get(x).cloned(),
                    Sym::Lit(_) => None,
                })
                .collect();
            if let Some(children) = children {
                empty.insert(
                    prod.lhs,
                    Node {
                        sym: Sym::Nt(prod.lhs),
                        prod: Some(p as ProdId),
                        text: None,
                        children,
                    },
                );
                grew = true;
            }
        }
        if !grew {
            return empty;
        }
    }
}
