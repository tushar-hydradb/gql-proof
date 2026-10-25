//! The Syntax Rules of graph type specifications (ISO/IEC 39075 18.1, 18.2, 18.3, 18.5, with
//! Cor 1), checked on a `Plain` tree straight from the text.
//!
//! - 18.5 SR 1: the property types simply contained in one <property types specification> have
//!   distinct names, anywhere in the tree
//! - 18.2 SR 7, 18.3 SR 8: a present key label set is disjoint from the implied label set, for
//!   every node and edge type specification, anywhere in the tree
//! - in every <graph type specification body>, over the element type specifications it simply
//!   contains: 18.1 SR 8 (effective key label sets of node types distinct), SR 9 (a node type
//!   implying another is structurally consistent with it), SR 10 (local node type aliases
//!   distinct, a node type name being the alias by Cor 1's 18.2 SR 4 b), SR 11 with 18.3 SR 17
//!   and 18 (every endpoint of an edge type resolves to a node type specification of the body),
//!   SR 14 (edge types sharing an effective key label set agree), SR 16 a and b (an edge type
//!   implying another is structurally and endpoint-consistent with it)
//!
//! "Simply contains" stops at an inner <node type specification>, <edge type specification>,
//! <property types specification> or <graph type specification body>: those are the
//! containers a property value type can nest (a closed node, edge or graph reference value
//! type), and an edge's endpoint fillers are not node type specifications.
//!
//! Readings, each refusing whenever the rule cannot be shown to hold:
//! - names (labels, property names, aliases) compare by representative form (21.3 SR 3, 4):
//!   the default collation (ID022) is taken to equate exactly the equal strings
//! - GG22 (key label set inference) is applied both ways, since the checker does not know the
//!   claim: a violation under either reading is reported, tagged with the reading it needs
//! - a node or edge type is its label set and its property type set (18.2 SR 16, 18.3 SR 19);
//!   two property value types are taken to be the same type, and to combine to themselves under
//!   22.17, only when their trees are identical. So "the same node type" (18.1 SR 11, 18.3 SR
//!   17 c), "the same normal form" (18.3 SR 17 b v, through 18.2 SR 17 a), "the same property
//!   type set" (18.1 SR 14 d) and "structurally consistent" (18.1 SR 7 iv, for SR 9 and 16)
//!   fail on any two value types that are spelled differently, `INT` and `INTEGER` included
//! - an endpoint `( IMPLIES ... )`, a node type key label set with no label set phrase, leaves
//!   18.3 SR 17 b ii without a label set to look up: refused
//! - a key label set that matches several node type specifications (18.3 SR 17 b) is resolved
//!   to the first; 18.1 SR 8 reports the duplicate key

use super::{Plain, Violation, def_name, violation};
use std::collections::{BTreeMap, BTreeSet};

type Labels = BTreeSet<String>;
/// Property name to the shape of its value type's tree.
type Props = BTreeMap<String, String>;

const BOUNDARIES: &[&str] = &[
    "node type specification",
    "edge type specification",
    "property types specification",
    "graph type specification body",
];

pub fn check(tree: &Plain) -> Vec<Violation> {
    let mut out = Vec::new();
    walk(tree, &mut Vec::new(), &mut out);
    out
}

fn walk<'t>(node: &'t Plain, path: &mut Vec<&'t str>, out: &mut Vec<Violation>) {
    let Plain::Def {
        name,
        synthetic,
        children,
    } = node
    else {
        return;
    };
    if !synthetic {
        path.push(name);
        match name.as_str() {
            "property types specification" => distinct_properties(node, path, out),
            "node type specification" => disjoint(node, Kind::Node, "18.2 SR 7", path, out),
            "edge type specification" => disjoint(node, Kind::Edge, "18.3 SR 8", path, out),
            "graph type specification body" => body(node, path, out),
            _ => {}
        }
    }
    children.iter().for_each(|c| walk(c, path, out));
    if !synthetic {
        path.pop();
    }
}

/// Every `<want>` below `node` (not `node` itself), descending into neither a match nor a
/// boundary.
fn below<'t>(node: &'t Plain, wants: &[&str], out: &mut Vec<&'t Plain>) {
    let Plain::Def { children, .. } = node else {
        return;
    };
    for child in children {
        match def_name(child) {
            Some(n) if wants.contains(&n) => out.push(child),
            Some(n) if BOUNDARIES.contains(&n) => {}
            _ => below(child, wants, out),
        }
    }
}

fn first<'t>(node: &'t Plain, want: &str) -> Option<&'t Plain> {
    let mut found = Vec::new();
    below(node, &[want], &mut found);
    found.into_iter().next()
}

/// The name an <identifier> stands for, its representative form (21.3 SR 3, 4): a delimited
/// one without its quotes, doubled quotes undoubled.
pub(crate) fn ident(node: &Plain) -> String {
    fn reps(node: &Plain, out: &mut String) {
        match node {
            Plain::Def { name, .. }
                if name == "double quoted character representation"
                    || name == "accent quoted character representation" =>
            {
                out.push_str(match node.text().as_str() {
                    "\"\"" => "\"",
                    "``" => "`",
                    t => t,
                })
            }
            Plain::Def { children, .. } => children.iter().for_each(|c| reps(c, out)),
            _ => {}
        }
    }
    let mut delimited = Vec::new();
    super::find(node, "delimited identifier", &mut delimited);
    if delimited.is_empty() {
        return node.text();
    }
    let mut out = String::new();
    reps(node, &mut out);
    out
}

/// The tree of a value type as text with its structure, so equal shapes are identical trees.
fn shape(node: &Plain) -> String {
    match node {
        Plain::Def {
            name,
            synthetic,
            children,
        } => {
            let inner: Vec<String> = children.iter().map(shape).collect();
            if *synthetic {
                inner.join(" ")
            } else {
                format!("<{name}>({})", inner.join(" "))
            }
        }
        leaf => format!("{:?}", leaf.text()),
    }
}

/// The label names a <label set phrase> specifies (18.4 SR 1-3).
fn labels(lsp: &Plain) -> Labels {
    let mut names = Vec::new();
    super::find(lsp, "label name", &mut names);
    names.iter().map(|n| ident(n)).collect()
}

/// The property types of a <property types specification>, in order, duplicates kept.
fn property_types(pts: &Plain) -> Vec<(String, String)> {
    let mut types = Vec::new();
    below(pts, &["property type"], &mut types);
    types
        .iter()
        .map(|t| {
            let name = super::own(t, "property name")
                .map(ident)
                .unwrap_or_default();
            let vt = super::own(t, "property value type")
                .map(shape)
                .unwrap_or_default();
            (name, vt)
        })
        .collect()
}

/// 18.5 SR 1.
fn distinct_properties(pts: &Plain, path: &[&str], out: &mut Vec<Violation>) {
    let mut seen = BTreeSet::new();
    let mut reported = BTreeSet::new();
    for (name, _) in property_types(pts) {
        if !seen.insert(name.clone()) && reported.insert(name.clone()) {
            out.push(violation(
                path,
                "18.5 SR 1",
                format!("two property types named {name:?} in one property types specification"),
            ));
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Node,
    Edge,
}

impl Kind {
    fn key(self) -> &'static str {
        match self {
            Kind::Node => "node type key label set",
            Kind::Edge => "edge type key label set",
        }
    }
    fn implied(self) -> &'static str {
        match self {
            Kind::Node => "node type label set",
            Kind::Edge => "edge type label set",
        }
    }
    fn props(self) -> &'static str {
        match self {
            Kind::Node => "node type property types",
            Kind::Edge => "edge type property types",
        }
    }
    fn name(self) -> &'static str {
        match self {
            Kind::Node => "node type name",
            Kind::Edge => "edge type name",
        }
    }
}

/// What a node or edge type specification, or an endpoint's node type filler, simply contains.
struct Content {
    /// The key label set; `None` is "omitted" (18.2 SR 5, 18.3 SR 6).
    key: Option<Labels>,
    /// A <node type key label set> with no <label set phrase> (only matters for endpoints).
    key_without_phrase: bool,
    implied: Labels,
    props: Props,
}

impl Content {
    fn of(node: &Plain, kind: Kind) -> Content {
        let key_lsp = first(node, kind.key()).map(|k| first(k, "label set phrase"));
        let key_without_phrase = matches!(key_lsp, Some(None));
        let key = match key_lsp {
            Some(Some(lsp)) => Some(labels(lsp)),
            Some(None) => Some(Labels::new()),
            None => first(node, kind.name()).map(|n| Labels::from([ident(n)])),
        };
        let implied = first(node, kind.implied())
            .and_then(|s| first(s, "label set phrase"))
            .map(labels)
            .unwrap_or_default();
        let props_list = first(node, kind.props())
            .and_then(|p| super::own(p, "property types specification"))
            .map(property_types)
            .unwrap_or_default();
        let mut props = Props::new();
        for (n, t) in &props_list {
            props.entry(n.clone()).or_insert_with(|| t.clone());
        }
        Content {
            key,
            key_without_phrase,
            implied,
            props,
        }
    }

    /// The label set: key label set union implied label set (18.2 SR 8, 18.3 SR 9).
    fn label_set(&self) -> Labels {
        let mut all = self.implied.clone();
        all.extend(self.key.iter().flatten().cloned());
        all
    }
}

/// 18.2 SR 7, 18.3 SR 8.
fn disjoint(node: &Plain, kind: Kind, rule: &'static str, path: &[&str], out: &mut Vec<Violation>) {
    let c = Content::of(node, kind);
    if let Some(key) = &c.key {
        let both: Vec<_> = key.intersection(&c.implied).collect();
        if !both.is_empty() {
            out.push(violation(
                path,
                rule,
                format!(
                    "label {:?} both in the key label set and the implied label set",
                    both[0]
                ),
            ));
        }
    }
}

/// One endpoint of an edge type specification.
enum Endpoint {
    /// 18.3 SR 17 a.
    Alias(String),
    /// 18.3 SR 17 b and c: the node type filler, possibly empty (`( )`, 18.3 SR 17 c i).
    Filler(Content),
}

struct Elem {
    content: Content,
    labels: Labels,
    /// Nodes: the local node type alias, if one is specified (18.2 SR 4, Cor 1).
    alias: Option<String>,
    directed: bool,
    source: Option<Endpoint>,
    destination: Option<Endpoint>,
}

fn endpoint(edge: &Plain, reference: &str, alias: &str) -> Option<Endpoint> {
    let holder = first(edge, reference);
    let found = holder.map_or_else(|| first(edge, alias), |r| first(r, alias));
    if let Some(a) = found {
        return Some(Endpoint::Alias(ident(a)));
    }
    let r = holder?;
    Some(Endpoint::Filler(match first(r, "node type filler") {
        Some(f) => Content::of(f, Kind::Node),
        None => Content {
            key: None,
            key_without_phrase: false,
            implied: Labels::new(),
            props: Props::new(),
        },
    }))
}

fn elem(node: &Plain, kind: Kind) -> Elem {
    let content = Content::of(node, kind);
    let labels = content.label_set();
    let alias = match kind {
        Kind::Node => first(node, "local node type alias")
            .or_else(|| first(node, "node type name"))
            .map(ident),
        Kind::Edge => None,
    };
    let (directed, source, destination) = match kind {
        Kind::Node => (false, None, None),
        Kind::Edge => {
            let mut d = Vec::new();
            below(
                node,
                &["edge type pattern directed", "endpoint pair directed"],
                &mut d,
            );
            (
                !d.is_empty(),
                endpoint(node, "source node type reference", "source node type alias"),
                endpoint(
                    node,
                    "destination node type reference",
                    "destination node type alias",
                ),
            )
        }
    };
    Elem {
        content,
        labels,
        alias,
        directed,
        source,
        destination,
    }
}

/// Effective key label sets (18.2 SR 9, 18.3 SR 10), with or without GG22's inference.
fn effective(elems: &[Elem], gg22: bool) -> Vec<Option<Labels>> {
    (0..elems.len())
        .map(|i| match &elems[i].content.key {
            Some(k) => Some(k.clone()),
            None if !gg22 => None,
            None => {
                let others: Labels = (0..elems.len())
                    .filter(|&j| j != i)
                    .flat_map(|j| elems[j].labels.iter().cloned())
                    .collect();
                let uls: Labels = elems[i]
                    .content
                    .implied
                    .difference(&others)
                    .cloned()
                    .collect();
                (!uls.is_empty()).then_some(uls)
            }
        })
        .collect()
}

/// 18.1 SR 6: SUB implies SUPER.
fn implies(sub: usize, sup: usize, elems: &[Elem], eff: &[Option<Labels>]) -> bool {
    let Some(sup_key) = &eff[sup] else {
        return false;
    };
    sup_key.is_subset(&elems[sub].labels) && eff[sub].as_ref() != Some(sup_key)
}

/// 18.1 SR 7: why SUB is not structurally consistent with SUPER, if it is not (reading on the
/// value types).
fn inconsistent(sub: (&Labels, &Props), sup: (&Labels, &Props)) -> Option<String> {
    if !sup.0.is_subset(sub.0) {
        return Some("its label set does not include the other's".into());
    }
    for (pn, vt) in sup.1 {
        match sub.1.get(pn) {
            None => return Some(format!("it has no property {pn:?}")),
            Some(t) if t != vt => {
                return Some(format!(
                    "property {pn:?} has a value type not identical to the other's (reading)"
                ));
            }
            Some(_) => {}
        }
    }
    None
}

/// The same node type: the same label set and the same property type set (reading on the value
/// types).
fn same_type(a: (&Labels, &Props), b: (&Labels, &Props)) -> bool {
    a.0 == b.0 && a.1 == b.1
}

fn show(l: &Labels) -> String {
    format!("{{{}}}", l.iter().cloned().collect::<Vec<_>>().join(", "))
}

/// The rules over one <graph type specification body>.
fn body(gtsb: &Plain, path: &[&str], out: &mut Vec<Violation>) {
    let mut specs = Vec::new();
    below(
        gtsb,
        &["node type specification", "edge type specification"],
        &mut specs,
    );
    let nodes: Vec<Elem> = specs
        .iter()
        .filter(|s| def_name(s) == Some("node type specification"))
        .map(|s| elem(s, Kind::Node))
        .collect();
    let edges: Vec<Elem> = specs
        .iter()
        .filter(|s| def_name(s) == Some("edge type specification"))
        .map(|s| elem(s, Kind::Edge))
        .collect();

    // Rules that do not depend on GG22.
    let mut plain = Vec::new();
    // 18.1 SR 10.
    for i in 0..nodes.len() {
        if let Some(a) = &nodes[i].alias
            && nodes[..i].iter().any(|n| n.alias.as_ref() == Some(a))
        {
            plain.push((
                "18.1 SR 10",
                format!("two node types with the local alias {a:?}"),
            ));
        }
    }
    // 18.1 SR 11, 18.3 SR 17, 18: resolve endpoints to node type specifications.
    let mut ends: Vec<[Option<usize>; 2]> = Vec::new();
    for e in &edges {
        let mut pair = [None, None];
        for (slot, (end, which, rule)) in [
            (&e.source, "source", "18.3 SR 17"),
            (&e.destination, "destination", "18.3 SR 18"),
        ]
        .into_iter()
        .enumerate()
        {
            let Some(end) = end else {
                plain.push((
                    "18.1 SR 11",
                    format!("an edge type with no {which} node type"),
                ));
                continue;
            };
            match end {
                Endpoint::Alias(a) => {
                    match nodes.iter().position(|n| n.alias.as_ref() == Some(a)) {
                        Some(i) => pair[slot] = Some(i),
                        None => plain.push((
                            rule,
                            format!(
                                "a ii: no node type with the local alias {a:?} for the {which}"
                            ),
                        )),
                    }
                }
                Endpoint::Filler(f) if f.key.is_some() => {
                    if f.key_without_phrase {
                        plain.push((
                            rule,
                            format!(
                                "b ii: a {which} node type key label set with no label set phrase names no key label set (reading)"
                            ),
                        ));
                        continue;
                    }
                    let key = f.key.as_ref().unwrap();
                    match nodes
                        .iter()
                        .position(|n| n.content.key.as_ref() == Some(key))
                    {
                        None => plain.push((
                            rule,
                            format!(
                                "b ii: no node type with the key label set {} for the {which}",
                                show(key)
                            ),
                        )),
                        Some(i) => {
                            if same_type(
                                (&nodes[i].labels, &nodes[i].content.props),
                                (&f.label_set(), &f.props),
                            ) {
                                pair[slot] = Some(i);
                            } else {
                                plain.push((
                                    rule,
                                    format!(
                                        "b v: the {which} filler's node type and the node type keyed {} are not shown to have the same normal form (reading)",
                                        show(key)
                                    ),
                                ));
                            }
                        }
                    }
                }
                Endpoint::Filler(f) => {
                    let want = (&f.label_set(), &f.props);
                    match nodes
                        .iter()
                        .position(|n| same_type((&n.labels, &n.content.props), want))
                    {
                        Some(i) => pair[slot] = Some(i),
                        None => {
                            // Only a value type comparison makes this a reading.
                            let reading = if nodes.iter().any(|n| &n.labels == want.0) {
                                " (reading on value types)"
                            } else {
                                ""
                            };
                            plain.push((
                                "18.1 SR 11",
                                format!(
                                    "no node type specification of the body specifies the {which} node type, labels {}{reading}",
                                    show(want.0)
                                ),
                            ))
                        }
                    }
                }
            }
        }
        ends.push(pair);
    }

    // Rules over effective key label sets, under each reading of GG22.
    let under = |gg22: bool| -> Vec<(&'static str, String)> {
        let mut v = Vec::new();
        let neff = effective(&nodes, gg22);
        let eeff = effective(&edges, gg22);
        // 18.1 SR 8.
        for i in 0..nodes.len() {
            if let Some(k) = &neff[i]
                && neff[..i].iter().any(|o| o.as_ref() == Some(k))
            {
                v.push((
                    "18.1 SR 8",
                    format!(
                        "two node types with the effective key label set {}",
                        show(k)
                    ),
                ));
            }
        }
        // 18.1 SR 9.
        for n in 0..nodes.len() {
            for o in 0..nodes.len() {
                if o != n
                    && implies(o, n, &nodes, &neff)
                    && let Some(why) = inconsistent(
                        (&nodes[o].labels, &nodes[o].content.props),
                        (&nodes[n].labels, &nodes[n].content.props),
                    )
                {
                    v.push((
                        "18.1 SR 9",
                        format!(
                            "a node type implying the one keyed {} is not structurally consistent with it: {why}",
                            show(neff[n].as_ref().unwrap())
                        ),
                    ));
                }
            }
        }
        // 18.1 SR 14.
        for i in 0..edges.len() {
            let Some(k) = &eeff[i] else { continue };
            for j in 0..i {
                if eeff[j].as_ref() != Some(k) {
                    continue;
                }
                let why = if edges[i].directed != edges[j].directed {
                    Some("one is directed, the other undirected".to_string())
                } else if edges[i].labels != edges[j].labels {
                    Some("their label sets differ".into())
                } else if edges[i].content.props != edges[j].content.props {
                    Some("their property type sets are not shown to be the same (reading)".into())
                } else {
                    None
                };
                if let Some(why) = why {
                    v.push((
                        "18.1 SR 14",
                        format!(
                            "two edge types with the effective key label set {}: {why}",
                            show(k)
                        ),
                    ));
                }
            }
        }
        // 18.1 SR 16.
        let node_of = |i: usize| (&nodes[i].labels, &nodes[i].content.props);
        for e in 0..edges.len() {
            for o in 0..edges.len() {
                if o == e || !implies(o, e, &edges, &eeff) {
                    continue;
                }
                let key = show(eeff[e].as_ref().unwrap());
                if let Some(why) = inconsistent(
                    (&edges[o].labels, &edges[o].content.props),
                    (&edges[e].labels, &edges[e].content.props),
                ) {
                    v.push((
                        "18.1 SR 16",
                        format!("a: an edge type implying the one keyed {key} is not structurally consistent with it: {why}"),
                    ));
                }
                // Unresolved endpoints are reported above.
                let ([Some(os), Some(od)], [Some(es), Some(ed)]) = (ends[o], ends[e]) else {
                    continue;
                };
                let fits = |a: usize, b: usize| inconsistent(node_of(a), node_of(b)).is_none();
                let consistent = match (edges[o].directed, edges[e].directed) {
                    (true, true) => fits(os, es) && fits(od, ed),
                    (false, false) => {
                        (fits(os, es) && fits(od, ed)) || (fits(os, ed) && fits(od, es))
                    }
                    _ => false,
                };
                if !consistent {
                    v.push((
                        "18.1 SR 16",
                        format!(
                            "b: an edge type implying the one keyed {key} is not structurally endpoint-consistent with it (reading on value types)"
                        ),
                    ));
                }
            }
        }
        v.dedup();
        v
    };
    let with = under(true);
    let without = under(false);
    let mut found: Vec<(&'static str, String)> = plain;
    for x in &with {
        if without.contains(x) {
            found.push(x.clone());
        } else {
            found.push((
                x.0,
                format!("{} (with GG22's key label set inference)", x.1),
            ));
        }
    }
    for x in &without {
        if !with.contains(x) {
            found.push((
                x.0,
                format!("{} (without GG22's key label set inference)", x.1),
            ));
        }
    }
    let mut seen = BTreeSet::new();
    for (rule, detail) in found {
        if seen.insert((rule, detail.clone())) {
            out.push(violation(path, rule, detail));
        }
    }
}
