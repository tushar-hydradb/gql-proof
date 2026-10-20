"""Extracts the conformance rules of ISO/IEC 39075 into a machine readable map.

5.3.7: a standard-defined feature is defined by its Conformance Rules, and "an implicit
Conformance Rule is any normative statement that begins 'Without Feature nnn,'". So the
statements to collect are every sentence that begins that way, wherever it is. Their
containment vocabulary is defined in 5.3.2.1, and `conformance.lark` parses each one into a
tree pattern over the BNF's names.

The rules are those of the 2024 text as Cor 1:2026 corrects them: `corrigendum.py` reads Cor 1
into `corrigendum.json` first, and its rule, table 10 and 24.2 edits are applied here after the
2024 text has been checked against itself.

The PDF stays local and so does the output: nothing here is committed.

    .venv-pdf/bin/python -I tools/conformance.py <iso pdf> <grammar dir> <out json>
"""

import argparse
import collections
import hashlib
import json
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pdfplumber
import pypdfium2 as pdfium
from lark import Lark, Token, Transformer, Tree, v_args
from lark.visitors import CollapseAmbiguities

# Page geometry, in points from the bottom: running heads and the licence banner sit above
# 760, the copyright line and page number below 55.
BODY = (55, 760)
# With loose character boxes, letters of one word touch or overlap; words are about 1.6 apart.
WORD_GAP = 0.8
# Chars whose middles are this close sit on one line.
LINE_TOLERANCE = 3
# A raised run whose font is below this fraction of its line's is a superscript.
SUPERSCRIPT = 0.9
SECTIONS = {"Function", "Format", "Syntax Rules", "General Rules", "Conformance Rules"}
SOFT_HYPHEN = "￾"


def squash(text):
    return re.sub(r"\s+", "", text)


def same_text(text):
    """For comparing two printings of one rule: no whitespace, no case, and no hyphens, since
    a hyphen at a line end may or may not be a soft one ("non-terminal", "nonterminal")."""
    return re.sub(r"[\s\-‐]+", "", text).lower()


def page_chars(page, band=BODY):
    """(char, left, right, middle y, font size) for every char drawn inside the band."""
    tp = page.get_textpage()
    out = []
    for i in range(tp.count_chars()):
        ch = tp.get_text_range(i, 1)
        # Spaces are zero-size boxes below the baseline; word breaks are found from gaps.
        if ch in "\r\n ":
            continue
        left, bottom, right, top = tp.get_charbox(i, loose=True)
        y = (bottom + top) / 2
        if band[0] < y < band[1]:
            out.append((ch, left, right, y, pdfium.raw.FPDFText_GetFontSize(tp.raw, i)))
    return out


def body_lines(page):
    """The page's body text as lines, top to bottom and left to right, with the spaces the PDF
    only implies put back. Ordered by position, not by the content stream, which puts a rule's
    enumerator wherever it was drawn. A raised row in a smaller font is a superscript and joins
    the line below it, written `^`: 2^7."""
    return [text for text, _ in positioned_lines(page)]


def positioned_words(page):
    """(word, left, middle y) for every word in the body, split where body_lines puts spaces."""
    out = []
    for text, chars in positioned_lines(page):
        i = 0
        for word in text.split(" "):
            letters = [c for c in word if c != "^"]
            if letters:
                first = chars[i]
                out.append((word, first[1], first[3]))
            i += len(letters)
    return out


def positioned_lines(page):
    """body_lines, each with its chars in order."""
    rows = []
    for c in sorted(page_chars(page), key=lambda c: -c[3]):
        if rows and abs(rows[-1][0] - c[3]) < LINE_TOLERANCE:
            rows[-1][1].append(c)
        else:
            rows.append((c[3], [c]))
    def size(chars):
        return max(c[4] for c in chars)

    merged = []
    for y, chars in rows:
        above = merged[-1] if merged else None
        if above and above[0] - y < size(chars) and size(above[1]) < SUPERSCRIPT * size(chars):
            chars = merged.pop()[1] + chars
        merged.append((y, chars))
    lines = []
    for _, chars in merged:
        chars = sorted(chars, key=lambda c: c[1])
        # Justification sometimes spreads letters too, so a word gap is measured against this
        # line's typical letter gap.
        gaps = sorted(b[1] - a[2] for a, b in zip(chars, chars[1:]) if " " not in (a[0], b[0]))
        word_gap = max(WORD_GAP, (gaps[len(gaps) // 2] if gaps else 0) + WORD_GAP)
        line, last, small, base = [], None, False, size(chars)
        for ch, left, right, _, fs in chars:
            if last is not None and left - last > word_gap and line and line[-1] != " " and ch != " ":
                line.append(" ")
            raised = fs < SUPERSCRIPT * base and ch != " "
            if raised and not small and line:
                line.append("^")
            small = raised
            line.append(ch)
            last = right
        text = "".join(line).strip()
        if text:
            lines.append((text, chars))
    return lines


def join(lines):
    """Lines into running text: a soft hyphen at a line end joins without a space."""
    out = ""
    for l in lines:
        if out.endswith(SOFT_HYPHEN):
            out = out[:-1] + l
        else:
            out = f"{out} {l}" if out else l
    return out.replace(SOFT_HYPHEN, "")


def bookmarks(pdf):
    """Subclause titles by page, from the PDF outline: (page, number, title)."""
    out = []
    for b in pdf.get_toc(max_depth=10):
        dest = b.get_dest()
        title = b.get_title()
        m = re.match(r"^((?:\d+(?:\.\d+)*)|[A-E]) (.*)$", title)
        if dest is not None and m:
            out.append((dest.get_index(), m.group(1), m.group(2)))
    return out


class Block:
    """Running text under one subclause and section heading."""

    def __init__(self, page, subclause, title, section):
        self.page, self.subclause, self.title, self.section = page, subclause, title, section
        self.lines = []


def blocks(pdf, marks):
    by_page = collections.defaultdict(list)
    for page, number, title in marks:
        by_page[page].append((number, title))
    out = []
    cur = Block(0, None, None, None)
    for p in range(len(pdf)):
        pending = list(by_page.get(p, []))
        for line in body_lines(pdf[p]):
            flat = squash(line)
            hit = next((h for h in pending if squash(f"{h[0]} {h[1]}") == flat), None)
            if hit is None and pending and p >= 0:
                # annex headings read "Annex A (informative) <title>" on the page itself
                hit = next((h for h in pending if h[0].isalpha() and flat.startswith(f"Annex{h[0]}")), None)
            if hit is not None:
                pending.remove(hit)
                out.append(cur)
                cur = Block(p, hit[0], hit[1], None)
                continue
            if line in SECTIONS:
                out.append(cur)
                cur = Block(p, cur.subclause, cur.title, line)
                continue
            cur.lines.append(line)
    out.append(cur)
    return [b for b in out if b.lines]


# A statement ends at a full stop before the next enumerator, note, sentence or the end, or at
# the next enumerator when its full stop is missing (GQ22's is).
# Cor 1 numbers the rules it inserts 1.1), 40.1).
ENUMERATOR = r"\s+\(?[0-9a-z]+(?:\.[0-9]+)?\)\s"
STATEMENT = re.compile(
    r"(?:(?P<rule>\(?[0-9a-z]+(?:\.[0-9]+)?\))\s+)?"
    r"(?P<text>Without ?Feature ?(?P<code>[A-Z][A-Z0-9]{3}) ?, ?“(?P<name>[^”]*)” ?,?(?P<body>.*?))"
    rf"(?:\.(?=(?:{ENUMERATOR}|\s+NOTE\s|\s+Without ?Feature|\s+[A-Z][a-z]*\s)|\s*$)|(?={ENUMERATOR})|\s*$)"
)
# Where annex A turns from the implicit rules to recapitulating the Conformance Rules sections.
RECAP = "The remainder of this Annex recapitulates"
DEVICE = re.compile(
    r"(?:(?P<rule>\(?[0-9a-z]+\))\s+)?(?P<text>Conforming GQL language shall not (?:contain|specify)(?P<body>.*?\.))"
    r"(?=\s+(?:\(?[0-9a-z]+\)\s|NOTE\s)|\s*$)"
)


def sha(text):
    return hashlib.sha256(squash(text).encode()).hexdigest()


def statements(text, block):
    for m in STATEMENT.finditer(text):
        yield {
            "feature": m.group("code"),
            "name": m.group("name"),
            "subclause": block.subclause,
            "title": block.title,
            "section": block.section,
            "rule": m.group("rule"),
            "text": m.group("text"),
            "body": m.group("body").strip(),
        }


def collect(bs, marks):
    """Every "Without Feature" statement: in the body, in annex A's summary of the implicit
    rules, and in annex A's recapitulation; and the specification devices."""
    annex = {n: p for p, n, _ in marks if n.isalpha()}
    out = {"body": [], "implicit": [], "recap": [], "devices": []}
    recap = False
    for b in bs:
        text = join(b.lines)
        if b.page < annex["A"]:
            out["body"].extend(statements(text, b))
            if b.section == "Conformance Rules":
                for m in DEVICE.finditer(text):
                    out["devices"].append(
                        {
                            "subclause": b.subclause,
                            "title": b.title,
                            "rule": m.group("rule"),
                            "text": m.group("text"),
                            "body": m.group("body").strip(),
                        }
                    )
        elif b.page < annex["B"]:
            head, sep, tail = (text, "", "") if recap else text.partition(RECAP)
            if not recap:
                out["implicit"].extend(statements(head, b))
            recap = recap or bool(sep)
            out["recap"].extend(statements(tail if sep else head if recap else "", b))
    return out


def subclause(bs, number):
    return join([l for b in bs if b.subclause == number for l in b.lines])


CODE = r"[A-Z][A-Z0-9]{3}"


def table_rows(path, pages):
    """Table 10's rows on these pages, read from the ruled cells with pdfplumber: the feature,
    its name, and what it implies. A row whose third cell is "At least one of:" collects the
    codes of the rows under it, whose first cells are empty, across a page break too."""
    out = []
    with pdfplumber.open(path) as pdf:
        for p in pages:
            page = pdf.pages[p]
            for table in page.find_tables():
                for row in table.extract():
                    cells = [c or "" for c in row]
                    if len(cells) != 4 or not (re.fullmatch(CODE, cells[0]) or (not cells[0] and out)):
                        continue
                    if cells[0]:
                        either = squash(cells[2]).lower() == "atleastoneof:"
                        out.append(
                            {
                                "page": p,
                                "top": table.bbox[1],
                                "feature": cells[0],
                                "name": cells[1],
                                "implied": [] if either else [cells[2]],
                                "names": [] if either else [cells[3]],
                                "either": either,
                            }
                        )
                    else:
                        out[-1]["implied"].append(cells[2])
                        out[-1]["names"].append(cells[3])
    for r in out:
        for c in [r["feature"], *r["implied"]]:
            if not re.fullmatch(CODE, c):
                raise SystemExit(f"table 10 row {r['feature']}: “{c}” is not a feature code")
        if r["either"] and len(r["implied"]) < 2:
            raise SystemExit(f"table 10 row {r['feature']}: “at least one of” with {len(r['implied'])} codes")
    return out


def row_key(r):
    return (r["feature"], r["either"], tuple(r["implied"]))


def check_row_names(rows, features, failures, where):
    for r in rows:
        for code, name in [(r["feature"], r["name"]), *zip(r["implied"], r["names"])]:
            if code not in features:
                failures.append(f"{where}: {code} is not a feature")
            elif same_text(name) != same_text(features[code]):
                failures.append(f"{where}: {code} named “{name}”, the features say “{features[code]}”")


def table10(path, marks, cor, features, cor_features, failures, notes):
    """24.7 table 10 as cor 1 leaves it. A row with one implied feature is an implication,
    which a claim is closed under; an "at least one of" row is a claim rule, checked like
    24.3's."""
    start = next(p for p, n, _ in marks if n == "24.7")
    end = next(p for p, n, _ in marks if n == "A")
    rows = table_rows(path, range(start, end))
    check_row_names(rows, features, failures, "table 10")
    for it in cor:
        if it["kind"] == "table rows delete":
            for r in it["rows"]:
                hit = [x for x in rows if row_key(x) == row_key(r)]
                if len(hit) != 1:
                    failures.append(f"cor 1 deletes table 10 row {r['feature']} -> {r['implied']}, which 2024 has {len(hit)} times")
                for x in hit:
                    rows.remove(x)
        elif it["kind"] == "table rows add":
            check_row_names(it["rows"], cor_features, failures, "cor 1 table 10")
            for r in it["rows"]:
                if any(row_key(x) == row_key(r) for x in rows):
                    notes.append(f"cor 1 adds table 10 row {r['feature']} -> {r['implied']}, which is there already")
                else:
                    rows.append(r)
    implies = [[r["feature"], b] for r in rows if not r["either"] for b in r["implied"]]
    either = [
        {"if_any": [r["feature"]], "one_of": [[b] for b in r["implied"]], "source": "table 10"}
        for r in rows
        if r["either"]
    ]
    graph = collections.defaultdict(set)
    for a, b in implies:
        graph[a].add(b)

    def cyclic(n, path):
        return n in path or any(cyclic(m, path | {n}) for m in graph[n])

    for a in list(graph):
        if cyclic(a, frozenset()):
            failures.append(f"table 10: {a} implies itself")
    return implies, either


def claims(bs, item1, features, failures):
    """The rules a claim must satisfy, as "if any of these is claimed, at least one of these
    sets is claimed in full". 24.2 for minimum conformance (no condition), with its list item
    1) as cor 1 replaces it, and 24.3 for the rest."""
    out = []
    minimum = subclause(bs, "24.2")
    if item1 is not None:
        minimum, n = re.subn(r"1\) A claim of conformance to at least one of:.*?(?= 2\) )", lambda _: item1, minimum, count=1)
        if n != 1:
            failures.append("24.2: cor 1 replaces list item 1), which does not read as expected")
    m = re.search(r"1\) A claim of conformance to at least one of:(.*?) 2\) ", minimum)
    if not m:
        failures.append("24.2: the minimum conformance claim does not read as expected")
    else:
        # a), b), ... are the options; an option may carry its own "at least one of: i) ii)"
        options, letter = [], "a"
        for part in re.split(r"\s([a-z])\)\s", " " + m.group(1))[1:]:
            if part == letter:
                options.append("")
                letter = chr(ord(letter) + 1)
            elif options:
                options[-1] += part if len(part) > 1 else f" {part}) "
        one_of = []
        for o in options:
            codes = re.findall(rf"Feature ({CODE})", o)
            one_of += [[codes[0]]] if len(codes) == 1 else [[codes[0], c] for c in codes[1:]]
        out.append({"if_any": None, "one_of": one_of, "source": "24.2"})
    for m in re.finditer(
        r"claims conformance to (.*?), shall also claim conformance to at least one of:(.*?)(?=A GQL-implementation|$)",
        subclause(bs, "24.3"),
    ):
        if_any = re.findall(rf"Feature ({CODE})", m.group(1))
        one_of = [[c] for c in re.findall(rf"Feature ({CODE})", m.group(2))]
        out.append({"if_any": if_any, "one_of": one_of, "source": "24.3"})
    for r in out:
        for c in (r["if_any"] or []) + [c for s in r["one_of"] for c in s]:
            if c not in features:
                failures.append(f"claim rule names {c}, which is not a feature")
    return out


def corrected(rules, implicit, cor, titles, failures, notes):
    """The conformance rules and implicit statements with cor 1's edits applied: its rules
    replace, delete and add whole Conformance Rules by number, and any "Without Feature"
    statement in the text it puts elsewhere (GC00's, in 4.2.5.3) joins the implicit ones."""
    rules, implicit = list(rules), list(implicit)

    def new(it, section):
        block = Block(it["page"], it["subclause"], titles.get(it["subclause"]), section)
        return [{**s, "source": "Cor 1"} for s in statements(it["text"], block)]

    for it in cor:
        if it["applied"] is None and it.get("text"):
            if any(s["subclause"] == it["subclause"] for s in implicit):
                failures.append(f"cor 1 rewrites text in {it['subclause']}, which holds 2024 statements outside its Conformance Rules")
            implicit += new(it, None)
        if not it["kind"].startswith("conformance rule"):
            continue
        here = [s for s in rules if s["subclause"] == it["subclause"]]
        if it["kind"] in ("conformance rule delete", "conformance rule replace"):
            for n in it["rules"]:
                gone = [s for s in here if s["rule"] == f"{n})"]
                if not gone:
                    failures.append(f"cor 1 {it['kind'].split()[-1]}s {it['subclause']} Conformance Rule {n}), which 2024 does not have")
                rules = [s for s in rules if not any(s is g for g in gone)]
        if it["kind"] == "conformance rule delete":
            continue
        added = new(it, "Conformance Rules")
        if it["kind"] == "conformance rule replace" and sorted(s["rule"] for s in added) != sorted(f"{n})" for n in it["rules"]):
            failures.append(f"cor 1 replaces {it['subclause']} rules {it['rules']} with {[s['rule'] for s in added]}")
        if not added:
            failures.append(f"cor 1 {it['subclause']} item {it['item']}: no rule in “{it['text'][:60]}”")
        for s in added:
            if it["kind"] == "conformance rule add" and any(x["rule"] == s["rule"] for x in here):
                notes.append(f"cor 1 adds {it['subclause']} Conformance Rule {s['rule']} ({s['feature']}), a number 2024 already uses")
        rules += added
    return rules, implicit


class Bnf:
    """What the sentence parser checks its readings against: which definitions can contain
    which, and which can be another (5.3.2.1: <A> is <B> if there is a rule <A> ::= <B>)."""

    def __init__(self, path):
        root = ET.parse(path).getroot()
        self.defs = {}
        for d in root.iter("BNFdef"):
            rhs = d.find("rhs")
            alts = rhs.findall("alt") or [rhs]
            # <A> ::= <B> [ ... ] is <A> ::= <B> with the optional parts left out
            units = set()
            for a in alts:
                required = [e for e in a if e.tag != "opt"]
                if len(required) == 1 and required[0].tag == "BNF":
                    units.add(required[0].get("name"))
            self.defs[d.get("name")] = (
                {b.get("name") for b in d.iter("BNF")},
                {k.text for k in d.iter("kw")},
                units,
            )
        self.reach = {n: self._closure(n, lambda m: self.defs[m][0]) for n in self.defs}
        self.chain = {n: self._closure(n, lambda m: self.defs[m][2]) for n in self.defs}

    def _closure(self, start, step):
        seen, todo = set(), [start]
        while todo:
            for m in step(todo.pop()):
                if m in self.defs and m not in seen:
                    seen.add(m)
                    todo.append(m)
        return seen

    def keywords(self, n):
        """Keywords anywhere under <n>."""
        return set().union(*(self.defs[m][1] for m in self.reach[n] | {n}))


GRAMMAR = Lark(
    (Path(__file__).parent / "conformance.lark").read_text(),
    parser="earley",
    ambiguity="explicit",
)


def nt(token):
    return str(token)[1:-1]


@v_args(inline=True)
class ToPattern(Transformer):
    """Parse trees into patterns: a node is {nt, words, conds}, and a statement forbids any of
    its nodes."""

    def __init__(self, subject):
        super().__init__()
        self.subject = subject

    def words(self, *kws):
        return {"nt": None, "words": [str(k) for k in kws], "conds": []}

    def quoted(self, *qs):
        return [{"nt": None, "words": [str(q)[1:-1]], "conds": []} for q in qs]

    def item(self, *parts):
        return parts[-1]

    def items(self, *xs):
        out = []
        for x in xs:
            out.extend(x if isinstance(x, list) else [x])
        return out

    def node(self, *parts):
        n = {"nt": None, "words": None, "conds": []}
        for p in parts:
            if isinstance(p, Token) and p.type == "NT":
                n["nt"] = nt(p)
            elif isinstance(p, dict) and "words" in p and p["nt"] is None and n["words"] is None and not n["conds"]:
                n["words"] = p["words"]
            elif isinstance(p, dict) and "cond" in p:
                n["conds"].append(p["cond"])
        return n

    def _how(self, parts):
        return next((str(p) for p in parts if isinstance(p, Token) and p.type == "HOW"), "any")

    def is_(self, items):
        return {"cond": {"is": {"negated": False, "any": items}}}

    def is_not(self, items):
        return {"cond": {"is": {"negated": True, "any": items}}}

    def followed_by(self, *parts):
        names = [nt(p) for p in parts if isinstance(p, Token) and p.type == "NT"]
        seqs = [[names[i], names[i + 1]] for i in range(0, len(names), 2)]
        return {"cond": {"followed_by": seqs}}

    def contains(self, *parts):
        items = parts[-1]
        return {"cond": {"contains": {"how": self._how(parts), "negated": False, "exactly_one": False, "any": items}}}

    def not_contains(self, *parts):
        items = parts[-1]
        return {"cond": {"contains": {"how": self._how(parts), "negated": True, "exactly_one": False, "any": items}}}

    def exactly_one(self, name):
        inner = {"nt": nt(name), "words": None, "conds": []}
        return {"cond": {"contains": {"how": "simply", "negated": False, "exactly_one": True, "any": [inner]}}}

    def not_in(self, _art, name):
        return {"cond": {"parent": {"negated": True, "how": "immediately", "nt": nt(name)}}}

    def forbid(self, *parts):
        head = next((p for p in parts if isinstance(p, dict)), None)
        items = parts[-1]
        if head is None:
            return {"kind": "pattern", "forbid": items}
        how = self._how(parts)
        head["conds"].append({"contains": {"how": how, "negated": False, "exactly_one": False, "any": items}})
        return {"kind": "pattern", "forbid": [head]}

    def require(self, *parts):
        head = next(p for p in parts if isinstance(p, dict))
        head["conds"].append({"contains": {"how": self._how(parts), "negated": True, "exactly_one": False, "any": parts[-1]}})
        return {"kind": "pattern", "forbid": [head]}

    def require_subject(self, items):
        head = {"nt": self.subject, "words": None, "conds": []}
        head["conds"].append({"contains": {"how": "any", "negated": True, "exactly_one": False, "any": items}})
        return {"kind": "pattern", "forbid": [head]}

    def contained_be(self, inner, _art, outer, items):
        v = {"nt": nt(inner), "words": None, "conds": [{"is": {"negated": True, "any": items}}]}
        s = {"nt": nt(outer), "words": None, "conds": [{"contains": {"how": "immediately", "negated": False, "exactly_one": False, "any": [v]}}]}
        return {"kind": "pattern", "forbid": [s]}

    def contained_not(self, *parts):
        names = [nt(p) for p in parts if isinstance(p, Token) and p.type == "NT"]
        v = {"nt": names[0], "words": None, "conds": [{"contains": {"how": self._how(parts), "negated": False, "exactly_one": False, "any": parts[-1]}}]}
        s = {"nt": names[1], "words": None, "conds": [{"contains": {"how": "immediately", "negated": False, "exactly_one": False, "any": [v]}}]}
        return {"kind": "pattern", "forbid": [s]}

    def typed(self, *_):
        return {"kind": "typed", "owner": "context provider"}

    def context(self, *_):
        return {"kind": "context", "owner": "context provider"}

    def structural(self, *_):
        return {"kind": "structural", "owner": "generator, not compiled yet"}

    def ntlist(self, *names):
        return [nt(n) for n in names]

    def juxtaposed(self, inner, _plural, _art, outer, unless):
        cond = {"juxtaposed": {"first": nt(inner), "then": nt(inner), "unless": unless}}
        return {
            "kind": "pattern",
            "forbid": [{"nt": nt(outer), "words": None, "conds": [cond]}],
            # 16.4 SR 2's depth of graph pattern matching, as for SR 6 and 14: otherwise a
            # node pattern in a subquery in a WHERE would count as one of "any two"
            "readings": ["at the same depth of graph pattern matching"],
        }

    def unflanked(self, _art, inner, _art2, by):
        return {
            "kind": "pattern",
            "forbid": [{"nt": nt(inner), "words": None, "conds": [{"unflanked": {"by": nt(by)}}]}],
        }

    def lexical(self, *_):
        return {"kind": "lexical", "owner": "leaf provider"}

    def semantic(self, *_):
        return {"kind": "semantic", "owner": "oracle"}


def nodes(pattern):
    """Every node in a pattern, with the relation its parent puts it in."""
    todo = [(n, None, None) for n in pattern.get("forbid", [])]
    while todo:
        n, parent, rel = todo.pop()
        yield n, parent, rel
        for c in n["conds"]:
            for rel, body in c.items():
                if rel in ("contains", "is"):
                    todo.extend((m, n, rel) for m in body["any"])


def sensible(pattern, bnf):
    """Whether each relation in the reading is one the grammar allows: a definition can only
    contain what it reaches, and only be what its unit rules chain to."""
    for n, parent, rel in nodes(pattern):
        if n["nt"] is not None and n["nt"] not in bnf.defs:
            return False
        if parent is None or parent["nt"] is None:
            continue
        p = parent["nt"]
        if n["nt"] is not None:
            if rel == "contains" and n["nt"] not in bnf.reach[p]:
                return False
            if rel == "is" and n["nt"] not in bnf.chain[p]:
                return False
        elif not set(n["words"]) <= bnf.keywords(p) and not all(len(w) == 1 for w in n["words"]):
            return False
    return True


def nesting(tree, depth=0):
    """How deep the reading attaches its lists: summed over every list, its length times its
    depth. The innermost attachment wins a tie."""
    if not isinstance(tree, Tree):
        return 0
    own = len(tree.children) * depth if tree.data == "items" else 0
    return own + sum(nesting(c, depth + (tree.data == "items")) for c in tree.children)


def parse(sentence, subject, bnf):
    """The reading of one sentence: every parse, minus those the grammar rules out, the most
    deeply nested first."""
    tree = GRAMMAR.parse(sentence)
    readings = []
    for t in CollapseAmbiguities().transform(tree):
        p = ToPattern(subject).transform(t)
        if p["kind"] != "pattern" or sensible(p, bnf):
            readings.append((nesting(t), json.dumps(p, sort_keys=True), p))
    if not readings:
        raise ValueError(f"no reading the grammar allows: {sentence}")
    readings.sort(key=lambda r: (-r[0], r[1]))
    best = readings[0]
    ties = {r[1] for r in readings if r[0] == best[0]}
    if len(ties) > 1:
        raise ValueError(f"{len(ties)} equally nested readings: {sentence}")
    return best[2]


# Longest chain of immediate containments a reading may go through.
CHAIN = 4


def chains(bnf, outer, inner):
    """Paths <outer> -> ... -> <inner> of immediate containments in which every step but at
    most one is a single-item rule (5.3.2.1's "is", optional parts left out)."""
    out = []

    def walk(path, wide):
        here = path[-1]
        if len(path) > CHAIN:
            return
        for nxt in sorted(bnf.defs[here][0]):
            if nxt not in bnf.defs or nxt in path:
                continue
            unit = nxt in bnf.defs[here][2]
            if not unit and wide:
                continue
            if nxt == inner:
                out.append(path + [nxt])
            else:
                walk(path + [nxt], wide or not unit)

    walk([outer], False)
    return out


def read_through(node, bnf, readings, vacuous):
    """Rewrites every "X immediately contains Y" that matches nothing as written (Y is never
    on X's right hand side) into the one chain of immediate containments through
    single-item rules that leads from X to Y, recording it. With no such chain, or several,
    the rule stays as written and is recorded as vacuous."""
    for cond in node["conds"]:
        for rel, body in cond.items():
            if rel not in ("contains", "is"):
                continue
            for i, alt in enumerate(body["any"]):
                if alt["nt"] is not None:
                    read_through(alt, bnf, readings, vacuous)
                if rel != "contains" or body["how"] != "immediately" or alt["nt"] is None:
                    continue
                outer, inner = node["nt"], alt["nt"]
                if inner in bnf.defs[outer][0]:
                    continue
                found = chains(bnf, outer, inner)
                if len(found) != 1:
                    vacuous.append(f"<{outer}> immediately containing <{inner}>: {len(found)} chains")
                    continue
                path = found[0]
                nested = alt
                for mid in reversed(path[1:-1]):
                    nested = {
                        "nt": mid,
                        "words": None,
                        "conds": [{"contains": {"how": "immediately", "negated": False, "exactly_one": False, "any": [nested]}}],
                    }
                body["any"][i] = nested
                readings.append(" > ".join(f"<{p}>" for p in path))


def with_readings(reading, bnf):
    """A parsed rule with its vacuous immediate containments read through single-item rules."""
    if reading["kind"] != "pattern":
        return reading
    readings, vacuous = [], []
    for node in reading["forbid"]:
        if node["nt"] is not None:
            read_through(node, bnf, readings, vacuous)
    if readings:
        reading["readings"] = reading.get("readings", []) + readings
    if vacuous:
        reading["vacuous"] = vacuous
    return reading


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pdf")
    ap.add_argument("grammar")
    ap.add_argument("out")
    ap.add_argument("--dump", action="store_true", help="print every statement and stop")
    args = ap.parse_args()

    pdf = pdfium.PdfDocument(args.pdf)
    marks = bookmarks(pdf)
    bs = blocks(pdf, marks)
    found = collect(bs, marks)

    if args.dump:
        for kind in ("body", "implicit", "recap"):
            for st in found[kind]:
                print(kind, st["feature"], st["subclause"], st["section"], st["rule"], "|", st["body"])
        for d in found["devices"]:
            print("device", d["subclause"], d["rule"], "|", d["body"])
        print({k: len(v) for k, v in found.items()}, file=sys.stderr)
        return

    grammar = Path(args.grammar)
    # the rules are read against the grammar as cor 1 leaves it (`corrigendum.py`)
    bnf = Bnf(grammar / "ISO_IEC_39075(en)+Cor1.bnf.xml")
    cor = json.loads((grammar / "corrigendum.json").read_text())
    features = {
        f.findtext("code"): " ".join("".join(f.find("description").itertext()).split())
        for f in ET.parse(grammar / "ISO_IEC_39075(en)-features.xml").getroot()
    }
    failures, notes = [], []

    # Every Conformance Rules statement is recapitulated in annex A, word for word.
    rules = [s for s in found["body"] if s["section"] == "Conformance Rules"]
    key = lambda s: (s["feature"], same_text(s["body"]))
    body, recap = collections.Counter(map(key, rules)), collections.Counter(map(key, found["recap"]))
    for f, _ in body - recap:
        failures.append(f"{f}: a conformance rule annex A does not recapitulate")
    for f, _ in recap - body:
        failures.append(f"{f}: annex A recapitulates a rule the body does not have")

    # Cor 1's names: a code features.xml lacks is new, a known code under another name is renamed
    cor_names = cor["features"]
    for c, n in cor_names.items():
        if c in features and same_text(n) != same_text(features[c]):
            notes.append(f"cor 1 renames {c} “{features[c]}” to “{n}”")
    corrected_features = {**features, **cor_names}
    titles = {n: t for _, n, t in marks}
    implicit = [s for s in found["body"] if s["section"] != "Conformance Rules"] + found["implicit"]
    rules, implicit = corrected(rules, implicit, cor["items"], titles, failures, notes)

    statements_out = []
    for origin, sts in (("conformance rule", rules), ("implicit", implicit)):
        for s in sts:
            source = s.get("source", "2024")
            names = cor_names if source == "Cor 1" else features
            if s["feature"] not in corrected_features:
                failures.append(f"{s['feature']}: not a feature")
            elif same_text(s["name"]) != same_text(names.get(s["feature"], corrected_features[s["feature"]])):
                failures.append(f"{s['feature']}: named “{s['name']}”, {source} says “{names[s['feature']]}”")
            subject = s["title"][1:-1] if s["title"] and s["title"].startswith("<") else None
            try:
                reading = with_readings(parse(s["body"], subject, bnf), bnf)
            except Exception as e:  # lark's errors and ours alike end the run below
                failures.append(f"{s['feature']} {s['subclause']} {s['rule']}: {e}")
                continue
            statements_out.append(
                {
                    "feature": s["feature"],
                    "subclause": s["subclause"],
                    "section": s["section"],
                    "rule": s["rule"],
                    "origin": origin,
                    "source": source,
                    **reading,
                    "sha256": sha(s["text"]),
                }
            )

    devices_out = []
    for d in found["devices"]:
        reading = with_readings(parse("conforming GQL language shall not contain" + d["body"], None, bnf), bnf)
        if reading["kind"] != "pattern":
            failures.append(f"{d['subclause']} {d['rule']}: an unconditional rule that is not a pattern")
        devices_out.append({"subclause": d["subclause"], "rule": d["rule"], **reading, "sha256": sha(d["text"])})

    covered = {s["feature"] for s in statements_out}
    # annex A's implicit summary also names features whose implicit rules begin "If ... supports"
    supports = set(re.findall(rf"Specifications for Feature ({CODE})", subclause(bs, "A")))
    for f in sorted(set(corrected_features) - covered - supports):
        failures.append(f"{f}: no statement defines it")
    for f in sorted(supports - covered):
        print(f"{f}: defined only by statements that do not begin “Without Feature”", file=sys.stderr)

    implies, either = table10(args.pdf, marks, cor["items"], features, corrected_features, failures, notes)
    item1 = [it for it in cor["items"] if it["kind"] == "list item replace" and it["subclause"] == "24.2"]
    if any(it["kind"] == "list item replace" and it["subclause"] != "24.2" for it in cor["items"]):
        failures.append("cor 1 replaces a list item outside 24.2")
    if len(item1) > 1 or (item1 and item1[0]["rules"] != ["1"]):
        failures.append("cor 1 replaces 24.2 list items other than 1)")
    claim_rules = claims(bs, item1[0]["text"] if item1 else None, corrected_features, failures) + either

    for n in dict.fromkeys(notes):
        print(n, file=sys.stderr)
    if failures:
        print("\n".join(failures), file=sys.stderr)
        sys.exit(1)

    out = {
        "edition": "ISO/IEC 39075:2024 + Cor 1:2026",
        "features": [
            {"code": c, "name": n, **({"cor1": "new" if c not in features else "renamed"} if c in cor_names and same_text(n) != same_text(features.get(c, "")) else {})}
            for c, n in corrected_features.items()
        ],
        "statements": statements_out,
        "devices": devices_out,
        "implies": implies,
        "claim_rules": claim_rules,
        "corrigendum": [
            {k: it[k] for k in ("subclause", "item", "kind", "instruction", "rationale", "applied")}
            for it in cor["items"]
        ],
        "notes": list(dict.fromkeys(cor["notes"] + notes)),
    }
    Path(args.out).write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    kinds = collections.Counter(s["kind"] for s in statements_out)
    print(
        f"{len(statements_out)} statements over {len(covered)} of {len(corrected_features)} features "
        f"({', '.join(f'{n} {k}' for k, n in kinds.most_common())}), {len(devices_out)} unconditional, "
        f"{len(implies)} implications, {len(claim_rules)} claim rules, "
        f"{sum(1 for s in statements_out if s['source'] == 'Cor 1')} statements from cor 1",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
