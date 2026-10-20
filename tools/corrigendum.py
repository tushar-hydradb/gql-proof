"""Reads ISO/IEC 39075:2024/Cor 1:2026 into its edit instructions, and applies the grammar ones.

Cor 1 is a list of items under subclause headings, each "N. Rationale: ..." followed by one
instruction ("Replace Conformance Rule 7) with:", "Move the BNF element ...") and its new text.
Every instruction is classified; one that matches no known shape fails the run, so nothing is
skipped silently. iso's machine readable files at standards.iso.org are still the 2024 ones, so
the grammar edits are applied here to `bnf.xml`, and `conformance.py` applies the rest.

    .venv-pdf/bin/python -I tools/corrigendum.py <cor 1 pdf> <iso pdf> <grammar dir>

writes `<grammar dir>/corrigendum.json` and `<grammar dir>/ISO_IEC_39075(en)+Cor1.bnf.xml`.
"""

import argparse
import copy
import json
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

import pypdfium2 as pdfium
from lark import Lark, Transformer, v_args

sys.path.insert(0, str(Path(__file__).parent))
from conformance import CODE, bookmarks, join, positioned_lines, same_text, squash, table_rows  # noqa: E402

# Cor 1's headings are 12 and 14 point at the left margin; its body is 11 point.
HEADING_SIZE = 11.5
MARGIN = 60
HEADING = re.compile(r"^(\d+(?:\.\d+)*) (.+)$")
ITEM = re.compile(r"^(\d+)\. Rationale: (.*)$")
NT_ = r"<([^<>]+)>"
RULES = r"((?:\d+\)(?:,? (?:and )?)?)+)"
KEYWORD_LISTS = ("reserved word", "pre-reserved word", "non-reserved word")

# (kind, applied by, pattern). First match wins, so the specific shapes come first.
INSTRUCTIONS = [
    ("conformance rule add", "conformance", r"(?:Add|Insert) the following Conformance Rules?:"),
    ("conformance rule replace", "conformance", rf"Replace Conformance Rules? {RULES} (?:with|as follows):"),
    ("conformance rule delete", "conformance", rf"Delete Conformance Rules? {RULES}\."),
    ("production replace", "grammar", rf"Replace the (?:Format|production) (?:of|for) {NT_}(?: as follows)?:?"),
    ("element move", "grammar", rf"Move the BNF element {NT_} from the BNF production {NT_} to the BNF production {NT_}\."),
    ("list add", "grammar", rf"Add “(\w+)” to the list of {NT_}"),
    ("list remove", "grammar", rf"Remove “(\w+)” from the list of {NT_}"),
    ("table rows delete", "conformance", r"Delete the following rows from Table (\d+), “([^”]*)”:"),
    ("table rows add", "conformance", r"Add the following rows to Table (\d+), “([^”]*)”:"),
    ("list item replace", "conformance", r"Replace list item (\d+)\) with:"),
    ("syntax rule", None, r"(?:Delete|Replace|Insert)(?: the following)? Syntax Rules?.*"),
    ("general rule", None, r"(?:Delete|Replace|Insert)(?: the following)? General Rules?.*"),
    ("figure", None, r"Replace Figure \d+, “[^”]*” with:"),
    ("paragraph", None, r"(?:Replace|Insert|Add) (?:the following )?(?:the )?\S+ paragraph.*"),
    ("bullet", None, r"Replace the \S+ bullet of the \S+ paragraph with:"),
    ("item", None, r"Replace item \d+\) with:"),
]


class Item:
    def __init__(self, page, y, subclause, title, number, rationale):
        self.page, self.y, self.subclause, self.title = page, y, subclause, title
        self.number, self.rationale = number, rationale
        self.instruction, self.lines, self.kind, self.by, self.args = None, [], None, None, ()


def subclause_of(number, title, marks, notes):
    """The 2024 subclause a Cor 1 heading names. Some headings carry only the clause number
    ("24 Minimum conformance"): then the title picks the subclause inside that clause."""
    same = [n for _, n, t in marks if n == number and squash(t) == squash(title)]
    if same:
        return same[0]
    inside = [n for _, n, t in marks if n.split(".")[0] == number.split(".")[0] and squash(t) == squash(title)]
    if len(inside) != 1:
        raise SystemExit(f"cor 1 heading “{number} {title}” names no 2024 subclause")
    notes.append(f"cor 1 heading “{number} {title}” is {inside[0]}")
    return inside[0]


def items(pdf, marks, notes):
    """Every item, with its subclause, rationale, instruction and the lines after it."""
    out, heading, cur, rationale = [], None, None, False
    for p in range(len(pdf)):
        lines = positioned_lines(pdf[p])
        for text, chars in lines:
            size, left, y = max(c[4] for c in chars), chars[0][1], chars[0][3]
            if size > HEADING_SIZE:
                m = HEADING.match(text)
                if m and left < MARGIN:
                    heading = [m.group(1), m.group(2)]
                elif heading and left > MARGIN:
                    heading[1] += " " + text
                continue
            m = ITEM.match(text)
            if m and left < MARGIN and heading:
                cur = Item(p, y, subclause_of(*heading, marks, notes), heading[1], int(m.group(1)), m.group(2))
                out.append(cur)
                rationale = True
                continue
            if cur is None:
                continue
            # the rationale wraps indented further than the instruction that follows it
            if rationale and left > MARGIN + 40:
                cur.rationale += " " + text
                continue
            rationale = False
            cur.lines.append((text, p, y))
    for it in out:
        classify(it)
    return out


def classify(it):
    """The instruction is the shortest run of the item's first lines that is one known shape."""
    for n in range(1, min(3, len(it.lines)) + 1):
        text = join([l for l, _, _ in it.lines[:n]])
        for kind, by, pattern in INSTRUCTIONS:
            m = re.fullmatch(pattern, text)
            if m:
                it.instruction, it.kind, it.by, it.args = text, kind, by, m.groups()
                it.page, it.y = it.lines[n - 1][1], it.lines[n - 1][2]
                it.lines = it.lines[n:]
                return
    raise SystemExit(f"{it.subclause} item {it.number}: no known instruction in “{it.lines[0][0] if it.lines else ''}”")


def rule_numbers(text):
    return re.findall(r"(\d+)\)", text or "")


# ISO's BNF notation, enough for the productions Cor 1 replaces. Checked against iso's own
# conversion of every 2024 production it covers before it is trusted with Cor 1's.
BNF = Lark(
    r"""
    // <pre-reserved word> opens its list with a bar
    rhs: "|"? alt ("|" alt)*
    alt: item+
    item: atom REPEAT?
    ?atom: NT -> nt
         | KW -> kw
         | "[" rhs "]" -> opt
         | "{" rhs "}" -> group
         | SEE -> see
    NT: /<[^<>]+>/
    KW: /[A-Z][A-Z0-9_]*/
    REPEAT: "..."
    SEE: "!! See the Syntax Rules."
    %ignore /\s+/
    """,
    start="rhs",
    parser="lalr",
)


@v_args(inline=True)
class ToXml(Transformer):
    def rhs(self, *alts):
        return alts

    def alt(self, *items):
        return [e for i in items for e in i]

    def item(self, atom, repeat=None):
        return [atom, ET.Element("repeat")] if repeat else [atom]

    def nt(self, t):
        return ET.Element("BNF", name=str(t)[1:-1])

    def kw(self, t):
        e = ET.Element("kw")
        e.text = str(t)
        return e

    def see(self, _):
        return ET.Element("seeTheRules")

    def opt(self, alts):
        return wrap("opt", alts)

    def group(self, alts):
        return wrap("group", alts)


def wrap(tag, alts):
    e = ET.Element(tag)
    if len(alts) == 1:
        e.extend(alts[0])
    else:
        for a in alts:
            alt = ET.SubElement(e, "alt")
            alt.extend(a)
    return e


def to_rhs(text):
    alts = ToXml().transform(BNF.parse(text))
    # "<a> | <b> !! See the Syntax Rules." refers the whole definition to its rules
    see = len(alts) > 1 and alts[-1][-1].tag == "seeTheRules"
    rhs = wrap("rhs", [a[:-1] if see and a is alts[-1] else a for a in alts])
    if see:
        rhs.append(ET.Element("seeTheRules"))
    return rhs


def shape(e):
    return (e.tag, e.get("name"), (e.text or "").strip() if e.tag == "kw" else "", [shape(c) for c in e])


def text_productions(path):
    """bnf.txt's productions by name: a line `<name> ::=`, its body up to the next blank line."""
    out, name, body = {}, None, []
    for line in Path(path).read_text().splitlines() + [""]:
        m = re.fullmatch(r"<([^<>]+)> ::=\s*", line)
        if m:
            name, body = m.group(1), []
        elif not line:
            # only an empty line ends one: <reserved word> has a line of spaces inside it
            if name:
                out[name] = " ".join(body)
            name = None
        elif name:
            body.append(line.strip())
    return out


def check_notation(root, txt):
    """The notation reader must turn bnf.txt into exactly what bnf.xml holds, for every
    production made only of names, keywords, groups, options and repetition."""
    plain = {"rhs", "alt", "BNF", "kw", "opt", "group", "repeat", "seeTheRules"}
    checked = 0
    for d in root.iter("BNFdef"):
        rhs = d.find("rhs")
        if any(e.tag not in plain for e in rhs.iter()):
            continue
        name = d.get("name")
        if shape(to_rhs(txt[name])) != shape(rhs):
            raise SystemExit(f"the bnf notation reader disagrees with bnf.xml on <{name}>")
        checked += 1
    return checked


def edit_grammar(root, before, it, notes):
    """Applies one grammar item to `root`; `before` is the 2024 grammar, untouched."""
    defs = {d.get("name"): d for d in root.iter("BNFdef")}
    old_defs = {d.get("name"): d for d in before.iter("BNFdef")}

    def need(name):
        if name not in defs:
            raise SystemExit(f"{it.subclause}: cor 1 edits <{name}>, which the 2024 grammar does not define")
        return defs[name]

    if it.kind == "production replace":
        (name,) = it.args
        d = need(name)
        text = join([l for l, _, _ in it.lines])
        m = re.fullmatch(rf"<{re.escape(name)}> ::=(.*)", text)
        if not m:
            raise SystemExit(f"{it.subclause}: the new production for <{name}> does not read as one")
        new = to_rhs(m.group(1))
        old = d.find("rhs")
        if shape(new) == shape(old):
            raise SystemExit(f"{it.subclause}: the new production for <{name}> is the old one")
        d.remove(old)
        d.append(new)
        return {"production": name, "text": m.group(1).strip()}
    if it.kind == "element move":
        element, source, target = it.args
        alts = [a for a in need(source).find("rhs").findall("alt") if shape_names(a) == [element]]
        if len(alts) != 1:
            raise SystemExit(f"{it.subclause}: <{source}> has no alternative that is just <{element}>")
        need(source).find("rhs").remove(alts[0])
        need(target).find("rhs").append(alts[0])
        return {"element": element, "from": source, "to": target}
    word, name = it.args

    def holding(list_name, where=defs):
        return [a for a in where[list_name].find("rhs").findall("alt") if [k.text for k in a.iter("kw")] == [word]]

    alts = holding(need(name).get("name"))
    if it.kind == "list remove" and not alts:
        # 21.3's three word lists: a removal that names the wrong one is read as the one
        # holding the word in 2024, if exactly one does, and the reading is named
        others = [n for n in KEYWORD_LISTS if n != name and holding(n, old_defs)]
        if len(others) != 1:
            raise SystemExit(f"{it.subclause}: {word} is not in <{name}>")
        notes.append(f"{it.subclause}: cor 1 removes {word} from <{name}>, the 2024 grammar has it in <{others[0]}>: read as that")
        name, alts = others[0], holding(others[0])
    rhs = need(name).find("rhs")
    if it.kind == "list add":
        if alts:
            raise SystemExit(f"{it.subclause}: {word} is already in <{name}>")
        alt = ET.Element("alt")
        ET.SubElement(alt, "kw").text = word
        # in alphabetical place, after anything that is not a keyword
        after = [i for i, a in enumerate(rhs) if a.find("kw") is None or a.find("kw").text < word]
        rhs.insert(after[-1] + 1 if after else 0, alt)
    else:
        if len(alts) != 1:
            raise SystemExit(f"{it.subclause}: {word} is not in <{name}>")
        rhs.remove(alts[0])
    return {"word": word, "list": name, **({"reading": f"<{name}>"} if name != it.args[1] else {})}


def shape_names(alt):
    return [e.get("name") for e in alt if e.tag == "BNF"] if len(alt) == 1 else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cor")
    ap.add_argument("iso")
    ap.add_argument("grammar")
    args = ap.parse_args()
    grammar = Path(args.grammar)
    notes = []

    marks = bookmarks(pdfium.PdfDocument(args.iso))
    pdf = pdfium.PdfDocument(args.cor)
    found = items(pdf, marks, notes)

    tree = ET.parse(grammar / "ISO_IEC_39075(en).bnf.xml")
    root = tree.getroot()
    before = copy.deepcopy(root)
    checked = check_notation(root, text_productions(grammar / "ISO_IEC_39075(en).bnf.txt"))

    tables = [it for it in found if it.kind.startswith("table rows")]
    rows = table_rows(args.cor, range(min(it.page for it in tables), len(pdf))) if tables else []
    # a table belongs to the last table instruction above it (pdfplumber measures from the
    # top of the page, pdfium from the bottom)
    for r in rows:
        at = (r["page"], r["top"])
        owner = [it for it in tables if (it.page, pdf[it.page].get_height() - it.y) < at][-1]
        owner.rows = getattr(owner, "rows", []) + [r]

    out = []
    for it in found:
        entry = {
            "subclause": it.subclause,
            "title": it.title,
            "item": it.number,
            "rationale": " ".join(it.rationale.split()),
            "instruction": it.instruction,
            "kind": it.kind,
            "applied": it.by,
            "page": it.page + 1,
        }
        if it.kind.startswith("conformance rule"):
            entry["rules"] = rule_numbers(it.args[0]) if it.args else []
        if it.kind.startswith("conformance rule") or it.kind == "list item replace" or it.by is None:
            entry["text"] = join([l for l, _, _ in it.lines])
        if it.kind == "list item replace":
            entry["rules"] = list(it.args)
        if it.kind.startswith("table rows"):
            if int(it.args[0]) != 10:
                raise SystemExit(f"{it.subclause}: cor 1 edits table {it.args[0]}, only table 10 is read")
            entry["rows"] = [{k: r[k] for k in ("feature", "name", "implied", "names", "either")} for r in getattr(it, "rows", [])]
            if not entry["rows"]:
                raise SystemExit(f"{it.subclause}: no rows under “{it.instruction}”")
        if it.by == "grammar":
            entry.update(edit_grammar(root, before, it, notes))
        out.append(entry)

    # every feature cor 1 names, with the name it gives
    names = {}
    for e in out:
        for code, name in re.findall(rf"Feature ({CODE}), “([^”]*)”", " ".join([e["rationale"], e.get("text", "")])):
            if same_text(names.setdefault(code, name)) != same_text(name):
                raise SystemExit(f"cor 1 names {code} both “{names[code]}” and “{name}”")

    ET.indent(tree, space="   ")
    tree.write(grammar / "ISO_IEC_39075(en)+Cor1.bnf.xml", encoding="UTF-8", xml_declaration=True)
    (grammar / "corrigendum.json").write_text(
        json.dumps({"items": out, "features": names, "notes": notes}, indent=1, ensure_ascii=False) + "\n"
    )
    kinds = {}
    for e in out:
        kinds[e["applied"] or "recorded"] = kinds.get(e["applied"] or "recorded", 0) + 1
    for n in notes:
        print(n, file=sys.stderr)
    print(
        f"cor 1: {len(out)} items ({', '.join(f'{n} {k}' for k, n in kinds.items())}), "
        f"{sum(len(e.get('rows', [])) for e in out)} table rows, notation checked on {checked} productions",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
