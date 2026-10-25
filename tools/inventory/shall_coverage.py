"""Every syntax rule whose text says `shall` has a row in the audit that is not a definition:
the audit's completeness, checked against the standard's text (iso-text/, gitignored).

    python3 -I tools/inventory/shall_coverage.py [iso-text/39075-2024.txt] [research/audit/audit.jsonl]
"""
import json, re, sys

text_path = sys.argv[1] if len(sys.argv) > 1 else "iso-text/39075-2024.txt"
audit_path = sys.argv[2] if len(sys.argv) > 2 else "research/audit/audit.jsonl"
lines = open(text_path).read().split("\n")
noise = re.compile(r"Licensed to|ISO Store|Single user|© ISO|^ISO/IEC 39075|--- page|^\d+$")
head = re.compile(r"^(\d+(?:\.\d+)?) (<[^>]+>.*|[A-Z][^.]*)$")

# The extraction loses indentation, so a numbered sub-list inside rule N (`1) 2) .. N+1)`)
# reads like the next top-level rule. Where both are possible the split is ambiguous; each
# ambiguous split is resolved here by hand, from the text, and an unresolved one fails the
# run (found by the sixth review: five clauses were split wrongly and passed by luck).
RESOLVE = {
    ("13.3", 4, "4) No <set property item> imme"): "top",
    ("14.10", 5, "5) LetOB_COL be a newcolumnwho"): "sub",
    ("16.6", 3, "3) If PPP is <counted shortest"): "sub",
    ("16.15", 3, "3) The declared type of the in"): "sub",
    ("17.2", 3, "3) The graph identified by CGP"): "sub",
    ("17.3", 3, "3) The graph type identified b"): "sub",
    ("17.4", 3, "3) The binding table identifie"): "sub",
    ("20.7", 3, "3) At least one <result> in a "): "top",
    ("20.24", 4, "4) If <trim character string> "): "sub",
}

# The clause each line belongs to: the last header line seen that is not in the contents.
rules = {}  # (clause, n) -> text
unresolved = []
clause, section, current, nested = None, None, None, None
for i, l in enumerate(lines):
    if i < 2600:  # the table of contents and front matter
        continue
    m = head.match(l)
    if m and "." * 5 not in l:
        if m.group(1) != clause:
            clause, section, current, nested = m.group(1), None, None, None
        continue
    s = l.strip()
    if s in ("Syntax Rules", "General Rules", "Conformance Rules", "Format", "Function"):
        section, current, nested = s, None, None
        continue
    if section != "Syntax Rules" or clause is None or noise.search(l):
        continue
    # Top level rules count up one at a time; a `1)` inside a rule opens a numbered sub-list.
    r = re.match(r"^(\d+)\) ", l)
    if r:
        n = int(r.group(1))
        expected = 1 if current is None else current[1] + 1
        top = n == expected
        if current is not None and n == 1:
            nested, top = 1, False
        elif nested is not None and n == nested + 1:
            nested = n
            if top:
                key = (clause, n, l[:30])
                if key not in RESOLVE:
                    unresolved.append(key)
                top = RESOLVE.get(key) == "top"
        if top:
            current, nested = (clause, n), None
            rules.setdefault(current, "")
    if current:
        rules[current] += " " + l
if unresolved:
    print("ambiguous rule splits not resolved in RESOLVE (read the text, add each):")
    for u in unresolved:
        print(f"  {u}")
    sys.exit(1)

# A shall that constrains nothing, each with the reason.
EXEMPT = {
    ("14.7", 7): "deleted by cor 1",
    ("20.7", 2): "the shall is item a, deleted by cor 1",
    ("21.3", 25): "'shall be considered upper-case' defines how keywords are read",
    ("22.17", 3): "applied only hypothetically by its importers (18.1 SR 7, 18.1 CR 2)",
}

rows = [json.loads(x) for x in open(audit_path)]
covered = {(r["clause"], int(r["sr"])) for r in rows if r["kind"] != "definition"}
listed = {(r["clause"], int(r["sr"])) for r in rows}
gaps = [(k, t) for k, t in sorted(rules.items(), key=lambda kv: (tuple(int(x) for x in kv[0][0].split(".")), kv[0][1]))
        if re.search(r"\bshall\b", t) and k not in covered and k not in EXEMPT]
# Cor 1 replaces or inserts syntax rules the 2024 text does not have: each with a shall needs
# a constraining row too (grammar/corrigendum.json, our own extraction).
cor1 = json.load(open("grammar/corrigendum.json"))["items"]
for item in cor1:
    if item["kind"] != "syntax rule" or not re.search(r"\bshall\b", item["text"]):
        continue
    n = int(re.match(r"\s*(\d+)", item["text"]).group(1))
    k = (item["subclause"], n)
    if k not in covered and k not in EXEMPT and k not in [g[0] for g in gaps]:
        gaps.append((k, "cor 1: " + item["text"]))
SHALL = re.compile(r"\bshall\b")
with_shall = sum(1 for t in rules.values() if SHALL.search(t))
print(f"{len(rules)} syntax rules in the text, {with_shall} with a shall")
print(f"{len(gaps)} with a shall and no constraining row in the audit (cor 1's replaced and inserted rules included)")
for (c, n), t in gaps:
    where = "listed as definition only" if (c, n) in listed else "not in the audit"
    m = re.search(r"[^.]*\bshall\b[^.]*", t)
    print(f"  {c} SR {n} ({where}): {m.group(0).strip()[:110] if m else ''}")
print(f"{len(EXEMPT)} exempt: " + "; ".join(f"{c} SR {n} ({why})" for (c, n), why in EXEMPT.items()))
sys.exit(1 if gaps else 0)
