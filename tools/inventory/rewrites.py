"""The syntax rules that rewrite text ("effectively replaced", "equivalent to", "implicit"),
and whether research/audit/rewrite-*.jsonl has a closed row for each.

    python3 -I tools/inventory/rewrites.py [--check]
"""
import glob, json, re, sys

lines = open("iso-text/39075-2024.txt").read().split("\n")
noise = re.compile(r"Licensed to|ISO Store|Single user|© ISO|^ISO/IEC 39075|--- page|^\d+$")
head = re.compile(r"^(\d+(?:\.\d+)?) (<[^>]+>.*|[A-Z][^.]*)$")
rules, clause, section, current = {}, None, None, None
for i, l in enumerate(lines):
    if i < 2600:
        continue
    m = head.match(l)
    if m and "." * 5 not in l:
        if m.group(1) != clause:
            clause, section, current = m.group(1), None, None
        continue
    s = l.strip()
    if s in ("Syntax Rules", "General Rules", "Conformance Rules", "Format", "Function"):
        section, current = s, None
        continue
    if section != "Syntax Rules" or clause is None or noise.search(l):
        continue
    r = re.match(r"^(\d+)\) ", l)
    if r:
        n = int(r.group(1))
        if n == (1 if current is None else current[1] + 1):
            current = (clause, n)
            rules.setdefault(current, "")
    if current:
        rules[current] += " " + l
pat = re.compile(r"effectively replaced|is equivalent to|are equivalent to|is implicit|are implicit")
rewrites = sorted((k for k, t in rules.items() if pat.search(t)),
                  key=lambda k: (tuple(int(x) for x in k[0].split(".")), k[1]))
if "--check" not in sys.argv:
    for c, n in rewrites:
        print(f"{c} SR {n}")
    sys.exit(0)
rows = {}
for f in glob.glob("research/audit/rewrite-*.jsonl"):
    for l in open(f):
        if l.strip():
            r = json.loads(l)
            rows.setdefault((r["clause"], int(r["sr"])), []).append(r)
missing = [k for k in rewrites if k not in rows]
open_rows = [r for rs in rows.values() for r in rs if r["status"] != "closed"]
print(f"{len(rewrites)} rewrite rules, {len(rewrites) - len(missing)} with rows, {len(open_rows)} open rows")
for c, n in missing:
    print(f"  no row: {c} SR {n}")
for r in open_rows:
    print(f"  open: {r['clause']} SR {r['sr']}: {r['consequence'][:120]}")
sys.exit(1 if missing or open_rows else 0)
