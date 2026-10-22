"""Every Syntax Rule of the standard's text, by subclause and number, as jsonl.
Reads the extracted text of ISO/IEC 39075:2024; output stays outside the repo."""
import json, re, sys

src, dst = sys.argv[1], sys.argv[2]
lines = open(src, encoding="utf8").read().split("\n")
noise = re.compile(r"(ISO/IEC 39075:2024\(en\)|© ISO/IEC|Licensed to|ISO Store Order|Single user licence|^--- page)")
heading = re.compile(r"^(\d+(?:\.\d+)+)\s+(.+)$")
top = re.compile(r"^(\d+)\)\s?(.*)$")
section = None
clause, title = None, None
rules, current = [], None
# Skip the table of contents: start at the first "Syntax Rules" heading in the body.
start = next(i for i, l in enumerate(lines) if l.strip() == "Syntax Rules" and i > 1500)
# Find the subclause heading before it.
for l in lines[:start][::-1]:
    m = heading.match(l.strip())
    if m and "...." not in l:
        clause, title = m.group(1), m.group(2)
        break
for l in lines[start:]:
    s = l.strip()
    if noise.search(s) or not s:
        continue
    if s in ("Syntax Rules", "General Rules", "Conformance Rules", "Format", "Function", "Access Rules"):
        if current: rules.append(current); current = None
        section = s
        continue
    m = heading.match(s)
    # Each page repeats its subclause's heading at the top: not a new subclause.
    if m and m.group(1) == clause:
        continue
    if m and not top.match(s) and len(m.group(1).split(".")) >= 2 and m.group(1)[0].isdigit() and int(m.group(1).split(".")[0]) <= 24 and ("<" in m.group(2) or m.group(2)[:1].isupper()):
        if current: rules.append(current); current = None
        clause, title, section = m.group(1), m.group(2), None
        continue
    if re.match(r"^Annex [A-Z]$", s):
        break
    if section != "Syntax Rules":
        continue
    m = top.match(s)
    # A top-level rule continues the numbering; a nested "1)" inside a rule does not.
    expected = (current["sr"] + 1) if current else 1
    if m and int(m.group(1)) == expected:
        if current: rules.append(current)
        current = {"clause": clause, "title": title, "sr": int(m.group(1)), "text": m.group(2)}
    elif current:
        current["text"] += " " + s
if current: rules.append(current)
with open(dst, "w") as out:
    for r in rules:
        out.write(json.dumps(r) + "\n")
clauses = {r["clause"] for r in rules}
print(len(rules), "syntax rules in", len(clauses), "subclauses")
