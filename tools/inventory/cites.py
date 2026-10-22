"""Which Syntax Rules the code cites, by component: `16.3 SR 10, 16`, `14.3 SR 3-5`,
`16.4 SR 6 b) i)` and the like, in comments and strings under src/."""
import json, os, re, sys, collections

root, dst = sys.argv[1], sys.argv[2]
cite = re.compile(r"(\d+\.\d+(?:\.\d+)?)\s+SR\s+((?:\d+(?:\s*[a-z]\)?)?(?:\s*[ivx]+\)?)?(?:\s*(?:,|-|and|to)\s*)?)+)")
num = re.compile(r"\d+")
def component(path):
    p = path.replace(root + "/", "")
    if p.startswith("src/context/scope"): return "scope"
    if p.startswith("src/context/types"): return "types"
    if p.startswith("src/verify/scope"): return "check-scope"
    if p.startswith("src/verify/types"): return "check-types"
    if p.startswith("src/verify"): return "check-syntax"
    if p.startswith("src/context"): return "engine"
    if p == "src/refine.rs": return "automata"
    if p == "src/scope.rs": return "old-scope"
    if p == "src/tokens.rs": return "tokens"
    return "other:" + p
out = collections.defaultdict(lambda: collections.defaultdict(list))
for dirpath, _, files in os.walk(os.path.join(root, "src")):
    for f in files:
        if not f.endswith(".rs"): continue
        path = os.path.join(dirpath, f)
        for i, line in enumerate(open(path, encoding="utf8"), 1):
            for m in cite.finditer(line):
                clause, rest = m.group(1), m.group(2)
                # Ranges "3-5" expand; sub-item letters after a number are ignored.
                parts = re.split(r"\s*(?:,|and)\s*", rest)
                srs = []
                for part in parts:
                    r = re.match(r"(\d+)\s*(?:-|to)\s*(\d+)", part)
                    if r:
                        srs += range(int(r.group(1)), int(r.group(2)) + 1)
                    else:
                        n = num.match(part.strip())
                        if n: srs.append(int(n.group()))
                for s in srs:
                    out[f"{clause} SR {s}"][component(path)].append(f"{path.replace(root + '/', '')}:{i}")
with open(dst, "w") as o:
    json.dump(out, o, indent=1, sort_keys=True)
by = collections.Counter(c for v in out.values() for c in v)
print(len(out), "distinct rules cited;", dict(by))
