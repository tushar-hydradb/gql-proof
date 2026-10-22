"""Merges the per-clause classifications, checks every rule has exactly one, and prints the
counts and the per-clause lists the inventory reports. No text of the standard is output."""
import json, glob, sys, collections, os

d = sys.argv[1]
rules = [json.loads(l) for l in open(os.path.join(d, "srs.jsonl"))]
keys = [(r["clause"], r["sr"]) for r in rules]
title = {r["clause"]: r["title"] for r in rules}
got = {}
for f in sorted(glob.glob(os.path.join(d, "class-*.jsonl"))):
    for l in open(f):
        if not l.strip():
            continue
        c = json.loads(l)
        k = (str(c["clause"]), int(c["sr"]))
        if k in got:
            print("duplicate", k, file=sys.stderr)
        got[k] = c
missing = [k for k in keys if k not in got]
extra = [k for k in got if k not in set(keys)]
print(f"rules {len(keys)}, classified {len(got)}, missing {len(missing)}, extra {len(extra)}", file=sys.stderr)
if missing:
    print("missing:", missing[:20], file=sys.stderr)
cor1 = {l.split(" (")[0] for l in open(os.path.join(d, "cor1-srs.txt"))}
kinds = collections.Counter(got[k]["kind"] for k in keys if k in got)
status = collections.Counter((got[k]["kind"], got[k]["status"]) for k in keys if k in got)
json.dump({"kinds": kinds, "status": {f"{a}/{b}": n for (a, b), n in status.items()},
           "missing": missing}, open(os.path.join(d, "counts.json"), "w"), indent=1)
print(json.dumps({"kinds": kinds}, indent=1))
for (a, b), n in sorted(status.items()):
    print(f"{a:15} {b:14} {n}")
