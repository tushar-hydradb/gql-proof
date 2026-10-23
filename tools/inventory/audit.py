"""Merge the audit parts (research/audit/part-*.jsonl) into one table, validate the rows
against research/audit/README.md's format, and print the counts and the findings.

    python3 -I tools/inventory/audit.py [--out research/audit/audit.jsonl] [--md]
"""
import argparse, collections, glob, json, os, sys

KEYS = ["clause", "sr", "item", "kind", "sentence", "replacement", "enforced", "check",
        "reachable", "status", "cor1", "note"]
KINDS = {"constraint", "type", "environment", "implementation", "definition"}
STATUSES = {"generated", "reading", "checked", "grammar", "open", "hypothesis", "n/a"}

def clause_key(c):
    return tuple(int(x) for x in c.split("."))

def load(paths):
    rows, errors = [], []
    for path in sorted(paths):
        with open(path) as f:
            for n, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError as e:
                    errors.append(f"{path}:{n}: {e}")
                    continue
                r["_part"] = os.path.basename(path)
                for k in KEYS:
                    if k not in r:
                        errors.append(f"{path}:{n}: missing {k}")
                        r.setdefault(k, "" if k != "sr" else 0)
                if r["kind"] not in KINDS:
                    errors.append(f"{path}:{n}: kind {r['kind']!r}")
                if r["status"] not in STATUSES:
                    errors.append(f"{path}:{n}: status {r['status']!r}")
                if r["kind"] in ("constraint", "type") and r["status"] == "n/a":
                    errors.append(f"{path}:{n}: {r['clause']} SR {r['sr']} {r['item']}: a {r['kind']} rule with status n/a")
                if r["status"] == "generated" and not r["enforced"]:
                    errors.append(f"{path}:{n}: {r['clause']} SR {r['sr']} {r['item']}: generated with no enforcement")
                if r["status"] in ("generated", "reading") and not r["check"]:
                    errors.append(f"{path}:{n}: {r['clause']} SR {r['sr']} {r['item']}: {r['status']} with no checker (not known to hold)")
                rows.append(r)
    rows.sort(key=lambda r: (clause_key(r["clause"]), int(r["sr"]), r["item"]))
    return rows, errors

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parts", default="research/audit/part-*.jsonl")
    ap.add_argument("--out", default="research/audit/audit.jsonl")
    ap.add_argument("--md", action="store_true", help="print the markdown tables for the note")
    a = ap.parse_args()
    rows, errors = load(glob.glob(a.parts))
    with open(a.out, "w") as f:
        for r in rows:
            f.write(json.dumps({k: r[k] for k in KEYS}, ensure_ascii=False) + "\n")
    print(f"{len(rows)} rows from {len(set(r['_part'] for r in rows))} parts -> {a.out}")
    if errors:
        print(f"{len(errors)} format problems:")
        for e in errors[:60]:
            print("  " + e)
    by = collections.Counter((r["kind"], r["status"]) for r in rows)
    kinds = ["constraint", "type", "environment", "implementation", "definition"]
    statuses = ["generated", "reading", "checked", "grammar", "open", "hypothesis", "n/a"]
    head = "kind            rows  " + "  ".join(f"{s:>10}" for s in statuses)
    print(head)
    for k in kinds:
        n = sum(v for (kk, _), v in by.items() if kk == k)
        print(f"{k:<14}{n:>6}  " + "  ".join(f"{by[(k, s)]:>10}" for s in statuses))
    findings = [r for r in rows if r["status"] == "open"]
    reach = [r for r in findings if r["reachable"].startswith("yes")]
    print(f"\nopen: {len(findings)} rows, {len(reach)} reachable in a cached set")
    for r in reach:
        print(f"  {r['clause']} SR {r['sr']} {r['item']} ({r['kind']}): {r['sentence'][:90]}")
        print(f"      {r['reachable'][:160]}")
    unknown = [r for r in findings if r["reachable"].startswith("unknown")]
    print(f"\nopen and reachability unknown: {len(unknown)}")
    for r in unknown:
        print(f"  {r['clause']} SR {r['sr']} {r['item']} ({r['kind']}): {r['sentence'][:100]}")
    unreach = [r for r in findings if r["reachable"].startswith("no")]
    print(f"\nopen but unreachable (grammar or claim reason): {len(unreach)}")
    for r in unreach:
        print(f"  {r['clause']} SR {r['sr']} {r['item']}: {r['reachable'][:120]}")
    readings = [r for r in rows if r["status"] == "reading"]
    print(f"\nreadings: {len(readings)}")
    repl = [r for r in rows if r["replacement"]]
    print(f"rows judged after a replacement: {len(repl)}")
    if a.md:
        print("\n| rule | kind | status | sentence |\n|---|---|---|---|")
        for r in rows:
            if r["kind"] in ("constraint", "type", "environment"):
                item = f" {r['item']}" if r["item"] else ""
                print(f"| {r['clause']} SR {r['sr']}{item} | {r['kind']} | {r['status']} | {r['sentence']} |")
    return 1 if errors else 0

if __name__ == "__main__":
    sys.exit(main())
