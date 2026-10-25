"""Merge the audit parts (research/audit/part-*.jsonl) into one table, validate the rows
against research/audit/README.md's format, and print the counts and the findings.

    python3 -I tools/inventory/audit.py [--out research/audit/audit.jsonl] [--md]
"""
import argparse, collections, glob, json, os, re, sys

KEYS = ["clause", "sr", "item", "kind", "sentence", "replacement", "enforced", "check",
        "reachable", "status", "cor1", "note"]
KINDS = {"constraint", "type", "environment", "implementation", "definition"}
STATUSES = {"generated", "reading", "permission", "checked", "grammar", "open", "hypothesis", "n/a"}

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
                if r["status"] in ("generated", "reading", "permission") and not r["check"]:
                    errors.append(f"{path}:{n}: {r['clause']} SR {r['sr']} {r['item']}: {r['status']} with no checker (not known to hold)")
                rows.append(r)
    rows.sort(key=lambda r: (clause_key(r["clause"]), int(r["sr"]), r["item"]))
    global UNPROBED
    # The checker column quotes the rule strings the checker reports; each must be a string
    # literal in the checker's sources, or the row claims a check nobody wrote.
    src = ""
    for f in glob.glob("src/verify.rs") + glob.glob("src/verify/*.rs"):
        src += open(f).read()
    tests = "".join(open(f).read() for f in glob.glob("tests/*.rs"))
    unprobed = set()
    for r in rows:
        if r["kind"] in ("constraint", "type") and r["status"] in ("generated", "reading", "permission", "checked", "grammar"):
            quoted = re.findall(r'"([0-9][0-9.]* SR [^"]+|ISO BNF)"', r["check"])
            named = re.findall(r"test:(\w+)", r["check"])
            for t in named:
                if f"fn {t}(" not in tests:
                    errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: no test {t}")
            if not quoted and not named:
                errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: the check column quotes no rule string")
            for q in quoted:
                if f'"{q}"' not in src:
                    errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: the checker reports no {q!r}")
                elif not red_probe(q, tests) and q not in PROBE_EXEMPT:
                    unprobed.add(q)
    UNPROBED = sorted(unprobed)
    for q in UNPROBED:
        errors.append(f"{q}: no red probe in tests/ (a call reporting it on a violating input)")
    for r in rows:
        if r["kind"] in ("constraint", "type") and r["status"] == "open":
            errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: open")
    # A `permission` row is a reading that lets in more than the text: it holds only under the
    # claim's H4, which names it.
    claim = open("research/soundness-claim.md").read()
    h4 = claim.split("## hypothesis H4", 1)[1].split("\n## ", 1)[0] if "## hypothesis H4" in claim else ""
    for r in rows:
        if r["status"] == "permission":
            name = f"{r['clause']} SR {r['sr']}" + (f" {r['item']}" if r["item"] else "")
            if name not in h4:
                errors.append(f"{name}: a permission not named in H4 of research/soundness-claim.md")
    # A `checked` row is kept by the gate alone: its rule strings are in verify::GATE_ONLY, so
    # a flag on them withholds a tree instead of stopping a run.
    m = re.search(r"pub const GATE_ONLY: &\[&str\] = &\[(.*?)\];", open("src/verify.rs").read(), re.S)
    gate = set(re.findall(r'"([^"]+)"', m.group(1))) if m else set()
    # A row the generator is said to keep must quote a string the run counts as a generator
    # bug when flagged; a gate-only string is withheld silently, so it would not test that.
    for r in rows:
        if r["status"] in ("generated", "reading", "permission"):
            qs = re.findall(r'"([0-9][0-9.]* SR [^"]+)"', r["check"])
            if qs and all(q in gate for q in qs):
                errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: {r['status']}, but {', '.join(qs)} gate-only (a generator miss is not counted): status checked")
    for r in rows:
        if r["status"] == "checked":
            for q in re.findall(r'"([0-9][0-9.]* SR [^"]+)"', r["check"]):
                if q not in gate:
                    errors.append(f"{r['clause']} SR {r['sr']} {r['item']}: checked, but {q!r} is not in verify::GATE_ONLY")
    return rows, errors

UNPROBED = []

PROBE_CALL = re.compile(r"\b(bad|red)\w*\s*\(")

def red_probe(q, tests):
    """Whether `q` is expected on a violating input somewhere in the tests: inside a `bad*(` or
    `red*(` call, as `Some(q)` or in a list of expected violations, or asserted present. A bare
    entry of a rule list (the automaton agreement test's) is no probe."""
    for m in re.finditer(re.escape(f'"{q}"'), tests):
        back = tests[max(0, m.start() - 600):m.start()]
        calls = list(PROBE_CALL.finditer(back))
        if calls and ";" not in back[calls[-1].start():] and "#[test]" not in back[calls[-1].start():]:
            return True
        line = tests[tests.rfind("\n", 0, m.start()) + 1:tests.find("\n", m.end())]
        if re.fullmatch(r'\s*"[^"]+",\s*', line):
            continue
        pre = tests[max(0, m.start() - 10):m.start()]
        if pre.endswith(("Some(", "vec![", "[", ", ", "contains(&")):
            return True
    return False


def write_table(rows, path):
    """The per-rule table: every constraint, type and environment row."""
    keep = [r for r in rows if r["kind"] in ("constraint", "type", "environment")]
    c = collections.Counter((r["kind"], r["status"]) for r in keep)
    statuses = ("generated", "reading", "permission", "checked", "grammar", "hypothesis", "open")
    out = [
        "# the soundness table",
        "",
        "> for agents: generated by `python3 -I tools/inventory/audit.py --table research/soundness-table.md`; do not edit by hand. people start at the [readme](../README.md)",
        "",
        "one row per constraining sentence of a syntax rule. status: `generated` the generator keeps it as written and the checker reports it; `reading` kept by a stricter reading, the checker reports it; `permission` a reading that lets in more than the text, holding under H4; `checked` the checker reports it and the gate alone keeps it out (`verify::GATE_ONLY`); `grammar` no derivation breaks it; `hypothesis` holds under H1. the argument: `soundness-claim.md`",
        "",
        "| kind | " + " | ".join(statuses) + " |",
        "|---|" + "---|" * len(statuses),
    ]
    for k in ("constraint", "type", "environment"):
        out.append(f"| {k} | " + " | ".join(str(c[(k, st)]) for st in statuses) + " |")
    out += ["", "| rule | kind | status | in our words | checker |", "|---|---|---|---|---|"]
    for r in keep:
        item = f" {r['item']}" if r["item"] else ""
        out.append(
            f"| {r['clause']} SR {r['sr']}{item} | {r['kind']} | {r['status']} | "
            f"{r['sentence'].replace('|', '/')} | {r['check'].replace('|', '/')[:90]} |"
        )
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")
# Rule strings no text can break, so no red probe exists; each with the reason.
PROBE_EXEMPT = {
    "16.9 SR 2": "a path variable is declared only at a <path pattern>, always an unconditional singleton",
    "20.6 SR 6": "every linear query statement ends in a result statement once 14.12 SR 27 makes a SELECT a RETURN",
    "9.2 SR 7": "on the rewritten text every linear query statement contains a result statement (a SELECT is a RETURN, 14.12 SR 27 a; an EXISTS holds one, 19.4 SR 2, 3)",
}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parts", default="research/audit/part-*.jsonl")
    ap.add_argument("--out", default="research/audit/audit.jsonl")
    ap.add_argument("--md", action="store_true", help="print the markdown tables for the note")
    ap.add_argument("--table", help="write the per-rule soundness table (markdown) to this file")
    a = ap.parse_args()
    rows, errors = load(glob.glob(a.parts))
    with open(a.out, "w") as f:
        for r in rows:
            f.write(json.dumps({k: r[k] for k in KEYS}, ensure_ascii=False) + "\n")
    print(f"{len(rows)} rows from {len(set(r['_part'] for r in rows))} parts -> {a.out}")
    if errors:
        print(f"{len(errors)} format problems:")
        for e in errors:
            print("  " + e)
    if UNPROBED:
        print(f"{len(UNPROBED)} rule strings the checker reports with no probe in tests/: {', '.join(UNPROBED)}")
    by = collections.Counter((r["kind"], r["status"]) for r in rows)
    kinds = ["constraint", "type", "environment", "implementation", "definition"]
    statuses = ["generated", "reading", "permission", "checked", "grammar", "open", "hypothesis", "n/a"]
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
    if a.table:
        write_table(rows, a.table)
    if a.md:
        print("\n| rule | kind | status | sentence |\n|---|---|---|---|")
        for r in rows:
            if r["kind"] in ("constraint", "type", "environment"):
                item = f" {r['item']}" if r["item"] else ""
                print(f"| {r['clause']} SR {r['sr']}{item} | {r['kind']} | {r['status']} | {r['sentence']} |")
    return 1 if errors else 0

if __name__ == "__main__":
    sys.exit(main())
