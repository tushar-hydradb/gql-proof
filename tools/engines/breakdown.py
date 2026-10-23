"""Sorts an engine's results (jsonl from tools/engines/*: sentence, outcome, status, message)
into why each sentence was refused: our sentence is invalid, the engine's documented
deviation, an engine parse gap, a data exception raised as it should, the runner's
environment, a bug already reported. The rules below are turbolay's messages at #243
(484d1a72); a new engine or head needs its own.

    python3 -I tools/engines/breakdown.py results.jsonl
"""

import collections
import json
import re
import sys

# Refusals of our own sentences: syntax rules the generator does not enforce yet.
OURS = [
    ("a path pattern has a positive minimum node count", "16.7 SR 16: path pattern with no node"),
    ("simplified negation, conjunction", "16.12: quantifier or ? inside a simplified pattern"),
    ("named subpath has a positive minimum node count", "16.7 SR 20: subpath with no node"),
    ("positive minimum path length", "16.7 SR 8: quantified or questioned primary of length 0"),
    ("TRIM ... FROM needs", "20.24 SR 3: TRIM with a bare FROM"),
    ("under DIFFERENT EDGES a selective", "16.4 SR 12: selective pattern not alone"),
    ("a VALUE subquery returns at most one row", "20.6 SR 10: VALUE body not one row"),
    ("quantified primaries do not nest", "16.7 SR 9: quantifier directly under a quantifier"),
    ("a quantifier's upper bound is greater than 0", "16.11 SR 3: upper bound 0"),
    ("minimum exceeds maximum", "16.11 SR 3: upper bound below lower"),
]


def bucket(r):
    m, s, st = r.get("message", ""), r["sentence"], r["status"]
    if r["outcome"] == "ok":
        return "accepted", ""
    for key, why in OURS:
        if key in m:
            return "ours: invalid sentence", why
    if re.search(r"\bEXISTS\s*\{\s*FINISH\s*\}", s):
        return "ours: invalid sentence", "19.4 SR 5: EXISTS body is FINISH (empty type)"
    if '@""' in s or "@``" in s:
        return "ours: invalid sentence", "21.3 SR 4: empty delimited identifier"
    if "NULL . " in s:
        return "ours: invalid sentence", "20.11: property of NULL"
    if "bounds are at most" in m:
        return "engine: documented deviation", "IL018: a quantifier bound above 255"
    if st == "42002":
        return "environment", "no parameters passed by the runner"
    if st.startswith("22"):
        return "dynamic: raised as it should", m.split(" - ", 1)[-1][:60]
    if "FINISH cannot end an arm" in m or ("FINISH NEXT CALL" in s and "statement boundary" in m):
        return "engine: bug already reported", "FINISH in a composite query or before NEXT CALL"
    if re.search(r"\bNEXT YIELD\b", s) and st == "42001":
        return "engine: bug already reported", "NEXT with YIELD does not parse"
    if "unsupported" in m or ("statement boundary" in m and "CALL" in s):
        if re.match(r"^VALUE \w+ ", s):
            return "engine: documented deviation", "L26: typed VALUE definition"
        return "engine: documented deviation", m.split(": ", 1)[-1][:60]
    if re.search(r"EXISTS\s*[{(][^})]*KEEP", s):
        return "engine: parse gap", "KEEP after a graph pattern inside EXISTS"
    if st == "42001" and re.search(r'@["`]', s):
        return "engine: parse gap", "<no escape> @ before a delimited identifier"
    if re.search(r"\bVALUE \w+ ", s):
        return "engine: parse gap", "typed VALUE with a reference, record or closed type"
    return "unsorted", m[:70]


def main():
    rows = {}
    for line in open(sys.argv[1]):
        r = json.loads(line)
        rows.setdefault(r["sentence"], r)
    by = collections.defaultdict(lambda: collections.defaultdict(list))
    for r in rows.values():
        b, why = bucket(r)
        by[b][why].append(r["sentence"])
    total = len(rows)
    print(f"{total} distinct sentences")
    for b in sorted(by, key=lambda b: -sum(len(v) for v in by[b].values())):
        n = sum(len(v) for v in by[b].values())
        print(f"{n:6}  {100 * n / total:5.1f}%  {b}")
        if b == "accepted":
            continue
        for why, v in sorted(by[b].items(), key=lambda kv: -len(kv[1])):
            print(f"          {len(v):5}  {why}\n                 e.g. {min(v, key=len)[:100]!r}")
    count = lambda b: sum(len(v) for v in by[b].values())
    valid = total - count("ours: invalid sentence") - count("engine: documented deviation") - count("environment")
    handled = count("accepted") + count("dynamic: raised as it should")
    print(f"valid, outside documented deviations and the environment: {handled} of {valid} handled ({100 * handled / valid:.0f}%)")


if __name__ == "__main__":
    main()
