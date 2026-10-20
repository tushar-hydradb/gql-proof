"""Summarises an engine run (jsonl lines {sentence, outcome, status, message}): counts by
outcome and status, the tokens parses stop at, and the shortest sentence per kind of failure.

    python3 -I tools/engines/report.py results.jsonl
"""

import collections
import json
import re
import sys


def kind(row):
    message = row["message"]
    stop = re.search(r"Invalid input '([^']*)'|mismatched input '([^']*)'", message)
    if stop:
        return f"{row['status']} parse stops at '{stop.group(1) or stop.group(2)}'"
    return f"{row['status']} {re.sub(r'[`(].*', '', message)[:70].strip()}"


def main():
    rows = [json.loads(line) for line in open(sys.argv[1])]
    print(f"{len(rows)} sentences")
    for (outcome, status), n in collections.Counter((r["outcome"], r["status"]) for r in rows).most_common():
        print(f"  {n:5} {outcome} {status}")
    shortest = {}
    counts = collections.Counter()
    for r in rows:
        if r["outcome"] == "ok":
            continue
        k = kind(r)
        counts[k] += 1
        if k not in shortest or len(r["sentence"]) < len(shortest[k]):
            shortest[k] = r["sentence"]
    print("failures by kind, with the shortest sentence:")
    for k, n in counts.most_common(30):
        print(f"  {n:5} {k}\n        {shortest[k][:150]}")


if __name__ == "__main__":
    main()
