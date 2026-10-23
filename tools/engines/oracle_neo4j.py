"""Runs the witness oracle's records against neo4j's http endpoint: for each record of the
witness tier with a cypher setup, empties the graph, runs the setup, runs the sentence, and
compares what came back with what the record expects. Writes one result line per record:
{sentence, verdict, detail}. verdict is agree, disagree, refused (the sentence has no
neo4j parse or plan) or unloadable (the setup failed).

    python3 -I tools/engines/oracle_neo4j.py oracle.jsonl results.jsonl [--url URL]

Elements come back as their property maps in the http row format, so they are compared by
the `_id` property the oracle gives every element; a path comes back as a list of them.
"""

import argparse
import json
import urllib.request


def run(url, statement):
    body = json.dumps({"statements": [{"statement": statement}]}).encode()
    request = urllib.request.Request(url, body, {"Content-Type": "application/json"})
    response = json.load(urllib.request.urlopen(request))
    if response["errors"]:
        error = response["errors"][0]
        return None, error["code"].rsplit(".", 1)[-1] + ": " + error["message"].split("\n")[0]
    result = response["results"][0]
    return {"columns": result["columns"], "rows": [d["row"] for d in result["data"]]}, None


def matches(expected, got):
    """Whether a returned value is the expected binding, elements by `_id`."""
    kind, value = expected["kind"], expected.get("value")
    if kind == "Null":
        return got is None
    if kind in ("Node", "Edge"):
        return isinstance(got, dict) and got.get("_id") == value
    if kind == "Path":
        # The row format gives a path as the property maps of its elements in order.
        if not isinstance(got, list) or len(got) != len(value):
            return False
        return all(isinstance(g, dict) and g.get("_id") == v for g, v in zip(got, value))
    if kind == "List":
        return isinstance(got, list) and len(got) == len(value) and all(
            matches(e, g) for e, g in zip(value, got)
        )
    return False


def judge(record, result):
    expect = record["expect"]
    rows = result["rows"]
    if expect.get("rows") == 0:
        return ("agree", f"{len(rows)} rows") if not rows else ("disagree", f"expected no rows, got {len(rows)}")
    if not expect["result"]:
        return "agree", "completed, no result expected"
    row = expect.get("row")
    if row is None:
        return "agree", f"completed, {len(rows)} rows, no row claimed"
    columns = result["columns"]
    for got in rows:
        values = dict(zip(columns, got))
        if all(col in values and matches(bound, values[col]) for col, bound in row.items()):
            return "agree", f"the witness row is among {len(rows)}"
    return "disagree", f"the witness row is not among {len(rows)} rows: {rows[:3]!r}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("oracle")
    ap.add_argument("results")
    ap.add_argument("--url", default="http://localhost:17474/db/neo4j/tx/commit")
    args = ap.parse_args()
    counts = {}
    with open(args.oracle) as src, open(args.results, "w") as out:
        for line in src:
            record = json.loads(line)
            expect = record.get("expect")
            setup = record.get("setup", {})
            if not expect or expect.get("tier") != "witness" or setup.get("cypher") is None:
                continue
            sentence = record["sentence"]
            _, error = run(args.url, "MATCH (n) DETACH DELETE n")
            if error:
                raise SystemExit(f"could not empty the graph: {error}")
            verdict, detail = None, None
            for statement in setup["cypher"]:
                _, error = run(args.url, statement)
                if error:
                    verdict, detail = "unloadable", error
                    break
            if verdict is None:
                result, error = run(args.url, sentence)
                if error:
                    verdict, detail = "refused", error
                else:
                    verdict, detail = judge(record, result)
            counts[verdict] = counts.get(verdict, 0) + 1
            out.write(json.dumps({"sentence": sentence, "verdict": verdict, "detail": detail}, ensure_ascii=False) + "\n")
    for verdict, n in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"{n:6}  {verdict}")


if __name__ == "__main__":
    main()
