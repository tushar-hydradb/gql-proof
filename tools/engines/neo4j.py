"""Runs gql-proof sentences (jsonl with a "sentence" field) against neo4j's http endpoint, one
request each so one error cannot abort the rest, and writes one result line per sentence:
{sentence, outcome, status, message}. outcome is ok or refused.

    python3 -I tools/engines/neo4j.py sentences.jsonl results.jsonl [--url URL] [--run]

By default each sentence is prefixed with EXPLAIN, which parses and plans it without running.
--run executes it instead, against whatever the database holds.
"""

import argparse
import json
import urllib.request


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sentences")
    ap.add_argument("results")
    ap.add_argument("--url", default="http://localhost:17474/db/neo4j/tx/commit")
    ap.add_argument("--run", action="store_true", help="execute instead of EXPLAIN")
    args = ap.parse_args()
    with open(args.sentences) as src, open(args.results, "w") as out:
        for line in src:
            sentence = json.loads(line)["sentence"]
            statement = sentence if args.run else "EXPLAIN " + sentence
            body = json.dumps({"statements": [{"statement": statement}]}).encode()
            request = urllib.request.Request(args.url, body, {"Content-Type": "application/json"})
            response = json.load(urllib.request.urlopen(request))
            if response["errors"]:
                error = response["errors"][0]
                row = {
                    "sentence": sentence,
                    "outcome": "refused",
                    "status": error["code"].rsplit(".", 1)[-1],
                    "message": error["message"].split("\n")[0],
                }
            else:
                rows = len(response["results"][0]["data"])
                row = {"sentence": sentence, "outcome": "ok", "status": "", "message": f"{rows} rows"}
            out.write(json.dumps(row, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()
