"""Measures how the context engine grows: runs `gql-proof context` over parts of the grammar
and caps on variables, smallest first, and prints how each measure scales.

    python3 tools/context_sweep.py run [--starts ...] [--slots 1 2 3] [--phases fixpoint emit]
    python3 tools/context_sweep.py report

`run` appends one row per run to target/context/sweep.csv as the run ends (start, rule, slots,
references, phase, labels, pushes, partials at one position, emitted productions, ms per
phase, peak memory), and prints it. Nothing is cut off: the smaller cases come first, so the
curve builds up from short runs and a long one shows where growth starts. `report` reads the
csv and prints, per part of the grammar, every measure against the cap, with the factor from
the cap before.
"""

import argparse
import csv
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / "target" / "release" / "gql-proof"
OUT = ROOT / "target" / "context" / "sweep.csv"
STARTS = ["value expression", "graph pattern", "simple linear query statement", "GQL-program"]
FIELDS = [
    "start",
    "rule",
    "slots",
    "references",
    "phase",
    "labels",
    "pushes",
    "partials_max",
    "emitted",
    "fixpoint_ms",
    "emit_ms",
    "peak_mb",
    "status",
]


def run_one(start, rule, slots, references, phase):
    with tempfile.NamedTemporaryFile(suffix=".json") as stats:
        cmd = [
            "/usr/bin/time",
            "-l",
            str(BINARY),
            "context",
            "--start",
            start,
            "--rule",
            rule,
            "--slots",
            str(slots),
            "--references",
            str(references),
            "--phase",
            phase,
            "--stats",
            stats.name,
            "--top",
            "5",
        ]
        done = subprocess.run(cmd, capture_output=True, text=True)
        peak = re.search(r"(\d+)\s+maximum resident set size", done.stderr)
        row = {
            "start": start,
            "rule": rule,
            "slots": slots,
            "references": references,
            "phase": phase,
            "peak_mb": round(int(peak.group(1)) / 2**20, 1) if peak else "",
            "status": "ok" if done.returncode == 0 else f"exit {done.returncode}",
        }
        if done.returncode == 0:
            s = json.loads(Path(stats.name).read_text())
            row["labels"] = sum(s["labels"].values())
            row["pushes"] = sum(d["pushes"] for d in s["defs"].values())
            row["partials_max"] = max((p["partials_max"] for p in s["prods"].values()), default=0)
            row["emitted"] = s["emit"]["productions"]
            row["fixpoint_ms"] = round(s["phases"].get("fixpoint", 0) / 1e6, 1)
            row["emit_ms"] = round(s["phases"].get("emit", 0) / 1e6, 1)
        else:
            tail = done.stderr.strip().splitlines()[-3:]
            print("  " + "\n  ".join(tail), file=sys.stderr)
        return row


def run(args):
    OUT.parent.mkdir(parents=True, exist_ok=True)
    new = not OUT.exists()
    with OUT.open("a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        if new:
            w.writeheader()
        for slots in args.slots:
            for start in args.starts:
                for phase in args.phases:
                    references = min(slots, args.references) if args.references else slots
                    row = run_one(start, args.rule, slots, references, phase)
                    w.writerow(row)
                    f.flush()
                    print(", ".join(f"{k}={row.get(k, '')}" for k in FIELDS), flush=True)


def report(_args):
    rows = list(csv.DictReader(OUT.open()))
    measures = ["labels", "pushes", "partials_max", "emitted", "fixpoint_ms", "emit_ms", "peak_mb"]
    keys = sorted({(r["start"], r["rule"], r["phase"]) for r in rows})
    for start, rule, phase in keys:
        group = [r for r in rows if (r["start"], r["rule"], r["phase"]) == (start, rule, phase)]
        group.sort(key=lambda r: (int(r["slots"]), int(r["references"])))
        print(f"\n{start} ({rule}, {phase})")
        print("  slots refs " + " ".join(f"{m:>16}" for m in measures))
        before = None
        for r in group:
            cells = []
            for m in measures:
                v = r.get(m) or ""
                factor = ""
                if before and v and before.get(m) and float(before[m]) > 0:
                    factor = f" x{float(v) / float(before[m]):.1f}"
                cells.append(f"{v + factor:>16}")
            status = "" if r["status"] == "ok" else f"  ({r['status']})"
            print(f"  {r['slots']:>5} {r['references']:>4} " + " ".join(cells) + status)
            before = r


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--starts", nargs="+", default=STARTS)
    r.add_argument("--rule", default="scope")
    r.add_argument("--slots", nargs="+", type=int, default=[1, 2, 3, 4])
    r.add_argument("--references", type=int, help="cap references at this (default: slots)")
    r.add_argument("--phases", nargs="+", default=["fixpoint", "emit"])
    sub.add_parser("report")
    args = p.parse_args()
    {"run": run, "report": report}[args.cmd](args)


if __name__ == "__main__":
    main()
