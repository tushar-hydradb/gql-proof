iso := "https://standards.iso.org/iso-iec/39075/ed-1/en"
pdf := "papers/iso/ISO_IEC_39075_2024.pdf"
cor1 := "papers/iso/ISO_IEC_39075;2024_Cor_1;2026_en.pdf"
python := ".venv-pdf/bin/python"

# download the iso artifacts into grammar/, skipping ones already there
fetch:
    #!/usr/bin/env bash
    set -euo pipefail
    for f in ".bnf.xml" ".bnf.txt" "-features.xml" "-conditions.xml" "-implementation-defined.xml" "-implementation-dependent.xml"; do
        out="grammar/ISO_IEC_39075(en)$f"
        [ -f "$out" ] || curl -fsSL -o "$out" "{{iso}}/ISO_IEC_39075(en)$f"
    done

# python tooling for the pdf
venv:
    uv venv .venv-pdf
    uv pip install --python {{python}} pypdfium2 pdfplumber lark pageindex

# read cor 1 into grammar/corrigendum.json and apply its grammar edits to the 2024 bnf.xml,
# which iso has not updated
grammar: fetch
    #!/usr/bin/env bash
    set -euo pipefail
    for f in "{{pdf}}" "{{cor1}}"; do
        [ -f "$f" ] || { echo "the iso pdfs are not downloadable, put your copy at $f" >&2; exit 1; }
    done
    {{python}} -I tools/corrigendum.py "{{cor1}}" "{{pdf}}" grammar

# extract the conformance rules, as cor 1 corrects them, into grammar/conformance.json
features: grammar
    {{python}} -I tools/conformance.py "{{pdf}}" grammar grammar/conformance.json

test: features
    cargo test --release

# a throwaway neo4j with an empty database on localhost:17474
neo4j-up:
    #!/usr/bin/env bash
    set -euo pipefail
    docker ps --format '{{{{.Names}}' | grep -qx gqlproof-neo4j || docker run -d --name gqlproof-neo4j -p 17474:7474 -p 17687:7687 -e NEO4J_AUTH=none neo4j:latest >/dev/null
    until curl -sf localhost:17474 >/dev/null; do sleep 2; done

neo4j-down:
    docker rm -f gqlproof-neo4j

# short sentences for a claim, run on neo4j with EXPLAIN, then the report
neo4j claim="claims/neo4j.claim": neo4j-up
    mkdir -p target/engines
    cargo run --release -q -- purdom --short --claim {{claim}} --format jsonl > target/engines/neo4j-sentences.jsonl
    python3 -I tools/engines/neo4j.py target/engines/neo4j-sentences.jsonl target/engines/neo4j-results.jsonl
    python3 -I tools/engines/report.py target/engines/neo4j-results.jsonl

# short sentences for a claim, run on the gql engine in a turbolay worktree, then the report
turbolay worktree claim="claims/turbolay.claim":
    #!/usr/bin/env bash
    set -euo pipefail
    grep -q '^serde_json' {{worktree}}/crates/cypher-engine/Cargo.toml || { echo "add serde_json = { workspace = true } to [dev-dependencies] of {{worktree}}/crates/cypher-engine/Cargo.toml" >&2; exit 1; }
    mkdir -p target/engines
    cargo run --release -q -- purdom --short --claim {{claim}} --format jsonl > target/engines/turbolay-sentences.jsonl
    cp tools/engines/turbolay_probe.rs {{worktree}}/crates/cypher-engine/tests/zz_gql_proof.rs
    out=$PWD/target/engines
    (cd {{worktree}} && GQL_PROOF_IN=$out/turbolay-sentences.jsonl GQL_PROOF_OUT=$out/turbolay-results.jsonl cargo test --release -q -p hydradb-cypher-engine --test zz_gql_proof >/dev/null)
    python3 -I tools/engines/report.py target/engines/turbolay-results.jsonl
