iso := "https://standards.iso.org/iso-iec/39075/ed-1/en"
pdf := "papers/iso/ISO_IEC_39075_2024.pdf"
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
    uv pip install --python {{python}} pypdfium2 lark pageindex

# extract the conformance rules from the iso pdf into grammar/conformance.json
features: fetch
    #!/usr/bin/env bash
    set -euo pipefail
    [ -f "{{pdf}}" ] || { echo "the iso pdf is not downloadable, put your copy at {{pdf}}" >&2; exit 1; }
    {{python}} -I tools/conformance.py "{{pdf}}" grammar grammar/conformance.json

test: features
    cargo test --release
