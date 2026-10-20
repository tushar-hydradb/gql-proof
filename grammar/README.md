# grammar

nothing iso-owned is stored in the repo. this directory is filled locally and gitignored

`just fetch` downloads the digital artifacts published with iso/iec 39075:2024 (gql) from https://standards.iso.org/iso-iec/39075/ed-1/en/, unmodified, under the iso customer licence:
- `ISO_IEC_39075(en).bnf.xml` is the grammar, compiled into the generator
- `ISO_IEC_39075(en).bnf.txt` is the same grammar as readable bnf
- `ISO_IEC_39075(en)-features.xml` is the 228 optional feature ids and names
- `ISO_IEC_39075(en)-conditions.xml` is the gqlstatus classes and subclasses
- `ISO_IEC_39075(en)-implementation-defined.xml` and `-implementation-dependent.xml` are the implementation-defined and -dependent elements

`just features` writes `conformance.json` from the iso pdf, which cannot be downloaded and has to be at `papers/iso/ISO_IEC_39075_2024.pdf`. it holds every "Without Feature" statement as a tree pattern, the implied features (table 10) and the rules on claims (24.2, 24.3). see `tools/conformance.py`
