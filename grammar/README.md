# grammar

nothing iso-owned is stored in the repo. this directory is filled locally and gitignored

`just fetch` downloads the digital artifacts published with iso/iec 39075:2024 (gql) from https://standards.iso.org/iso-iec/39075/ed-1/en/, unmodified, under the iso customer licence:
- `ISO_IEC_39075(en).bnf.xml` is the 2024 grammar
- `ISO_IEC_39075(en).bnf.txt` is the same grammar as readable bnf
- `ISO_IEC_39075(en)-features.xml` is the 228 optional feature ids and names
- `ISO_IEC_39075(en)-conditions.xml` is the gqlstatus classes and subclasses
- `ISO_IEC_39075(en)-implementation-defined.xml` and `-implementation-dependent.xml` are the implementation-defined and -dependent elements

iso has not updated these for technical corrigendum 1:2026, so `just grammar` reads cor 1 from its pdf (`papers/iso/ISO_IEC_39075;2024_Cor_1;2026_en.pdf`) with `tools/corrigendum.py`:
- `corrigendum.json` is every cor 1 item, its instruction classified, applied or recorded
- `ISO_IEC_39075(en)+Cor1.bnf.xml` is the grammar with cor 1's grammar edits applied, the one compiled into the generator

`just features` writes `conformance.json` from the iso pdf, which cannot be downloaded and has to be at `papers/iso/ISO_IEC_39075_2024.pdf`, with cor 1's edits applied. it holds every "Without Feature" statement as a tree pattern, the implied features (table 10) and the rules on claims (24.2, 24.3, table 10's "at least one of" rows). see `tools/conformance.py`
