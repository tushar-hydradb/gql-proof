# grammar

what the generator is built from. everything here is iso's or made from iso's material, so it is filled locally and gitignored. only this readme and `SHA256SUMS` are committed. how to get the pdfs is in the main readme

`just fetch` downloads the files published with iso/iec 39075:2024 from https://standards.iso.org/iso-iec/39075/ed-1/en/, unmodified, under iso's customer licence, and checks them against `SHA256SUMS`:
- `ISO_IEC_39075(en).bnf.xml` is the 2024 grammar
- `ISO_IEC_39075(en).bnf.txt` is the same grammar as readable bnf
- `ISO_IEC_39075(en)-features.xml` is the 228 optional feature ids and names
- `ISO_IEC_39075(en)-conditions.xml` is the gqlstatus classes and subclasses
- `ISO_IEC_39075(en)-implementation-defined.xml` and `-implementation-dependent.xml` are what the standard leaves to implementations

if the check fails, iso changed a file. look at what changed before updating the sums, since the tools were checked against these exact files

iso has not updated these for corrigendum 1, so `just grammar` reads cor 1 from its pdf with `tools/corrigendum.py` (it also needs the 2024 pdf, for its table of contents):
- `corrigendum.json` is every cor 1 item, what kind of edit it is, and whether it was applied or recorded
- `ISO_IEC_39075(en)+Cor1.bnf.xml` is the grammar with cor 1's grammar edits applied, the one the generator is built from

`just features` writes `conformance.json` from the 2024 pdf, with cor 1's edits applied. it holds every conformance rule as a tree pattern, which features imply which (table 10) and the rules on what a claim has to include (24.2, 24.3). see `tools/conformance.py`
