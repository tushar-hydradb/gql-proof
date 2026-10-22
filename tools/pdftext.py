"""The text of a pdf, page by page, each page under a `--- page N ---` line, as
`tools/inventory/` reads it. Used on the standard's pdf; the output is licensed text and
goes to iso-text/, which is gitignored.

    .venv-pdf/bin/python -I tools/pdftext.py <pdf> <out.txt>
"""

import sys

import pypdfium2 as pdfium

src, dst = sys.argv[1], sys.argv[2]
pdf = pdfium.PdfDocument(src)
with open(dst, "w", encoding="utf8") as out:
    for i in range(len(pdf)):
        out.write(f"--- page {i + 1} ---\n")
        out.write(pdf[i].get_textpage().get_text_range())
        out.write("\n")
