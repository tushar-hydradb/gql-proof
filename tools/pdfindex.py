"""Local PDF index for the papers and the ISO spec, built on PageIndex.

Indexing runs through Claude Code (`claude-code/haiku`), so documents never leave the
machine except to Claude. The index lives in `papers/.index/`, which is gitignored along
with the PDFs.

    .venv-pdf/bin/python tools/pdfindex.py index papers/iso/ISO_IEC_39075_2024.pdf
    .venv-pdf/bin/python tools/pdfindex.py list
    .venv-pdf/bin/python tools/pdfindex.py tree <doc_id>
    .venv-pdf/bin/python tools/pdfindex.py pages <doc_id> 120-123
"""

import argparse
import json
from pathlib import Path

from pageindex import PageIndexClient

STORE = Path(__file__).resolve().parent.parent / "papers" / ".index"


def client() -> PageIndexClient:
    return PageIndexClient(index_model="claude-code/haiku", storage_path=str(STORE))


def print_tree(nodes, depth=0):
    for node in nodes:
        start, end = node.get("start_index"), node.get("end_index")
        pages = f"p{start}" if start == end else f"p{start}-{end}"
        print(f"{'  ' * depth}{node.get('title', '?')}  [{pages}]  {node.get('node_id', '')}")
        print_tree(node.get("nodes") or [], depth + 1)


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("index").add_argument("pdf")
    sub.add_parser("list")
    sub.add_parser("tree").add_argument("doc_id")
    pages = sub.add_parser("pages")
    pages.add_argument("doc_id")
    pages.add_argument("spec", help="'5-7', '3,8' or '12'")
    args = parser.parse_args()

    c = client()
    if args.cmd == "index":
        print(json.dumps(c.submit_document(args.pdf), indent=2))
    elif args.cmd == "list":
        for doc in c.list_documents().get("documents", []):
            print(doc.get("id") or doc.get("doc_id"), doc.get("name"), doc.get("status"))
    elif args.cmd == "tree":
        print_tree(c.get_document_structure(args.doc_id))
    elif args.cmd == "pages":
        for page in c.get_page_content(args.doc_id, args.spec):
            print(f"--- page {page.get('page_index')} ---")
            print(page.get("markdown") or page.get("text") or "")


if __name__ == "__main__":
    main()
