#!/usr/bin/env python3
"""Synchronize the editable metatheory manuscript with its standalone copies.

The modular paper tree is authoritative. Generated files are atomically
replaced so a public copy with another hard link cannot mutate its peer.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
NAME = "Tsiokos_2026_Three_Conditional_Clay_Problem_Closures_A_Shared_Gaussian_Observation_and_a_Common_Vocabulary.tex"


def replace(path: Path, data: bytes) -> None:
    if path.exists() and path.read_bytes() == data:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temp = Path(handle.name)
        handle.write(data)
    try:
        temp.chmod(0o644)
        os.replace(temp, path)
    finally:
        temp.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--public-dir", type=Path)
    args = parser.parse_args()
    if args.public_dir and not args.public_dir.is_dir():
        parser.error("--public-dir must exist")

    paper = ROOT / "paper/meta_math"
    if args.build:
        subprocess.run(
            ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
             "-outdir=build", "main.tex"], cwd=paper, check=True,
        )
    bbl = paper / "build/main.bbl"
    pdf = paper / "build/main.pdf"
    if not bbl.is_file() or not pdf.is_file():
        parser.error("build/main.bbl or build/main.pdf missing; use --build")
    expanded = subprocess.run(
        ["latexpand", "--expand-bbl", "build/main.bbl", "main.tex"],
        cwd=paper, check=True, stdout=subprocess.PIPE,
    ).stdout
    expanded = b"\n".join(line.rstrip() for line in expanded.splitlines()) + b"\n"
    source = (
        "% Generated from paper/meta_math/main.tex by scripts/sync_meta_math_paper.py.\n"
        "% Edit modular sources and regenerate this copy.\n"
    ).encode() + expanded
    targets = [
        (paper / "build/main_flat.tex", source),
        (ROOT / NAME, source),
        (ROOT / NAME.replace(".tex", ".pdf"), pdf.read_bytes()),
    ]
    if args.public_dir:
        targets.append((args.public_dir / NAME, source))
        targets.append((args.public_dir / NAME.replace(".tex", ".pdf"),
                        pdf.read_bytes()))
    stale = [str(path) for path, data in targets
             if not path.exists() or path.read_bytes() != data]
    if args.check:
        if stale:
            print("Stale generated files:\n" + "\n".join(stale))
            return 1
    else:
        for path, data in targets:
            replace(path, data)
    print(("Checked" if args.check else "Synchronized")
          + f" metatheory: {len(targets)} artifacts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
