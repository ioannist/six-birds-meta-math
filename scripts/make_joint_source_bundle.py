#!/usr/bin/env python3
"""Create and check a source-only RH/Navier/PvNP campaign bundle.

The four Lean projects retain their sibling layout so Lake's local path
dependencies resolve without a custom LEAN_PATH. Standard Git packages are
fetched from the pinned Lake manifests when the verifier runs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path


REPOSITORIES = (
    "six-birds-needles",
    "six-birds-duality-confinement",
    "six-birds-hiddenness",
    "six-birds-meta-math",
)
PAPERS = {
    "six-birds-needles": ("needles_xi", "needles_aor", "needles_emergence", "needles_ns"),
    "six-birds-duality-confinement": ("duality_confinement", "rh"),
    "six-birds-hiddenness": ("hiddenness", "pvnp"),
    "six-birds-meta-math": ("meta_math",),
}
OMIT_DIRS = {".git", ".lake", "build", "build.bak", "submission", "__pycache__"}
OMIT_SUFFIXES = {".olean", ".ilean", ".c", ".o", ".aux", ".log", ".fls", ".fdb_latexmk", ".synctex.gz", ".pdf"}
VERIFY_SCRIPT = """#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum --quiet --check SHA256SUMS
python3 - <<'PY'
import json, pathlib, tomllib
root=pathlib.Path.cwd()
for lakefile in root.rglob('lakefile.toml'):
    if '.lake' in lakefile.parts:
        continue
    d=tomllib.loads(lakefile.read_text())
    for item in d.get('require',[]):
        if 'path' in item:
            q=(lakefile.parent/item['path']).resolve(strict=True)
            if root not in q.parents:
                raise SystemExit(f'local dependency escapes bundle: {q}')
for manifest in root.rglob('lake-manifest.json'):
    if '.lake' in manifest.parts:
        continue
    for item in json.loads(manifest.read_text()).get('packages',[]):
        if item.get('type') == 'path':
            q=(manifest.parent/item['dir']).resolve(strict=True)
            if root not in q.parents:
                raise SystemExit(f'locked local dependency escapes bundle: {q}')
print('Local Lake paths resolve inside source bundle.')
PY
(cd six-birds-meta-math/lean && lake build SixBirdsMetaMath.RHNavierPvNP)
"""
README = """# RH–Navier–PvNP source bundle

This directory contains the four maintained Lean source projects, their
vendored local Foundations dependencies, and the nine editable paper source
trees. It contains no compiled project artifacts or generated paper PDFs.

Run `./verify.sh` here. It verifies the source hashes, checks that local Lake
dependencies resolve inside this bundle, and builds the maintained joint
`SixBirdsMetaMath.RHNavierPvNP` target, which imports the retained
RH--Navier bridge and the concrete SAT construction. A matching Lean
toolchain and network access for pinned packages are needed unless
those packages are already cached. The four project directories must
remain siblings.

`SHA256SUMS` is the authoritative file inventory. This is a source snapshot of
the local worktrees, not an identification by their current Git commits.
"""


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def keep(path: Path) -> bool:
    return not any(path.name.endswith(ext) for ext in OMIT_SUFFIXES)


def copy_tree(source: Path, target: Path) -> None:
    if not source.is_dir():
        raise FileNotFoundError(source)
    for current, dirs, files in os.walk(source):
        dirs[:] = sorted(d for d in dirs if d not in OMIT_DIRS)
        relative = Path(current).relative_to(source)
        for name in sorted(files):
            old = Path(current) / name
            if not keep(old):
                continue
            new = target / relative / name
            new.parent.mkdir(parents=True, exist_ok=True)
            # Resolve file symlinks so bibliography/assets are self-contained.
            shutil.copy2(old, new, follow_symlinks=True)


def source_paths(bundle: Path) -> list[Path]:
    return sorted(
        (p for p in bundle.rglob("*") if p.is_file() and p.name != "SHA256SUMS"),
        key=lambda p: p.relative_to(bundle).as_posix(),
    )


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify_local_paths(bundle: Path) -> None:
    root = bundle.resolve()
    for name in REPOSITORIES:
        if not (root / name / "lean" / "lakefile.toml").is_file():
            raise FileNotFoundError(root / name / "lean" / "lakefile.toml")
    for lakefile in root.rglob("lakefile.toml"):
        if ".lake" in lakefile.parts:
            continue
        data = tomllib.loads(lakefile.read_text())
        for requirement in data.get("require", []):
            if "path" not in requirement:
                continue
            target = (lakefile.parent / requirement["path"]).resolve(strict=True)
            if root not in target.parents:
                raise ValueError(f"dependency escapes bundle: {lakefile}: {target}")
    for manifest in root.rglob("lake-manifest.json"):
        if ".lake" in manifest.parts:
            continue
        for requirement in json.loads(manifest.read_text()).get("packages", []):
            if requirement.get("type") != "path":
                continue
            target = (manifest.parent / requirement["dir"]).resolve(strict=True)
            if root not in target.parents:
                raise ValueError(f"locked dependency escapes bundle: {manifest}: {target}")
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"external symlink in bundle: {path}")
        if path.is_file() and path.name.endswith((".olean", ".ilean")):
            raise ValueError(f"compiled project output in bundle: {path}")


def create(output: Path) -> None:
    if output.exists():
        raise FileExistsError(output)
    root = repo_root()
    with tempfile.TemporaryDirectory(prefix="joint-source-bundle-", dir=output.parent) as temporary:
        bundle = Path(temporary) / output.name
        bundle.mkdir()
        for name in REPOSITORIES:
            source = root / name
            dest = bundle / name
            copy_tree(source / "lean", dest / "lean")
            copy_tree(source / "vendor", dest / "vendor")
            for legal_name in ("LICENSE", "LICENSE.md", "LICENSE.txt",
                               "COPYING", "NOTICE"):
                legal_file = source / legal_name
                if legal_file.is_file():
                    shutil.copy2(legal_file, dest / legal_name,
                                 follow_symlinks=True)
            for paper in PAPERS[name]:
                copy_tree(source / "paper" / paper, dest / "paper" / paper)
            shared_bib = source / "paper" / "references.bib"
            if shared_bib.is_file():
                (dest / "paper").mkdir(parents=True, exist_ok=True)
                shutil.copy2(shared_bib, dest / "paper" / "references.bib",
                             follow_symlinks=True)
        (bundle / "verify.sh").write_text(VERIFY_SCRIPT)
        (bundle / "verify.sh").chmod(0o755)
        (bundle / "README.md").write_text(README)
        verify_local_paths(bundle)
        summary = {
            "repositories": REPOSITORIES,
            "papers": PAPERS,
            "files": len(source_paths(bundle)) + 1,
            "joint_target": "SixBirdsMetaMath.RHNavierPvNP",
        }
        (bundle / "BUNDLE.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
        files = source_paths(bundle)
        checksums = "".join(f"{digest(p)}  {p.relative_to(bundle).as_posix()}\n" for p in files)
        (bundle / "SHA256SUMS").write_text(checksums)
        summary["checksum_file_sha256"] = digest(bundle / "SHA256SUMS")
        bundle.rename(output)
    print(json.dumps(summary, indent=2, sort_keys=True))


def check(bundle: Path) -> None:
    verify_local_paths(bundle)
    result = subprocess.run(["sha256sum", "--check", "SHA256SUMS"], cwd=bundle,
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or "bundle checksum check failed")
    print(f"Source hashes and Lake dependency paths pass: {bundle}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("create", "check"):
        option = commands.add_parser(command)
        option.add_argument("directory", type=Path)
    args = parser.parse_args()
    if args.command == "create":
        create(args.directory.resolve())
    else:
        check(args.directory.resolve())


if __name__ == "__main__":
    try:
        main()
    except (FileNotFoundError, FileExistsError, ValueError, RuntimeError) as exc:
        print(f"bundle error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
