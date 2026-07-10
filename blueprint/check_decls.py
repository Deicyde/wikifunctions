#!/usr/bin/env python3
"""Compile-check every ``\\lean{...}`` declaration in the blueprint.

The old checker compared only the final identifier component against a regular-expression index,
so a misspelled namespace could still pass.  This checker generates a temporary Lean module that
imports the repository root and asks Lean to resolve every fully qualified name.

Run from any directory: ``python3 blueprint/check_decls.py``.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys
import tempfile


ROOT = pathlib.Path(__file__).resolve().parent.parent
CONTENT = ROOT / "blueprint" / "src" / "content.tex"
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.?!]*(?:\.[A-Za-z_][A-Za-z0-9_'.?!]*)*$")


def declaration_names() -> list[str]:
    content = CONTENT.read_text(encoding="utf-8")
    names: list[str] = []
    for match in re.finditer(r"\\lean\{([^}]*)\}", content):
        names.extend(name.strip() for name in match.group(1).split(",") if name.strip())
    invalid = [name for name in names if not LEAN_NAME.fullmatch(name)]
    if invalid:
        raise ValueError(f"invalid Lean declaration syntax in blueprint: {invalid}")
    return list(dict.fromkeys(names))


def main() -> int:
    names = declaration_names()
    if not names:
        print("blueprint declaration check: no \\lean names found", file=sys.stderr)
        return 1

    source = "import Wikifunctions\n\n" + "\n".join(f"#check {name}" for name in names) + "\n"
    path: pathlib.Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", suffix=".lean", prefix="wikifunctions-blueprint-",
            delete=False
        ) as handle:
            handle.write(source)
            path = pathlib.Path(handle.name)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False
        )
    finally:
        if path is not None:
            path.unlink(missing_ok=True)

    if result.returncode != 0:
        print(result.stdout, file=sys.stderr)
        print(f"blueprint declaration check failed ({len(names)} names)", file=sys.stderr)
        return result.returncode

    print(f"OK: Lean resolved all {len(names)} blueprint declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
