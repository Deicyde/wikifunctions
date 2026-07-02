#!/usr/bin/env python3
"""Round-trip properties for the A1 prototype. Run from the repo root:

    python3 roundtrip/test_roundtrip.py

Exits non-zero if any property fails. Checks, per deployed program:

  P1  Imp idempotence   translate(render(translate(src))) == translate(src)
      The honest round-trip: the Imp fixed point is stable even across the
      for->while desugaring, so it holds for BOTH programs.

  P2  Python fidelity    ast(render(translate(src))) == ast(src)
      Byte-for-byte (AST-equal) reconstruction. Holds for genuine while-loop
      programs (Z13701); for a desugared `for` loop (Z13667) it is expected to
      differ (while-form vs for-form) — asserted as such, not silently.

  P3  Kernel certificate  `lake env lean` accepts the generated *Check.lean,
      i.e. the translated Imp is definitionally equal to the committed
      hand-transcription (retires the D9 transcription-trust gap).
"""
from __future__ import annotations

import ast
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import py2imp  # noqa: E402

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
PROGRAMS = ["Z13701", "Z13667"]
DESUGARED = {"Z13667"}  # uses `for`, so P2 is expected to differ (documented)


def astdump(src: str) -> str:
    return ast.dump(ast.parse(src))


def main() -> int:
    fails: list[str] = []

    for name in PROGRAMS:
        src = (HERE / "programs" / f"{name}.py").read_text()
        imp = py2imp.translate(src)
        reprinted = py2imp.render_py(imp)

        # P1 — Imp idempotence (both programs)
        if py2imp.translate(reprinted) != imp:
            fails.append(f"{name}: P1 Imp round-trip is not idempotent")
        else:
            print(f"[P1] {name}: translate ∘ render ∘ translate = translate  ✓")

        # P2 — Python fidelity
        same = astdump(reprinted) == astdump(src)
        if name in DESUGARED:
            if same:
                fails.append(f"{name}: P2 expected the for->while desugaring to differ, but it matched")
            else:
                print(f"[P2] {name}: reconstructs the while-form (for->while desugaring, as documented)  ✓")
        else:
            if same:
                print(f"[P2] {name}: render ∘ translate reproduces the source AST byte-for-byte  ✓")
            else:
                fails.append(f"{name}: P2 reconstruction is not AST-equal to the source")

    # P3 — kernel certificate for all programs
    for name in PROGRAMS:
        subprocess.run([sys.executable, str(HERE / "py2imp.py"), "check",
                        str(HERE / "programs" / f"{name}.py")], check=True,
                       stdout=subprocess.DEVNULL)
        r = subprocess.run(["lake", "env", "lean", f"roundtrip/generated/{name}Check.lean"],
                           cwd=REPO, capture_output=True, text=True)
        if r.returncode == 0:
            print(f"[P3] {name}: Lean kernel certifies translated Imp = committed transcription  ✓")
        else:
            fails.append(f"{name}: P3 kernel check failed:\n{r.stdout}\n{r.stderr}")

    print()
    if fails:
        print("FAILED:")
        for f in fails:
            print("  -", f)
        return 1
    print(f"All properties passed for {', '.join(PROGRAMS)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
