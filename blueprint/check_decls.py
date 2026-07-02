#!/usr/bin/env python3
"""Verify every \\lean{...} declaration named in the blueprint exists in the Lean sources.

Heuristic but strict: for each declaration named in a \\lean{} macro in
blueprint/src/content.tex, strip the namespace and confirm the base identifier is
introduced by a def/theorem/lemma/abbrev/inductive/instance in some .lean file.
Exits non-zero (listing every miss) if any name is unaccounted for.

Run from the repo root:  python3 blueprint/check_decls.py
"""
import re, sys, pathlib

root = pathlib.Path(__file__).resolve().parent.parent
content = (root / "blueprint/src/content.tex").read_text()

# collect declaration names from \lean{a, b, c}
names = []
for m in re.finditer(r"\\lean\{([^}]*)\}", content):
    names += [n.strip() for n in m.group(1).split(",") if n.strip()]

# index every declared identifier across the Lean sources
decl_re = re.compile(
    r"^\s*(?:noncomputable\s+|protected\s+|private\s+)*"
    r"(?:def|theorem|lemma|abbrev|inductive|structure|instance)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
declared = set()
for lean in root.rglob("*.lean"):
    if ".lake" in lean.parts or ".blueprint-venv" in lean.parts:
        continue
    for line in lean.read_text().splitlines():
        mm = decl_re.match(line)
        if mm:
            base = mm.group(1).split(".")[-1]   # strip any dotted prefix
            declared.add(base)

missing = []
for full in names:
    base = full.split(".")[-1]
    if base not in declared:
        missing.append(full)

print(f"blueprint \\lean names: {len(names)}  |  distinct declared idents: {len(declared)}")
if missing:
    print(f"MISSING ({len(missing)}):")
    for m in missing:
        print(f"  - {m}")
    sys.exit(1)
print("OK: every \\lean declaration in the blueprint resolves to a Lean source declaration.")
