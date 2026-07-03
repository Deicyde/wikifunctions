#!/usr/bin/env python3
"""Enumerate the value primitives Wikifunctions actually supports.

Two groups, so the blueprint's `Val` can be seen as a subset of a known, fixed menu
rather than an ad-hoc trio:

  * BUILT-IN types -- the complete, authoritative set is the function-schemata
    `data/CANONICAL/*.yaml` files (the types the platform enforces natively). We list
    them with their live labels and flag the atomic *value* types among them. Note:
    NO number type is built in.

  * NUMERIC community types -- naturals/integers/rationals/floats are wiki content
    built on top of Z6 (a natural is a record wrapping a Z6 digit-string), not
    platform built-ins. These are curated (community types are open-ended).

`Val`'s three carriers are marked. Usage: python3 blueprint/list_primitives.py
"""
from __future__ import annotations

import json
import subprocess
import time

SCHEMATA_TREE = ("https://gitlab.wikimedia.org/api/v4/projects/"
                 "repos%2Fabstract-wiki%2Fwikifunctions%2Ffunction-schemata/"
                 "repository/tree?path=data/CANONICAL&per_page=100")
API = "https://www.wikifunctions.org/w/api.php"

# The atomic *value* types among the built-ins (the rest are structural machinery:
# Z1-Z4 object/type, Z7/Z8 call/function, Z14-Z18 impl/args, Z22 result, Z39, ...).
BUILTIN_VALUE = {"Z6", "Z40", "Z86", "Z80", "Z21", "Z23", "Z60", "Z61", "Z6040", "Z5"}
# Numeric carriers -- community types, NOT built-in.
NUMERIC = ["Z13518", "Z16683", "Z19677", "Z20838"]
VAL = {"Z40", "Z13518", "Z19677"}   # what the Lean `Val` currently covers


def _curl(url: str) -> str:
    for i in range(4):
        out = subprocess.run(["curl", "-sS", "--retry", "2", "--max-time", "40", url],
                             capture_output=True, text=True).stdout
        if out.strip():
            return out
        time.sleep(1.2 * (i + 1))
    return ""


def builtins() -> list[str]:
    d = json.loads(_curl(SCHEMATA_TREE))
    zs = [f["name"][:-5] for f in d if f["name"].endswith(".yaml") and f["name"][1:2].isdigit()]
    return sorted(zs, key=lambda z: int(z[1:]))


def labels(zids: list[str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for i in range(0, len(zids), 8):
        raw = _curl(f"{API}?action=wikilambda_fetch&format=json&zids={'|'.join(zids[i:i+8])}")
        for z, payload in (json.loads(raw) if raw else {}).items():
            try:
                lbls = json.loads(payload["wikilambda_fetch"])["Z2K3"]["Z12K1"]
                out[z] = next((m["Z11K2"] for m in lbls if isinstance(m, dict)
                               and m.get("Z11K1") == "Z1002"), "?")
            except Exception:
                out[z] = "?"
    return out


def main() -> int:
    bi = builtins()
    lab = labels(bi + NUMERIC)
    mark = lambda z: "  <- Val" if z in VAL else ("  (value)" if z in BUILTIN_VALUE else "")
    print(f"=== BUILT-IN types (function-schemata, {len(bi)}) ===")
    for z in bi:
        print(f"  {z:6} {lab.get(z,'?'):26}{mark(z)}")
    print("\n=== NUMERIC types (community, built on Z6 -- none is built-in) ===")
    for z in NUMERIC:
        print(f"  {z:8} {lab.get(z,'?'):24}{'  <- Val' if z in VAL else ''}")
    print("\nVal covers: " + ", ".join(f"{z} ({lab.get(z,'?')})" for z in sorted(VAL)))
    print("Built-in atomic VALUE types: " + ", ".join(sorted(BUILTIN_VALUE, key=lambda z: int(z[1:]))))
    print("Note: no built-in number type; naturals/integers/rationals/floats are community types.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
