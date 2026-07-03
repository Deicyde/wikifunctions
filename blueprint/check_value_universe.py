#!/usr/bin/env python3
"""Verify that the blueprint's `Val` universe is COMPLETE for the modelled fragment.

`Val` (Wikifunctions/Core.lean, WikifunctionsEval.lean) has three constructors:
nat (Z13518), bool (Z40), rational (Z19677). The blueprint claims those are exactly
the value types the six modelled composites and their eleven leaves use. This script
checks that claim against ground truth: it fetches each function's formal `Z8`
signature from the live API and collects every argument type (Z8K1 -> Z17 -> Z17K1)
and return type (Z8K2). If the closure is a subset of Val, the claim holds; any type
outside Val is a gap and the script exits non-zero.

The `Z8` signature is the authoritative, machine-enforced spec for a function's
types (Abstract Wikipedia Function model, section Z8/Functions; schema Z8.yaml).

Usage: python3 blueprint/check_value_universe.py
"""
from __future__ import annotations

import json
import subprocess
import sys
import time

API = "https://www.wikifunctions.org/w/api.php"

# Val's three carriers.
VAL = {"Z13518": "nat", "Z40": "bool", "Z19677": "rational"}

# The six composites (functions) and the eleven leaves they call.
COMPOSITES = {"Z13701": "coprime", "Z13660": "lcm", "Z15849": "kronecker",
              "Z15483": "r-simplex", "Z20000": "Bayes", "Z14933": "perfect"}
LEAVES = {"Z13522": "natEq", "Z13612": "gcd", "Z13539": "mul", "Z13546": "div",
          "Z13521": "add", "Z13582": "dec", "Z13846": "ite", "Z13848": "choose",
          "Z13993": "sumProperDivisors", "Z19706": "ratMul", "Z19708": "ratDiv"}


def _fetch(zid: str, tries: int = 4) -> dict:
    for i in range(tries):
        out = subprocess.run(
            ["curl", "-sS", "--retry", "2", "--max-time", "30",
             f"{API}?action=wikilambda_fetch&format=json&zids={zid}"],
            capture_output=True, text=True).stdout
        if out.strip():
            try:
                return json.loads(json.loads(out)[zid]["wikilambda_fetch"])
            except Exception:
                pass
        time.sleep(1.2 * (i + 1))
    raise SystemExit(f"fetch failed for {zid}")


def _ref(x) -> str:
    if isinstance(x, str):
        return x
    if isinstance(x, dict):
        return x.get("Z9K1") or x.get("Z1K1") or "?"
    return str(x)


def signature(zid: str) -> tuple[list[str], str]:
    z8 = _fetch(zid).get("Z2K2", {})
    args = [_ref(a.get("Z17K1")) for a in z8.get("Z8K1", []) if isinstance(a, dict)]
    return args, _ref(z8.get("Z8K2"))


def main() -> int:
    closure: set[str] = set()
    show = lambda t: f"{t}({VAL.get(t, '!!')})"
    for group, table in (("COMPOSITE", COMPOSITES), ("LEAF", LEAVES)):
        print(f"=== {group} FUNCTIONS ===")
        for zid, label in table.items():
            args, ret = signature(zid)
            closure |= set(args) | {ret}
            print(f"  {zid} {label:18} ({', '.join(show(a) for a in args)}) -> {show(ret)}")

    extra = closure - set(VAL)
    print(f"\nType closure: {{{', '.join(sorted(closure))}}}")
    print(f"Val:          {{{', '.join(sorted(VAL))}}}  ({', '.join(VAL.values())})")
    if extra:
        print(f"\nINCOMPLETE — types outside Val: {sorted(extra)}")
        return 1
    print("\nCOMPLETE — every argument and return type is a Val carrier.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
