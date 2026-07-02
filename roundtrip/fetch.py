#!/usr/bin/env python3
"""Fetch deployed Wikifunctions code implementations from the live API, so the
round-trip runs against *production* source rather than the vendored copies.

A function's `Z8K4` lists its implementation ZIDs; a code implementation carries
`Z14K3` (a `Z16` Code object) whose `Z16K1` is the programming language and
`Z16K2` the source string. This module walks `Z8K4` in order and returns the
first implementation in the requested language — mirroring the orchestrator's
first-listed selection.

Uses `curl` (not urllib) to sidestep the macOS Python CA-bundle issue, matching
the convention of the WikiLean build scripts.

CLI:
    fetch.py <function-zid>     print the deployed source
    fetch.py --check           AST-diff live source against the vendored programs/*.py
    fetch.py --update          overwrite the vendored programs/*.py from live
"""
from __future__ import annotations

import ast
import json
import subprocess
import sys
import time
from pathlib import Path

API = "https://www.wikifunctions.org/w/api.php"
PYTHON_LANG = "Z610"           # the Wikifunctions programming-language ZID for Python
HERE = Path(__file__).resolve().parent

# known function ZID -> vendored source stem in programs/
VENDORED = {"Z13701": "Z13701", "Z13667": "Z13667"}


class FetchError(Exception):
    pass


def _fetch_raw(zid: str, attempts: int = 4) -> dict:
    """Fetch and parse one ZObject, retrying transient empty/failed responses.
    The reply nests the object as a JSON *string* under `wikilambda_fetch`."""
    last = "no attempt made"
    for i in range(attempts):
        r = subprocess.run(
            ["curl", "-sS", "--retry", "2", "--retry-delay", "1", "--max-time", "30",
             f"{API}?action=wikilambda_fetch&format=json&zids={zid}"],
            capture_output=True, text=True)
        if r.returncode == 0 and r.stdout.strip():
            try:
                outer = json.loads(r.stdout)
            except json.JSONDecodeError:
                last = f"non-JSON body: {r.stdout[:120]!r}"
            else:
                if zid in outer and "wikilambda_fetch" in outer[zid]:
                    return json.loads(outer[zid]["wikilambda_fetch"])
                last = f"unexpected keys: {list(outer)[:4]}"
        else:
            last = f"empty/failed (rc={r.returncode}): {r.stderr.strip()[:120]}"
        time.sleep(1.5 * (i + 1))
    raise FetchError(f"fetch {zid} failed after {attempts} attempts: {last}")


def _value(obj: dict) -> dict:
    """The persistent object's value (Z2K2), or the object itself if already a value."""
    return obj.get("Z2K2", obj)


def _as_str(z6) -> str:
    if isinstance(z6, str):
        return z6                                # canonical: a bare string
    if isinstance(z6, dict):
        return z6.get("Z6K1", "")                # normal form: { Z1K1: Z6, Z6K1: ... }
    raise FetchError(f"not a Z6 string: {z6!r}")


def _lang(z16k1) -> str:
    if isinstance(z16k1, str):
        return z16k1                             # canonical reference, e.g. "Z610"
    if isinstance(z16k1, dict):
        return z16k1.get("Z9K1", "")             # normal-form reference
    raise FetchError(f"not a language reference: {z16k1!r}")


def deployed_code(function_zid: str, lang: str = PYTHON_LANG) -> tuple[str, str]:
    """(impl_zid, source) of the first `lang` code implementation of the function."""
    fn = _value(_fetch_raw(function_zid))
    z8k4 = fn.get("Z8K4")
    if not isinstance(z8k4, list) or len(z8k4) < 2:
        raise FetchError(f"{function_zid} lists no implementations (Z8K4)")
    for impl_zid in z8k4[1:]:                     # z8k4[0] is the 'Z14' type header
        impl = _value(_fetch_raw(impl_zid))
        z16 = impl.get("Z14K3")
        if isinstance(z16, dict) and _lang(z16.get("Z16K1")) == lang:
            return impl_zid, _as_str(z16.get("Z16K2"))
    raise FetchError(f"{function_zid} has no {lang} code implementation in Z8K4")


def _norm(src: str) -> str:
    return ast.dump(ast.parse(src))


def cmd_check() -> int:
    drift = 0
    for zid, stem in VENDORED.items():
        vend = (HERE / "programs" / f"{stem}.py").read_text()
        impl, live = deployed_code(zid)
        if _norm(vend) == _norm(live):
            print(f"ok    {zid} (impl {impl}): programs/{stem}.py matches deployed source (AST)")
        else:
            drift += 1
            print(f"DRIFT {zid} (impl {impl}): deployed source differs (AST) from programs/{stem}.py")
    if drift:
        print(f"\n{drift} function(s) drifted — update the vendored source and re-verify the Prog.lean.")
    return 1 if drift else 0


def cmd_update() -> int:
    for zid, stem in VENDORED.items():
        _, live = deployed_code(zid)
        # re-emit through ast so the vendored copy is normalised (4-space indent)
        (HERE / "programs" / f"{stem}.py").write_text(ast.unparse(ast.parse(live)) + "\n")
        print(f"updated programs/{stem}.py from deployed {zid}")
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        print("usage: fetch.py {<function-zid> | --check | --update}", file=sys.stderr)
        return 2
    if argv[0] == "--check":
        return cmd_check()
    if argv[0] == "--update":
        return cmd_update()
    impl, src = deployed_code(argv[0])
    print(f"# {argv[0]} -> deployed implementation {impl}\n{src}", end="" if src.endswith("\n") else "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
