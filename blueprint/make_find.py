#!/usr/bin/env python3
"""Generate the blueprint's declaration resolver: a doc-gen4-style `find/` page.

leanblueprint renders every `\\lean{Decl}` as a link `{dochome}/find/#doc/{Decl}`.
We do not host doc-gen4 API docs (the CI blueprint build is plasTeX-only), so
instead of a doc site we ship a tiny static resolver at `<web>/find/index.html`
that reads the `#doc/<Decl>` hash and redirects to that declaration's exact Lean
source line on GitHub.

The declaration -> source map is recovered from `blueprint/src/content.tex`
itself: every node pairs a `\\lean{A, B}` with a `\\leansrc{file}{line}`, so the
map stays in lockstep with the blueprint content (single source of truth) and
needs no Lean parsing.

Usage: python3 blueprint/make_find.py [web_dir]   (default: blueprint/web)
"""
import json
import re
import sys
from pathlib import Path

REPO = "Deicyde/wikifunctions"
BRANCH = "main"
HERE = Path(__file__).resolve().parent
CONTENT = HERE / "src" / "content.tex"

lean_re = re.compile(r"\\lean\{([^}]*)\}")
leansrc_re = re.compile(r"\\leansrc\{([^}]*)\}\{([^}]*)\}")


def build_map() -> dict[str, str]:
    text = CONTENT.read_text(encoding="utf-8")
    leans = [(m.start(), m.group(1)) for m in lean_re.finditer(text)]
    srcs = [(m.start(), m.group(1), m.group(2)) for m in leansrc_re.finditer(text)]
    if not srcs:
        sys.exit("make_find: no \\leansrc found in content.tex")

    mapping: dict[str, str] = {}
    unresolved: list[str] = []
    for pos, decls in leans:
        # nearest \leansrc occurring after this \lean
        nxt = next(((f, l) for (sp, f, l) in srcs if sp > pos), None)
        for decl in (d.strip() for d in decls.split(",") if d.strip()):
            if nxt is None:
                unresolved.append(decl)
                continue
            f, l = nxt
            mapping[decl] = f"https://github.com/{REPO}/blob/{BRANCH}/{f}#L{l}"
    if unresolved:
        print(f"make_find: WARNING unresolved decls: {unresolved}", file=sys.stderr)
    return mapping


PAGE = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>Find declaration</title>
<meta name="robots" content="noindex">
<style>body{{font-family:system-ui,sans-serif;max-width:40em;margin:4em auto;padding:0 1em;color:#222}}
code{{background:#f4f4f4;padding:.1em .3em;border-radius:3px}}a{{color:#3b5}}</style>
</head><body>
<h1>Resolving declaration&hellip;</h1>
<p id="msg">If you are not redirected, the declaration was not found in this blueprint.</p>
<p><a href="../">&larr; Back to the blueprint</a> &middot;
   <a href="https://github.com/{repo}">repository</a></p>
<script>
// decl -> exact Lean source line on GitHub, generated from content.tex.
const MAP = {map};
const REPO = "https://github.com/{repo}";
function resolve() {{
  let h = decodeURIComponent(location.hash.replace(/^#/, ""));
  // leanblueprint uses the doc-gen4 form "#doc/<FullyQualifiedName>".
  h = h.replace(/^doc\\//, "");
  if (!h) return;
  const url = MAP[h];
  if (url) {{ location.replace(url); return; }}
  // Unknown decl: fall back to a repo code search for the short name.
  const short = h.split(".").pop();
  document.getElementById("msg").innerHTML =
    '<code>' + h + '</code> is not a blueprint declaration. ' +
    '<a href="' + REPO + '/search?q=' + encodeURIComponent(short) + '&type=code">Search the repo</a>.';
}}
addEventListener("hashchange", resolve);
resolve();
</script>
</body></html>
"""


def main() -> None:
    web = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "web"
    mapping = build_map()
    out_dir = web / "find"
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "index.html").write_text(
        PAGE.format(map=json.dumps(mapping, indent=0), repo=REPO), encoding="utf-8"
    )
    print(f"make_find: wrote {out_dir/'index.html'} with {len(mapping)} declarations")


if __name__ == "__main__":
    main()
