# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) for the
Wikifunctions × Lean formalization: an interactive dependency graph in which every
node is pinned to the Lean declaration it formalizes **and** the live WikiLambda
object it models. It is the reviewable interface to the claim that this repo
faithfully models deployed Wikifunctions; the prose analysis lives in
[`../SPEC_AUDIT.md`](../SPEC_AUDIT.md) and the per-declaration citation map in
[`../BLUEPRINT.md`](../BLUEPRINT.md).

![dependency graph](dep_graph.png)

Each node carries a **Lean** link (to the exact source line on GitHub) and, where
it models a specific object, a **WikiLambda** link to
[wikifunctions.org](https://www.wikifunctions.org). Green = statement and proof
complete in Lean. Divergences from the live system are flagged inline (D1–D18).

## Structure

```
blueprint/
├── src/
│   ├── content.tex        ← the blueprint itself (4 chapters = the 4 spec layers)
│   ├── web.tex            ← plasTeX master (interactive HTML + dep graph)
│   ├── print.tex          ← xelatex master (PDF)
│   ├── blueprint.sty      ← local print-only macro stubs (web uses the plasTeX plugin)
│   ├── plastex.cfg, latexmkrc, extra_styles.css
│   └── macros/            ← common/web/print; defines \wf and \leansrc
├── check_decls.py         ← verifies every \lean{} names a real Lean declaration
└── dep_graph.{png,svg}    ← rendered static preview of the graph
```

## Build

One-time tooling (kept out of git in `.blueprint-venv/`):

```bash
python3 -m venv .blueprint-venv && . .blueprint-venv/bin/activate
pip install leanblueprint
```

Then:

```bash
# interactive web version + dependency graph  → blueprint/web/
cd blueprint/src && plastex -c plastex.cfg web.tex

# printable PDF                               → blueprint/print/print.pdf
cd blueprint/src && latexmk -xelatex -output-directory=../print print.tex
```

## Review it locally

```bash
python3 -m http.server 8137 --directory blueprint/web
# open http://localhost:8137/  (graph at /dep_graph_document.html)
```

## Check the Lean names

```bash
python3 blueprint/check_decls.py     # exits non-zero if any \lean{} name is unknown
```

## Declaration links (`\lean{}` → GitHub source)

leanblueprint renders every `\lean{Decl}` as a link `{dochome}/find/#doc/Decl`.
This project does **not** host doc-gen4 API docs, so `\dochome` (in `src/web.tex`)
points at our own static resolver instead:

```bash
python3 blueprint/make_find.py blueprint/web   # writes blueprint/web/find/index.html
```

`make_find.py` reads the `\lean{}`/`\leansrc{}` pairs out of `content.tex` and
emits a `find/` page that redirects each declaration to its exact Lean source
line on GitHub — so both the prose blueprint and the dependency-graph nodes link
straight to the code. The CI workflow runs this right after the plasTeX build.

The web build is also deployed to GitHub Pages by
`.github/workflows/blueprint.yml` on every push to `main` (enable Pages →
"GitHub Actions" in repo settings).
