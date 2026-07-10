# Formalization blueprint

This directory builds the interactive dependency graph for the Wikifunctions Lean model. A green
node names one or more declarations that Lean resolves from the repository root module; prose-only
claims and open obligations are intentionally not marked formalized.

The blueprint is published at <https://deicyde.github.io/wikifunctions/>.

## Local checks

From the repository root:

```bash
lake build
python3 blueprint/check_decls.py
```

`check_decls.py` extracts every `\lean{Fully.Qualified.Name}` from `src/content.tex`, generates a
temporary Lean module importing `Wikifunctions`, and compile-checks the names. It does not use the
old short-name regular-expression heuristic.

To build the web version:

```bash
python3 -m venv .blueprint-venv
.blueprint-venv/bin/pip install -r blueprint/requirements.txt
cd blueprint/src
../../.blueprint-venv/bin/plastex -c plastex.cfg web.tex
cd ../..
python3 blueprint/make_find.py blueprint/web
python3 blueprint/make_legacy_redirects.py blueprint/web
```

The generated site is written to `blueprint/web/` and is not tracked. GitHub Actions repeats the
declaration check before publishing the site. `make_legacy_redirects.py` preserves chapter URLs
published by earlier blueprint versions, including `ch-zobject.html`.

## Source files

- `src/content.tex` is the formalization narrative and dependency graph.
- `src/web.tex` and `src/print.tex` are the HTML and PDF entry points.
- `check_decls.py` asks Lean to resolve every documented declaration.
- `make_find.py` generates links from blueprint nodes to repository source lines.
- `make_legacy_redirects.py` generates compatibility pages for retired chapter routes.

The schema/function-model links in the prose identify external authorities. Revision-sensitive
live data is also pinned in Lean declarations or adjacent module documentation; an external link
alone is never treated as a proof.
