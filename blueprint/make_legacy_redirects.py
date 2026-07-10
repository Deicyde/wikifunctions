#!/usr/bin/env python3
"""Generate compatibility redirects for retired blueprint chapter URLs.

plasTeX derives chapter filenames from LaTeX labels.  Renaming a chapter therefore
changes its public URL unless we preserve the old route explicitly.  GitHub Pages
builds from a fresh checkout, so stale files in a developer's local ``web/``
directory cannot provide that compatibility layer.

Usage: python3 blueprint/make_legacy_redirects.py [web_dir]
       (default: blueprint/web)
"""

import json
import sys
from html import escape
from pathlib import Path


HERE = Path(__file__).resolve().parent

# Routes published by the previous blueprint structure.
LEGACY_REDIRECTS = {
    "ch-zobject.html": "ch-model.html",
    "ch-canonical.html": "ch-model.html",
    "ch-types.html": "ch-schema.html",
}


def redirect_page(target: str) -> str:
    quoted_target = json.dumps(target)
    escaped_target = escape(target, quote=True)
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta http-equiv="refresh" content="0; url={escaped_target}">
  <meta name="robots" content="noindex">
  <link rel="canonical" href="{escaped_target}">
  <title>Blueprint page moved</title>
</head>
<body>
  <p>This blueprint chapter moved to <a href="{escaped_target}">{escaped_target}</a>.</p>
  <script>
    location.replace({quoted_target} + location.search + location.hash);
  </script>
</body>
</html>
"""


def main() -> None:
    web = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "web"
    missing_targets = [target for target in LEGACY_REDIRECTS.values() if not (web / target).is_file()]
    if missing_targets:
        sys.exit(f"make_legacy_redirects: missing generated targets: {sorted(set(missing_targets))}")

    for legacy, target in LEGACY_REDIRECTS.items():
        (web / legacy).write_text(redirect_page(target), encoding="utf-8")

    print(f"make_legacy_redirects: wrote {len(LEGACY_REDIRECTS)} compatibility pages")


if __name__ == "__main__":
    main()
