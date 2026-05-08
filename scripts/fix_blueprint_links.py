#!/usr/bin/env python3
"""
fix_blueprint_links.py
======================

Post-process ``blueprint/web/`` after ``leanblueprint web`` so that links
to Lean declarations point somewhere useful:

  * **Mathlib declarations** → Mathlib's own doc-gen4 deployment at
    ``https://leanprover-community.github.io/mathlib4_docs/find/#doc/X``,
    whose ``find/`` redirect resolves any Mathlib name.
  * **Project-local declarations** → the GitHub source file at the line
    where the declaration is defined, e.g.
    ``https://github.com/JonCYeh/PeterWeylThmFinite/blob/main/PeterWeyl.lean#L156``.

Why this exists
---------------

By default, leanblueprint emits every Lean link as
``<dochome>/find/#doc/X`` where ``<dochome>`` is the value of
``\\dochome{...}`` in ``blueprint/src/web.tex``. That works only if
doc-gen4 has been deployed at ``<dochome>`` *and* knows about every cited
declaration — including local ones. For projects that haven't deployed
doc-gen4 (or that prefer to point readers at GitHub source for local
decls), this rewrite is the simplest fix.

Usage::

    python3 scripts/fix_blueprint_links.py             # rewrite in place
    python3 scripts/fix_blueprint_links.py --dry-run   # report counts only

The script is idempotent: rerunning produces no further changes (it skips
hrefs that already point at mathlib4_docs or github.com).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BLUEPRINT_WEB = ROOT / "blueprint" / "web"

# Edit these two if the project moves or you want a different default branch.
GITHUB_REPO = "JonCYeh/PeterWeylThmFinite"
GITHUB_BRANCH = "main"

MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs"

# Lean files whose top-level declarations count as "local" (link to GitHub
# source). Glob is relative to ROOT.
LOCAL_LEAN_GLOBS = ["PeterWeyl.lean", "PeterWeyl/*.lean"]

# Match every <a href="..."> whose href ends in ``/find/#doc/<name>``,
# regardless of the URL prefix the LaTeX configured. Group 1 is the decl
# name. We deliberately don't match hrefs that already point at a
# mathlib4_docs or github.com URL, so the script is idempotent.
HREF_RE = re.compile(
    r'href="(?P<url>(?!https://leanprover-community\.github\.io/mathlib4_docs)'
    r'(?!https://github\.com/)'
    r'[^"]*?/find/#doc/(?P<name>[A-Za-z0-9_.\']+))"'
)

DECL_RE = re.compile(
    r"^(?:noncomputable\s+|protected\s+|private\s+)?"
    r"(?:def|theorem|lemma|instance|abbrev|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
NS_RE = re.compile(r"^namespace\s+(?P<ns>[A-Za-z_][A-Za-z0-9_.']*)\s*$")
NS_END_RE = re.compile(r"^end\s+(?P<ns>[A-Za-z_][A-Za-z0-9_.']*)\s*$")


def build_local_decl_map() -> dict[str, tuple[str, int]]:
    """Map fully qualified Lean name → (file path relative to repo root, line).

    We do a lightweight namespace-aware scan: track ``namespace X`` /
    ``end X`` blocks and prefix the bare declaration name with the current
    namespace stack. This catches names like
    ``PeterWeyl.groupAlgebra_algEquiv_pi_matrix`` and
    ``Representation.multiplicity_eq_inner_char`` that the blueprint cites.
    """
    out: dict[str, tuple[str, int]] = {}
    for pattern in LOCAL_LEAN_GLOBS:
        for path in sorted(ROOT.glob(pattern)):
            ns_stack: list[str] = []
            rel = path.relative_to(ROOT).as_posix()
            with path.open() as fh:
                for i, line in enumerate(fh, 1):
                    if m := NS_RE.match(line):
                        ns_stack.append(m.group("ns"))
                        continue
                    if m := NS_END_RE.match(line):
                        if ns_stack and ns_stack[-1] == m.group("ns"):
                            ns_stack.pop()
                        continue
                    if m := DECL_RE.match(line):
                        bare = m.group("name")
                        full = ".".join(ns_stack + [bare]) if ns_stack else bare
                        # First definition wins (mirroring Lean's name resolution).
                        out.setdefault(full, (rel, i))
    return out


def rewrite_html(text: str, decl_map: dict[str, tuple[str, int]]) -> tuple[str, int, int]:
    """Return (new_text, n_local_rewrites, n_mathlib_rewrites)."""
    n_local = n_mathlib = 0

    def repl(m: re.Match[str]) -> str:
        nonlocal n_local, n_mathlib
        name = m.group("name")
        if hit := decl_map.get(name):
            n_local += 1
            file_rel, line = hit
            new_url = (
                f"https://github.com/{GITHUB_REPO}/blob/{GITHUB_BRANCH}/"
                f"{file_rel}#L{line}"
            )
        else:
            n_mathlib += 1
            new_url = f"{MATHLIB_DOCS}/find/#doc/{name}"
        return f'href="{new_url}"'

    new_text = HREF_RE.sub(repl, text)
    return new_text, n_local, n_mathlib


def patch_dep_graph_worker(web_dir: Path, dry_run: bool) -> int:
    """The d3-graphviz `{useWorker: true}` config in `dep_graph_document.html`
    spawns a Web Worker that loads `graphvizlib.wasm`/`expatlib.wasm`.  The
    worker fails to render under several common local-serve setups (MIME
    type quirks, cross-origin restrictions on workers loading WASM, etc.),
    so the dependency graph silently shows nothing while the rest of the
    site works fine.

    Switching to `useWorker: false` runs the layout synchronously on the
    main thread — slightly slower but reliably renders.  This patch is
    safe to apply unconditionally; it's idempotent across reruns.
    """
    fp = web_dir / "dep_graph_document.html"
    if not fp.exists():
        return 0
    text = fp.read_text()
    new = text.replace("useWorker: true", "useWorker: false")
    if new == text:
        return 0
    if not dry_run:
        fp.write_text(new)
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    ap.add_argument(
        "--dry-run", action="store_true",
        help="don't write any files; just report counts",
    )
    ap.add_argument(
        "--web-dir", type=Path, default=DEFAULT_BLUEPRINT_WEB,
        help="directory of HTML files to patch (default: blueprint/web). "
             "In CI, point this at the Jekyll-bundled output, e.g. _site/blueprint.",
    )
    args = ap.parse_args()

    web_dir: Path = args.web_dir
    if not web_dir.is_dir():
        try:
            shown = web_dir.relative_to(ROOT)
        except ValueError:
            shown = web_dir
        print(
            f"ERROR: {shown} not found — "
            f"run `leanblueprint web` first (or pass --web-dir).",
            file=sys.stderr,
        )
        return 1

    decl_map = build_local_decl_map()
    print(
        f"local decl map: {len(decl_map)} names from {LOCAL_LEAN_GLOBS}",
        file=sys.stderr,
    )

    total_local = total_mathlib = 0
    files_touched = 0
    for html in sorted(web_dir.rglob("*.html")):
        text = html.read_text()
        new_text, nl, nm = rewrite_html(text, decl_map)
        if nl == 0 and nm == 0:
            continue
        files_touched += 1
        total_local += nl
        total_mathlib += nm
        if not args.dry_run:
            html.write_text(new_text)
        try:
            rel = html.relative_to(ROOT)
        except ValueError:
            rel = html
        print(f"  {rel}  local={nl}  mathlib={nm}")

    verb = "would rewrite" if args.dry_run else "rewrote"
    print(
        f"\n{verb} {total_local} local + {total_mathlib} mathlib hrefs "
        f"across {files_touched} files"
    )

    n_worker = patch_dep_graph_worker(web_dir, args.dry_run)
    if n_worker:
        verb2 = "would patch" if args.dry_run else "patched"
        print(f"{verb2} dep_graph_document.html: useWorker: true → false")

    return 0


if __name__ == "__main__":
    sys.exit(main())
