# Contributing

Contributions are welcome. This is a small focused repo (the Peter–Weyl
theorem for finite groups), so most contributions will be one of:

- **Bug fixes** in the [`PeterWeyl/`](PeterWeyl/) library or the blueprint.
- **Cleanups** that simplify proofs or align them with newer Mathlib API.
- **Mathlib backports** — if a lemma in this repo is general enough to
  belong upstream, opening a Mathlib PR is preferred over duplicating it
  here.

## Before you open a PR

1. `lake build` passes locally.
2. The blueprint still builds (`leanblueprint all`) and the dependency
   graph renders without errors. Every Lean declaration cited from the
   blueprint should still resolve to something that exists.
3. Lint passes — Mathlib's style conventions are honoured (no
   `auto-bound implicits`, descriptive names, `where`-clauses preferred
   over `let`-clauses inside `def`s).
4. If you added a new declaration, add a `\lean{...}` directive to the
   blueprint citing it, plus `\leanok` if the proof is complete.

## Bumping Mathlib

Use `scripts/update.sh` (or `lake update mathlib` followed by
`lake exe cache get`). Commit the resulting changes to `lake-manifest.json`
and `lean-toolchain` together as a single dependency-bump PR — don't mix
with substantive changes.

## Filing issues

Issues are tracked on the GitHub repository. When filing one, please
include:

- The Lean toolchain version (`cat lean-toolchain`).
- The Mathlib commit (visible in `lake-manifest.json`).
- A minimal reproducer if it's a build failure.

## Code of conduct

This project follows the [Lean community Code of
Conduct](https://leanprover-community.github.io/code-of-conduct.html);
see also [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) in this repository.
