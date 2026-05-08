# Peter–Weyl theorem for finite groups, in Lean 4

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 / Mathlib formalization of the **Peter–Weyl theorem for finite
groups** and its sum-of-squares dimension identity.

> **Theorem.** Let `G` be a finite group and `k` an algebraically closed
> field whose characteristic does not divide `|G|`. Then the group algebra
> `k[G]` is `k`-algebra isomorphic to a finite product of matrix algebras
> over `k`.

> **Corollary.** `|G| = ∑ᵢ dᵢ²`, where the sum is over the irreducible
> `k`-representations of `G` and `dᵢ` is their dimension.

The Lean source lives in [`PeterWeyl/`](PeterWeyl/), with an umbrella
file [`PeterWeyl.lean`](PeterWeyl.lean) at the project root that imports
both submodules.  The proof itself is in
[`PeterWeyl/Basic.lean`](PeterWeyl/Basic.lean); the two main results are
[`groupAlgebra_algEquiv_pi_matrix`](PeterWeyl/Basic.lean#L157) and
[`sum_sq_dim_eq_card`](PeterWeyl/Basic.lean#L194).
Auxiliary stubs cited from the blueprint live in
[`PeterWeyl/Auxiliary.lean`](PeterWeyl/Auxiliary.lean).

## Proof outline

The proof routes through the ring-theoretic Wedderburn–Artin theorem
([`Mathlib.RingTheory.SimpleModule.WedderburnArtin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/SimpleModule/WedderburnArtin.html)):

1. Maschke's theorem (Mathlib) shows `k[G]` is a semisimple ring.
2. Wedderburn–Artin (Mathlib) gives `k[G] ≃ ∏ᵢ Mₙᵢ(Dᵢ)` for finite-dim
   division `k`-algebras `Dᵢ`.
3. Algebraic closedness of `k` collapses each `Dᵢ` to `k`.
4. Counting `k`-dimensions on both sides yields the sum-of-squares
   identity.

A LaTeX exposition of the proof, with cross-references to the Lean
declarations, lives in [`blueprint/`](blueprint/) and follows
[Terence Tao's blog post on the Peter–Weyl theorem](https://terrytao.wordpress.com/2011/01/23/the-peter-weyl-theorem-and-non-abelian-fourier-analysis-on-compact-groups/).

## Build

You need [elan](https://github.com/leanprover/elan) installed (the Lean
version manager). Then:

```sh
git clone <this-repo>
cd PeterWeylThmFinite
lake exe cache get   # download pre-built Mathlib oleans (~5 min, one-time)
lake build           # compile our project (fast once Mathlib is cached)
```

The `lean-toolchain` file pins the exact Lean version; `elan` will install
it automatically on first invocation.

## Blueprint

The blueprint is a LaTeX document with a clickable dependency graph that
mirrors the Lean development. To build and view it locally:

```sh
python3 -m venv venv && source venv/bin/activate
pip install leanblueprint
leanblueprint web         # rebuild HTML in blueprint/web/
leanblueprint serve       # start a local server (open http://localhost:8000/)
```

The dependency graph is at
[`http://localhost:8000/dep_graph_document.html`](http://localhost:8000/dep_graph_document.html).
If `leanblueprint serve` prints `Serving http://0.0.0.0:8000/`, just type
`http://localhost:8000/` in your browser — Chrome/Safari refuse `0.0.0.0`.

## Repository layout

- [`PeterWeyl.lean`](PeterWeyl.lean) — umbrella, imports the two submodules.
- [`PeterWeyl/`](PeterWeyl/) — the Lean development:
  [`Basic.lean`](PeterWeyl/Basic.lean) holds the proof of the theorem;
  [`Auxiliary.lean`](PeterWeyl/Auxiliary.lean) holds blueprint citation
  stubs (some completed, some `sorry`'d with proof plans).
- [`blueprint/`](blueprint/) — LaTeX blueprint and dependency graph
  (sources in [`blueprint/src/`](blueprint/src/), rendered HTML in
  [`blueprint/web/`](blueprint/web/)).
- [`scripts/`](scripts/) — helper scripts (Mathlib version updater, etc.).
- [`.github/workflows/`](.github/workflows/) — CI: project build,
  blueprint build, GitHub Pages deploy.

## License

Apache 2.0 — see [LICENSE](LICENSE).
If you use this formalization in academic work, see
[`CITATION.bib`](CITATION.bib).

## References

- Terence Tao,
  [The Peter–Weyl theorem and non-abelian Fourier analysis on compact groups](https://terrytao.wordpress.com/2011/01/23/the-peter-weyl-theorem-and-non-abelian-fourier-analysis-on-compact-groups/) (2011).
- Project template: [leanprover-community/LeanProject](https://github.com/leanprover-community/LeanProject).
- Blueprint tooling: [PatrickMassot/leanblueprint](https://github.com/PatrickMassot/leanblueprint).
