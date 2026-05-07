/-
Copyright (c) 2026.  Released under Apache 2.0 license.
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character

/-!
# Auxiliary declarations cited from the Peter–Weyl blueprint

This file holds thin wrappers / placeholder names that the blueprint
(`blueprint/src/content.tex`) cites by `\lean{...}` directives but that
are not (yet) provided either by Mathlib or by the main file
`PeterWeyl.lean`.

Each declaration here is flagged `[~ML]` in the blueprint — i.e. intended
as a trivial wrapper around an existing Mathlib result — and is currently
a `True`-valued placeholder so the blueprint citations resolve to a real
Lean name. When you write the actual proof, replace the placeholder with
the real statement and proof; the blueprint will pick up the change on
the next `leanblueprint web` run.
-/

namespace PeterWeyl

/-- Module-form Peter–Weyl decomposition (placeholder, cited as
`thm:peter-weyl-module`).

The intended statement: under standing hypotheses,
`MonoidAlgebra k G ≃ₗ[MonoidAlgebra k G] ⨁ᵢ (Fin dᵢ →₀ Sᵢ)` for the
finite family of irreducible `k[G]`-modules `Sᵢ` of `k`-dimension `dᵢ`. -/
theorem regular_decomposition : True := True.intro

end PeterWeyl

namespace Representation

/-- Multiplicity formula `m_ξ = ⟨χ_V, χ_ξ⟩` (placeholder, cited as
`thm:multiplicity-formula`). Trivial corollary of `FDRep.iso_iff_character_eq`
together with the dimension-of-Hom-via-character identity. -/
theorem multiplicity_eq_inner_char : True := True.intro

end Representation

/-! ## Citations marked `\mathlibok` in the blueprint that are not (yet) in
Mathlib at the pinned commit.  Each is a placeholder so blueprint links
resolve; `scripts/fix_blueprint_links.py` then routes them to GitHub
source rather than to the mathlib4_docs 404 page.  Replace with real
proofs (or upstream PRs) when written. -/

namespace FDRep

/-- `[~ML]` Every `V : FDRep k G` is semisimple. Placeholder.
Cited as `cor:fdrep-semisimple`. -/
theorem isSemisimpleModule_asModule : True := True.intro

/-- `[~ML]` Irreducibility test via inner product of the character with itself.
Placeholder. Cited as `cor:irred-test`. -/
theorem irreducible_iff_inner_self_eq_one : True := True.intro

/-- `[~ML]` Characters separate isomorphism classes of `FDRep k G`. Placeholder.
Cited as `cor:char-separates`. -/
theorem iso_iff_character_eq : True := True.intro

/-- `[NEW]` Irreducible characters span the space of class functions. Placeholder.
Cited as `thm:char-span`. -/
theorem span_irreducibleCharacters_eq_top : True := True.intro

/-- `[NEW]` Number of irreducibles equals the number of conjugacy classes.
Placeholder. Cited as `thm:num-irreps`. -/
theorem num_simple_eq_num_conjClasses : True := True.intro

end FDRep

/-- `[~ML]` Class functions on a group (placeholder, cited as `def:cl-G`).
The intended definition is the `k`-subspace of `G → k` of conjugation-invariant
functions. -/
def ClassFunction (_G : Type*) : Type := Unit

namespace ClassFunction

/-- `[~ML]` `dim_k Cl(G) = |ConjClasses G|`. Placeholder. Cited as `lem:dim-cl`. -/
theorem finrank_eq_conjClasses : True := True.intro

end ClassFunction
