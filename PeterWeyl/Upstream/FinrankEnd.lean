/-
Copyright (c) 2026.  Released under Apache 2.0 license.
Authors: TBD
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dimension of an endomorphism algebra in Wedderburn–Artin form

> **Upstream target**: `Mathlib/LinearAlgebra/Dimension/EndPiMatrix.lean`
> (or, alternatively, an extension of
> `Mathlib/LinearAlgebra/Dimension/Constructions.lean`).
>
> This is the smallest, most independent piece of the planned
> Mathlib contribution: a pure dimension calculation that doesn't mention
> representation theory or simplicity at all.  Useful for any caller of
> `IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end` who wants to read
> off the dimension of the endomorphism algebra.

Given a finite-product / matrix-block algebra equivalence
`E ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (Eᵢ i)`,
this file shows that
`Module.finrank k E = ∑ i, (d i)² * Module.finrank k (Eᵢ i)`.

## Main result

* `Module.finrank_End_pi_matrix` — the dimension formula.

## Implementation notes

The proof composes three Mathlib lemmas:
1. `LinearEquiv.finrank_eq` — transports `finrank` along the algebra equivalence
   (forgetting the multiplicative structure).
2. `Module.finrank_pi_fintype` — sums finranks across a finite product.
3. `Module.finrank_matrix` — `finrank k (Matrix (Fin n) (Fin n) E) = n² * finrank k E`.

The chain is one or two `simp_rw` steps.
-/

namespace Module

variable {k : Type*} [Field k]
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [AddCommGroup E] [Module k E]
variable {Eᵢ : ι → Type*} [∀ i, AddCommGroup (Eᵢ i)] [∀ i, Module k (Eᵢ i)]

/-- Dimension of an endomorphism algebra that splits as a product of matrix
algebras over (typically division) `k`-algebras.  The numerical formula is
`finrank k E = ∑ i, (d i)² * finrank k (Eᵢ i)`. -/
theorem finrank_End_pi_matrix
    [∀ i, Module.Finite k (Eᵢ i)] [∀ i, Module.Free k (Eᵢ i)] [Module.Finite k E]
    (d : ι → ℕ)
    (e : E ≃ₗ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (Eᵢ i)) :
    Module.finrank k E = ∑ i, (d i) ^ 2 * Module.finrank k (Eᵢ i) := by
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Fintype.card_fin]
  ring

end Module
