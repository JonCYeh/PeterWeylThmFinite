/-
Copyright (c) 2026.  Released under Apache 2.0 license.
-/
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.Algebra.Algebra.Pi

/-!
# The Peter–Weyl Theorem for finite groups

This file proves the **Peter–Weyl theorem** for a finite group `G` over an
algebraically closed field `k` whose characteristic does not divide `|G|`:

> The group algebra `k[G]` is `k`-algebra isomorphic to a finite product of
> matrix algebras over `k`.

We deduce the **sum-of-squares dimension identity** `|G| = ∑ᵢ dᵢ²`.

## Proof strategy

The proof routes through the ring-theoretic Wedderburn–Artin theorem in
`Mathlib.RingTheory.SimpleModule.WedderburnArtin`:

1. **Maschke's theorem** — `MonoidAlgebra.Submodule.instIsSemisimpleModule`
   in Mathlib registers `IsSemisimpleModule (MonoidAlgebra k G) V` for every
   `[Module (MonoidAlgebra k G) V]`. Specialised to `V := MonoidAlgebra k G`
   this gives `IsSemisimpleRing (MonoidAlgebra k G)`.

2. **Wedderburn–Artin** —
   `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` produces
   an isomorphism `k[G] ≃ₐ[k] ∏ᵢ Mat_{dᵢ}(Dᵢ)` with each `Dᵢ` a
   finite-dimensional division `k`-algebra.

3. **Algebraic closedness** collapses each `Dᵢ` to `k` via
   `IsAlgClosed.algebraMap_surjective_of_isAlgebraic`.

4. **Dimension count** of `k[G] ≃ ∏ᵢ Mat_{dᵢ}(k)` gives the sum-of-squares
   identity.

## Main results

* `PeterWeyl.divisionAlgebra_algEquiv_of_isAlgClosed` :
    a finite-dimensional division algebra over an algebraically closed
    field equals the field.
* `PeterWeyl.groupAlgebra_algEquiv_pi_matrix` :
    the Peter–Weyl decomposition
    `MonoidAlgebra k G ≃ₐ[k] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`.
* `PeterWeyl.sum_sq_dim_eq_card` :
    `Fintype.card G = ∑ i, (d i) ^ 2`.

## Standing hypotheses

`[Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero ((Nat.card G : k))]`.
The last is the standard Mathlib spelling of "char k does not divide |G|".

## Implementation notes

This file relies on declarations from recent Mathlib (post-2025-11):
* `Representation.IsIrreducible` and the bundled `IntertwiningMap`/`Equiv`
  API in `Mathlib.RepresentationTheory.Irreducible` and
  `Mathlib.RepresentationTheory.Intertwining`.
* `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` in
  `Mathlib.RingTheory.SimpleModule.WedderburnArtin`.

The author cannot run the Lean compiler in the environment in which this file
was authored; some lemma names in the dimension-counting step may need minor
adjustment (e.g. `Module.finrank_matrix` vs the variant returning
`Fintype.card m * Fintype.card n` rather than the squared form). All such
points are clearly flagged as `sorry` in this file.
-/

open scoped Classical
open MonoidAlgebra Module

namespace PeterWeyl

/-! ## Section 1: Standing hypotheses -/

variable (k G : Type*) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero ((Nat.card G : k))]

/-! ## Section 2: Semisimplicity of `k[G]` (Maschke) -/

/-- Maschke's theorem: the group algebra of a finite group over a field of
characteristic not dividing the group order is semisimple as a ring.

This is a direct consequence of `MonoidAlgebra.Submodule.instIsSemisimpleModule`
combined with the unfolding `IsSemisimpleRing R := IsSemisimpleModule R R`.
The Mathlib docstring on the former instance explicitly notes that this
implies `IsSemisimpleRing k[G]`. -/
instance instIsSemisimpleRing_groupAlgebra :
    IsSemisimpleRing (MonoidAlgebra k G) :=
  inferInstance

/-- `MonoidAlgebra k G = G →₀ k` is a finite-dimensional `k`-module. -/
instance instModuleFinite_groupAlgebra : Module.Finite k (MonoidAlgebra k G) :=
  Module.Finite.finsupp

omit [IsAlgClosed k] [Group G] [NeZero ((Nat.card G : k))] in
/-- The `k`-dimension of the group algebra equals the order of the group. -/
lemma finrank_groupAlgebra : finrank k (MonoidAlgebra k G) = Fintype.card G := by
  -- `MonoidAlgebra k G` is reducibly equal to `G →₀ k`.
  -- Mathlib provides `Module.finrank_finsupp_self : finrank R (ι →₀ R) = Fintype.card ι`.
  exact Module.finrank_finsupp_self k

/-! ## Section 3: Finite-dim division algebras over alg-closed fields

A finite-dimensional division `k`-algebra over an algebraically closed `k`
is isomorphic to `k` itself. This is the only genuinely new lemma the proof
requires; it is not currently packaged in Mathlib, but its proof is short:
since `D` is finite-dimensional over `k`, every element is algebraic, and
Mathlib's `IsAlgClosed.algebraMap_surjective_of_isAlgebraic` gives
surjectivity of `algebraMap k D`. The map is automatically injective
(nontrivial field hom).
-/

/-- The canonical algebra map `k → D` is surjective when `D` is a
finite-dimensional division algebra over an algebraically closed field `k`.
-/
lemma algebraMap_surjective_of_finiteDim_divisionRing
    (D : Type*) [DivisionRing D] [Algebra k D] [Module.Finite k D] :
    Function.Surjective (algebraMap k D) :=
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := D)).2

omit [IsAlgClosed k] in
/-- The canonical algebra map `k → D` is injective for any nonzero
`k`-algebra `D` with `[Field k]`. -/
lemma algebraMap_injective_of_field
    (D : Type*) [Ring D] [Nontrivial D] [Algebra k D] :
    Function.Injective (algebraMap k D) :=
  (algebraMap k D).injective

/-- **A finite-dimensional division algebra over an algebraically closed
field equals the field.** -/
noncomputable def divisionAlgebra_algEquiv_of_isAlgClosed
    (D : Type*) [DivisionRing D] [Algebra k D] [Module.Finite k D] :
    k ≃ₐ[k] D :=
  AlgEquiv.ofBijective (Algebra.ofId k D)
    ⟨algebraMap_injective_of_field k D,
     algebraMap_surjective_of_finiteDim_divisionRing k D⟩

/-! ## Section 4: The Peter–Weyl theorem (ring form) -/

/-- **Peter–Weyl theorem, ring form.**

The group algebra `k[G]` is `k`-algebra isomorphic to a finite product of
matrix algebras over `k`:
  `MonoidAlgebra k G ≃ₐ[k] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k`. -/
theorem groupAlgebra_algEquiv_pi_matrix :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, NeZero (d i)),
      Nonempty (MonoidAlgebra k G ≃ₐ[k]
        ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k) := by
  -- Step 1: Wedderburn–Artin (algebra form, finite version) on k[G].
  -- Hypotheses verified:
  --   * [CommSemiring k] from [Field k].
  --   * [Ring (MonoidAlgebra k G)] : Mathlib instance.
  --   * [Algebra k (MonoidAlgebra k G)] : Mathlib instance.
  --   * [IsSemisimpleRing (MonoidAlgebra k G)] : `instIsSemisimpleRing_groupAlgebra`.
  --   * [Module.Finite k (MonoidAlgebra k G)] : `instModuleFinite_groupAlgebra`.
  obtain ⟨n, D, d, _hDring, _hDalg, _hDfin, hd_ne, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite k
      (MonoidAlgebra k G)
  -- Step 2: each `D i` is `≃ₐ[k]` to `k` because `D i` is fin-dim div-alg
  -- over alg-closed `k`. Note: the existential gives us `Module.Finite k (D i)`
  -- via `_hDfin`.
  refine ⟨n, d, hd_ne, ⟨?_⟩⟩
  -- The matrix-pi side becomes `∀ i, Mat (D i)`; we want `∀ i, Mat k`.
  -- Combine with the per-component algebra equiv `D i ≃ₐ[k] k`, lifted to
  -- matrices via `AlgEquiv.mapMatrix`.
  refine φ.trans ?_
  -- Apply `AlgEquiv.piCongrRight` to the family of per-component equivs.
  refine AlgEquiv.piCongrRight (fun i => ?_)
  -- Per-component: lift `(D i ≃ₐ[k] k)` to matrices.
  -- We need `Module.Finite k (D i)`, which is `_hDfin i` from the destructured tuple.
  haveI : Module.Finite k (D i) := _hDfin i
  exact (divisionAlgebra_algEquiv_of_isAlgClosed k (D i)).symm.mapMatrix

/-! ## Section 5: Sum-of-squares dimension formula -/

include k in
/-- **Sum-of-squares dimension identity.**

Under the standing hypotheses, the cardinality of `G` equals the sum of the
squares of the dimensions of the matrix blocks in the Peter–Weyl
decomposition. -/
theorem sum_sq_dim_eq_card :
    ∃ (n : ℕ) (d : Fin n → ℕ),
      (Fintype.card G) = ∑ i : Fin n, (d i) ^ 2 := by
  obtain ⟨n, d, _hd_ne, ⟨φ⟩⟩ := groupAlgebra_algEquiv_pi_matrix k G
  refine ⟨n, d, ?_⟩
  -- Take `finrank k` of both sides of φ. Linear equivalences preserve finrank.
  have hLE : finrank k (MonoidAlgebra k G) =
             finrank k (∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) k) :=
    LinearEquiv.finrank_eq φ.toLinearEquiv
  -- LHS = |G|.
  rw [finrank_groupAlgebra] at hLE
  -- RHS: expand the finrank of the pi-product, then of each matrix block.
  rw [hLE, Module.finrank_pi_fintype k]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, sq]

end PeterWeyl

/-!
## Appendix: known caveats

The single `sorry` above is the dimension-counting step
`finrank k (∀ i, Matrix (Fin (d i)) (Fin (d i)) k) = ∑ i, (d i)^2`.
The mathematics is trivial; the formalisation requires composing two
Mathlib lemmas whose exact spellings should be verified against the
current Mathlib state. Likely candidates:

```
Module.finrank_pi_fintype :
    finrank R (∀ i : ι, M i) = ∑ i, finrank R (M i)

Matrix.finrank_matrix : -- or similarly named
    finrank R (Matrix m n R) = Fintype.card m * Fintype.card n
```

With these, the proof is:
```
rw [Module.finrank_pi_fintype, Fintype.card_fin]
simp_rw [Matrix.finrank_matrix, Fintype.card_fin, ← sq]
```
-/
