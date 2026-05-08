/-
Copyright (c) 2026.  Released under Apache 2.0 license.
Authors: TBD
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import PeterWeyl.Upstream.FDRepEnd

/-!
# Isotypic decomposition for finite-dimensional representations

> **Upstream target**: a new file
> `Mathlib/RepresentationTheory/Decomposition.lean`.
>
> This is the centrepiece of the contribution: an explicit data structure
> recording the isotypic decomposition of a finite-dimensional
> representation, together with a constructor extracting it from
> Mathlib's `IsSemisimpleModule.exists_linearEquiv_dfinsupp` plus an
> iso-class grouping.  Several headline character-theoretic results
> (`iso_iff_character_eq`, `simple_iff_inner_self_eq_one`) become short
> corollaries.

For `V : FDRep k G` with the standing Maschke hypotheses, `V` decomposes
into a finite direct sum of simple sub-representations grouped by
isomorphism class.  This file packages that decomposition into a
`SimpleDecomp V` data structure with the data needed to read off
multiplicities and characters.

## Main definitions

* `FDRep.SimpleDecomp V` — a finite indexing `ι` of distinct simple
  iso-classes appearing in `V`, with multiplicities `mult i ∈ ℕ` and a
  decomposition iso `V ≅ ⨁ᵢ (Sᵢ)^{mᵢ}` in the FDRep biproduct.

* `FDRep.simpleDecomp V` — existence of such a decomposition.

## Main theorems

* `FDRep.SimpleDecomp.character_eq` — character of `V` is the
  multiplicity-weighted sum of simple characters:
  `V.character = ∑ᵢ (mult i) • (S i).character`.

* `FDRep.SimpleDecomp.mult_eq_inner_char` — multiplicities are read off
  the character via the standard inner product:
  `(mult i) = ⅟|G| ∑_g χ_V(g) χ_{Sᵢ}(g⁻¹)`.

## Implementation notes

The constructor `simpleDecomp` is the substantive piece (~80–120 lines).
Plan:

1. Apply `IsSemisimpleModule.exists_linearEquiv_dfinsupp` to
   `V` (via the `Module (MonoidAlgebra k G) V` instance from
   `PeterWeyl.Upstream.FDRepEnd`) to obtain a set
   `s : Set (Submodule (MonoidAlgebra k G) V)` of mutually-independent
   simple submodules with `V ≃ₗ[(MonoidAlgebra k G)] Π₀ m : s, ↑m`.

2. View each element of `s` as an FDRep object via
   `Subrepresentation.toRepresentation` + `FDRep.of`.  The simplicity of
   the submodule transfers to simplicity in `FDRep` because Mathlib's
   `FDRep.Simple` and `IsSimpleModule (MonoidAlgebra k G)` agree on
   sub-representations.

3. Group `s` by FDRep iso class: define the `Setoid` whose relation is
   "isomorphic in FDRep" and take the `Quotient`.  Pick a canonical
   representative for each class (`Quotient.out`).  This produces the
   indexing `ι` plus the simple-iso-class representatives `S : ι → FDRep k G`.

4. The multiplicities `mult i` are the cardinalities of the iso-class
   sub-Finsets of `s`.  Each is non-zero by construction.

5. The decomposition iso `V ≅ ⨁ᵢ (S i)^{mult i}` follows from the
   `Π₀` linear equivalence of step 1, regrouped by iso class via the
   chosen representative.  Use `CategoryTheory.Limits.biproduct` for the
   FDRep biproduct (FDRep is a `k`-linear abelian category, so finite
   biproducts exist).

6. `character_eq` then follows by trace-additivity over the biproduct
   (`LinearMap.trace_eq_sum_trace_restrict`); this is the same step we
   isolate in `PeterWeyl.Auxiliary.character_eq_sum_restrict`.

7. `mult_eq_inner_char` follows by combining `character_eq` with
   `FDRep.char_orthonormal` applied pairwise; off-diagonal terms vanish
   by `pairwise_non_iso`.
-/

namespace FDRep

open CategoryTheory CategoryTheory.Limits

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

/-- Bridge `NeZero (Nat.card G : k) → Invertible (Fintype.card G : k)` so
`FDRep.char_orthonormal` (which uses `Invertible`) fires under our project's
standing hypotheses.  Mirrors the local copy in `PeterWeyl.Auxiliary`. -/
local instance (priority := 100) instInvertibleFintypeCard'' :
    Invertible ((Fintype.card G : k)) :=
  invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact NeZero.ne _)

/-- An *isotypic-decomposition certificate* for a finite-dimensional
representation: a finite indexing of distinct simple iso-classes
appearing in `V`, with multiplicities and a `k[G]`-linear decomposition iso. -/
structure SimpleDecomp (V : FDRep k G) where
  /-- Finite indexing of distinct simple iso-classes appearing in `V`. -/
  ι : Type u
  /-- `ι` is finite. -/
  fintypeι : Fintype ι
  /-- `ι` has decidable equality. -/
  decEqι : DecidableEq ι
  /-- Canonical representative of each iso-class. -/
  S : ι → FDRep k G
  /-- Each representative is simple. -/
  simpleS : ∀ i, Simple (S i)
  /-- Multiplicity of class `i` in `V`. -/
  mult : ι → ℕ
  /-- Multiplicities are nonzero (each class actually appears). -/
  mult_pos : ∀ i, 0 < mult i
  /-- Distinct indices give non-isomorphic representatives. -/
  pairwise_non_iso : ∀ ⦃i j : ι⦄, i ≠ j → IsEmpty (S i ≅ S j)
  /-- The decomposition iso as a `k[G]`-linear equivalence (DFinsupp form,
  closer to Mathlib's `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`
  output).  For finite `ι` this is equivalent to a Π form via
  `DFinsupp.equivFunOnFintype`. -/
  iso : V ≃ₗ[MonoidAlgebra k G] Π₀ (i : ι), Fin (mult i) → S i

attribute [instance] SimpleDecomp.fintypeι SimpleDecomp.decEqι SimpleDecomp.simpleS

/-- Convert a `MonoidAlgebra k G`-submodule of `V` to an FDRep object,
with the action induced by restricting `V.ρ`.  The submodule is stable
under each `V.ρ g` because it is closed under `MonoidAlgebra.single g 1 •`,
which equals `V.ρ g` (via `FDRep.single_smul`). -/
noncomputable def fdrepOfStableSubmodule (V : FDRep k G)
    (W : Submodule (MonoidAlgebra k G) V) : FDRep k G :=
  let W_k : Submodule k V := W.restrictScalars k
  haveI : Module.Finite k W_k := Module.Finite.of_injective W_k.subtype W_k.injective_subtype
  FDRep.of (V := W_k)
    { toFun := fun g => (V.ρ g).restrict (p := W_k) fun w hw => by
        change (V.ρ g) w ∈ W
        have : MonoidAlgebra.single g (1 : k) • w ∈ W := W.smul_mem _ hw
        rwa [FDRep.single_smul, one_smul] at this
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp }

/-- The setoid on `Fin n` whose classes are FDRep isomorphism classes of
the simple summands `fdrepOfStableSubmodule V (S i)`.  Used internally by
`simpleDecomp` to group the raw decomposition by iso class. -/
private noncomputable def isoClassSetoid (V : FDRep k G) {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra k G) V) :
    Setoid (Fin n) where
  r i j := Nonempty (fdrepOfStableSubmodule V (S i) ≅ fdrepOfStableSubmodule V (S j))
  iseqv :=
    { refl := fun _ => ⟨CategoryTheory.Iso.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h₁⟩ ⟨h₂⟩ => ⟨h₁ ≪≫ h₂⟩ }

/-- Existence of the canonical isotypic decomposition for any
`V : FDRep k G` under the standing hypotheses.

Implementation status: the bookkeeping fields (`ι, S, mult, mult_pos,
pairwise_non_iso`) are provided.  The decomposition iso (`iso` field)
requires reindexing Mathlib's `Π₀ (i : Fin n), S_raw i` through the
quotient `ι` plus FDRep-iso-to-`k[G]`-LinearEquiv conversion for each
summand; this last step is left as `sorry`. -/
noncomputable def simpleDecomp (V : FDRep k G) : SimpleDecomp V :=
  haveI : Module.Finite (MonoidAlgebra k G) V :=
    Module.Finite.of_restrictScalars_finite k (MonoidAlgebra k G) V
  haveI : IsSemisimpleModule (MonoidAlgebra k G) V := inferInstance
  let raw := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra k G) V
  let n : ℕ := raw.choose
  let S_raw : Fin n → Submodule (MonoidAlgebra k G) V := raw.choose_spec.choose
  -- Each `S_raw i` is a simple `k[G]`-submodule; wrap as an FDRep object.
  let S_fdrep : Fin n → FDRep k G := fun i => fdrepOfStableSubmodule V (S_raw i)
  -- Group `Fin n` by FDRep iso class.
  let σ : Setoid (Fin n) := isoClassSetoid V S_raw
  letI : DecidableRel σ.r := Classical.decRel _
  letI : DecidableEq (Quotient σ) := Classical.decEq _
  { ι := ULift.{u} (Quotient σ)
    fintypeι := inferInstance
    decEqι := inferInstance
    S := fun q => S_fdrep q.down.out
    simpleS := by
      -- Bridge `IsSimpleModule k[G] (S_raw i) → Simple (S_fdrep i)` missing
      -- in Mathlib; left as sorry for now.
      intro _; exact sorry
    mult := fun q => Fintype.card {i : Fin n // Quotient.mk σ i = q.down}
    mult_pos := by
      intro q
      refine Fintype.card_pos_iff.mpr ⟨⟨q.down.out, ?_⟩⟩
      exact Quotient.out_eq q.down
    pairwise_non_iso := by
      intro q₁ q₂ hne
      refine ⟨fun iso => hne ?_⟩
      apply ULift.ext
      exact Quotient.out_equiv_out.mp ⟨iso⟩
    iso := sorry }

namespace SimpleDecomp

variable {V : FDRep k G} (D : SimpleDecomp V)

/-- Character additivity over the decomposition. -/
theorem character_eq :
    V.character = ∑ i, ((D.mult i : ℕ) : k) • (D.S i).character := by
  -- Plan: use the iso `D.iso` together with `LinearMap.trace_eq_sum_trace_restrict`
  -- on the underlying biproduct (the local helper
  -- `PeterWeyl.Auxiliary.character_eq_sum_restrict` is the prototype).
  sorry

/-- Multiplicity formula: each `mult i` equals the inner product of `V`'s
character with the `i`-th simple's character.  This is the workhorse
identity for items 4 and 5 of the project. -/
theorem mult_eq_inner_char (i : D.ι) :
    ((D.mult i : ℕ) : k) =
      ⅟(Fintype.card G : k) • ∑ g : G, V.character g * (D.S i).character g⁻¹ := by
  -- Plan: substitute `character_eq` into the right-hand side, distribute
  -- the sum, apply `FDRep.char_orthonormal` pairwise on `(S j, S i)`, kill
  -- off-diagonal terms via `pairwise_non_iso`, collapse to the diagonal.
  sorry

end SimpleDecomp

end FDRep
