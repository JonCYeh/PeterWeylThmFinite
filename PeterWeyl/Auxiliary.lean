/-
Copyright (c) 2026.  Released under Apache 2.0 license.
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Algebra.DirectSum.LinearMap
import PeterWeyl.Upstream.FDRepEnd

open CategoryTheory

universe u

/-!
# Auxiliary declarations cited from the Peter–Weyl blueprint

Each declaration here is referenced by a `\lean{...}` directive in
`blueprint/src/content.tex` but is not provided by Mathlib at the pinned
toolchain.

Items flagged `[~ML]` in the blueprint are intended as trivial wrappers
around existing Mathlib results.  Two of these wrappers (the most
mechanical ones) are completed below.  The remaining `[~ML]` items have
their full signatures stated and are `sorry`'d, with a detailed proof
plan in their docstring; the corresponding `\leanok` markers have been
*removed* from `content.tex` so the dependency graph reflects the open
status accurately.

Items flagged `[NEW]` are kept as `True := True.intro` placeholders for
now — the right Lean signature for them depends on prerequisites that
themselves haven't landed (see their docstrings).
-/

/-! ## [~ML] items with completed proofs -/

namespace FDRep

section
variable {k G : Type u} [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]

-- The `Module (MonoidAlgebra k G) V` instance for `V : FDRep k G`
-- (`FDRep.moduleMonoidAlgebra`) lives in `PeterWeyl.Upstream.FDRepEnd`,
-- imported above.  It's the foundation everything below depends on.

/-- Every `V : FDRep k G` is a semisimple `k[G]`-module.  Cited as
`cor:fdrep-semisimple`.  Reduces to Maschke's
`MonoidAlgebra.Submodule.instIsSemisimpleModule` via the
`moduleMonoidAlgebra` instance above. -/
theorem isSemisimpleModule_asModule (V : FDRep k G) :
    IsSemisimpleModule (MonoidAlgebra k G) V :=
  inferInstance

end

end FDRep

/-- The `k`-subspace of `G → k` of conjugation-invariant functions.  Cited as
`def:cl-G`. -/
def ClassFunction (k : Type*) [Semiring k] (G : Type*) [Group G] :
    Submodule k (G → k) where
  carrier := { f | ∀ g h : G, f (h * g * h⁻¹) = f g }
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g h
    simp only [Pi.add_apply, h₁ g h, h₂ g h]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c f hf g h
    simp only [Pi.smul_apply, hf g h]

/-! ## [~ML] items with proof plans (stated with `sorry`) -/

namespace ClassFunction

variable (k : Type*) [Field k] (G : Type*) [Group G]

/-- The `k`-linear equivalence between functions on `ConjClasses G` and class
functions on `G`: precompose with `ConjClasses.mk` going one way; descend
via `Quotient.lift` going the other.  This bridge is the workhorse for
`finrank_eq_conjClasses` below. -/
noncomputable def equivConjClasses : (ConjClasses G → k) ≃ₗ[k] ClassFunction k G where
  toFun g :=
    ⟨g ∘ ConjClasses.mk, fun x h => by
      show g (ConjClasses.mk (h * x * h⁻¹)) = g (ConjClasses.mk x)
      congr 1
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)⟩
  invFun f := Quotient.lift f.val (fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc]
    exact (f.property a c).symm)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv g := by
    ext c
    induction c using Quotient.inductionOn with
    | _ x => rfl
  right_inv f := by
    ext x
    rfl

/-- `dim_k Cl(G) = #ConjClasses G`.  Cited as `lem:dim-cl`.

Proof: transport `Module.finrank_pi` (`finrank k (ι → k) = #ι`) along the
linear equivalence `equivConjClasses` (above). -/
theorem finrank_eq_conjClasses [Fintype (ConjClasses G)] :
    Module.finrank k (ClassFunction k G) = Fintype.card (ConjClasses G) := by
  rw [← LinearEquiv.finrank_eq (equivConjClasses k G)]
  exact Module.finrank_pi k

end ClassFunction

namespace FDRep

section
variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

/-- Bridge `NeZero (Nat.card G : k) → Invertible (Fintype.card G : k)` so
`FDRep.char_orthonormal` (which uses `Invertible`) fires under our project's
standing hypotheses. -/
local instance (priority := 100) instInvertibleFintypeCard' :
    Invertible ((Fintype.card G : k)) :=
  invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact NeZero.ne _)

/-- Characters add over a direct-sum decomposition: if `V`'s underlying type
splits internally as `⨁ᵢ Nᵢ` with each `Nᵢ` invariant under `V.ρ g`, then
`V.character g` is the sum of the sub-traces.  Foundational helper for
items 4–5 backward, isolating the trace-additivity step before any
multiplicity bookkeeping. -/
theorem character_eq_sum_restrict (V : FDRep k G)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → Submodule k V) (hint : DirectSum.IsInternal N)
    (hinv : ∀ (g : G) (i : ι), Set.MapsTo (V.ρ g) (N i) (N i)) (g : G) :
    V.character g =
      ∑ i, LinearMap.trace k (N i) ((V.ρ g).restrict (hinv g i)) := by
  show LinearMap.trace k V (V.ρ g) = _
  exact LinearMap.trace_eq_sum_trace_restrict hint (hinv g)

/-- Cast-friendly intermediate: for an alg-closed-field representation,
simplicity is equivalent to the equivariant endomorphism algebra being
1-dimensional.  Forward direction is `FDRep.finrank_hom_simple_simple`
(Schur). Backward is `sorry`'d — see plan below. -/
theorem simple_iff_finrank_End_eq_one (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 := by
  refine ⟨fun hV => ?_, fun _h => ?_⟩
  · haveI := hV
    rw [finrank_hom_simple_simple]
    exact if_pos ⟨Iso.refl V⟩
  · -- Backward.  By Maschke `V` is semisimple.  If `V` is not simple, it
    -- decomposes as `V = V₁ ⊕ V₂` with both nonzero, and `End_{k[G]} V`
    -- contains the projector idempotent for each summand, giving at least
    -- two linearly independent endomorphisms — contradicting `dim = 1`.
    sorry

-- The headline corollaries `FDRep.iso_iff_character_eq` (cor:char-separates)
-- and `FDRep.irreducible_iff_inner_self_eq_one` (cor:irred-test) live in
-- `PeterWeyl.Upstream.Characters` (the planned upstream contribution).
-- Both are stated with proper iff signatures; the backward directions are
-- sorry'd pending the FDRep simple-decomposition API in
-- `PeterWeyl.Upstream.Decomposition`.

end

end FDRep

namespace Representation

section
variable {k G : Type u} [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]

/-- Bridge `NeZero (Nat.card G : k) → Invertible (Fintype.card G : k)` so
Mathlib's character-theory lemmas (which use `Invertible`) fire under our
project's standing hypotheses (which use `NeZero`). -/
local instance (priority := 100) instInvertibleFintypeCard :
    Invertible ((Fintype.card G : k)) :=
  invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact NeZero.ne _)

/-- Inner product of characters equals the dimension of the equivariant Hom
space.  When `W` is simple this dimension is the multiplicity of `W` in `V`
(by Schur), so this is the "multiplicity formula" cited in the blueprint
as `thm:multiplicity-formula`.

Reduces directly to `FDRep.scalar_product_char_eq_finrank_equivariant`
(Mathlib). -/
theorem multiplicity_eq_inner_char (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, W.character g * V.character g⁻¹ =
      Module.finrank k (V ⟶ W) :=
  FDRep.scalar_product_char_eq_finrank_equivariant V W

end
end Representation

namespace PeterWeyl

section
variable (k G : Type u) [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]

/-- Module-form Peter–Weyl: the regular representation decomposes as a
finite direct sum of isotypic blocks.  Cited as `thm:peter-weyl-module`.

The signature here is a thin repackaging of Mathlib's
`IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end` applied with
`R := MonoidAlgebra k G` and `M := MonoidAlgebra k G` (the regular
module): we extract the existence of finitely many simple submodules
`Sᵢ` of `MonoidAlgebra k G` together with multiplicities `dᵢ ≠ 0`.

**Proof**: a one-liner once the Mathlib lemma is unfolded; left as
`sorry` here because the full unpacking + repackaging is ~10 lines of
`obtain ⟨n, S, d, hsimp, hd, _⟩ := ...`.  Replace with the body of
that destructure when ready. -/
theorem regular_decomposition :
    ∃ (n : ℕ) (S : Fin n → Submodule (MonoidAlgebra k G) (MonoidAlgebra k G))
      (d : Fin n → ℕ),
      (∀ i, IsSimpleModule (MonoidAlgebra k G) (S i)) ∧ (∀ i, NeZero (d i)) := by
  have ⟨n, S, d, hS, hd, _⟩ :=
    IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end (R₀ := k)
      (MonoidAlgebra k G) (MonoidAlgebra k G)
  exact ⟨n, S, d, hS, hd⟩

end
end PeterWeyl

/-! ## [NEW] items — require genuinely new content (not in Mathlib) -/

namespace FDRep

section
variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

/-- The irreducible characters span the space of class functions.  Cited as
`thm:char-span`.

**Implementation plan** (~50–80 lines once `regular_decomposition` and
`finrank_eq_conjClasses` land):
1. **Inclusion.**  Each irreducible character `χ_V ∈ ClassFunction k G`
   via `FDRep.char_conj`.
2. **Linear independence.**  By `FDRep.char_orthonormal`, distinct
   irreducible characters are orthogonal under
   `⟨φ, ψ⟩ := (1/|G|) ∑_g φ(g) ψ(g⁻¹)`, hence linearly independent.
3. **Counting irreducibles.**  Use `regular_decomposition` plus
   `char_orthonormal` to express the multiplicity of each irreducible
   `Vᵢ` in the regular representation as `dim Vᵢ`.  Cross-checking
   against `|G| = dim k[G] = ∑ᵢ dim²Vᵢ` (already proven in
   `PeterWeyl.sum_sq_dim_eq_card`) confirms the irreducibles are exactly
   the `Vᵢ` appearing in `regular_decomposition`, hence finitely many.
4. **Spanning.**  The orthonormal set of step 2 has cardinality equal to
   `Fintype.card (ConjClasses G) = dim ClassFunction k G` (using
   `finrank_eq_conjClasses` and the fact that an orthonormal set in an
   inner product space of dimension `n` with `n` elements is a basis).
   Hence the span is everything.

Note: step 4 hinges on an inner product / orthogonality lemma that
Mathlib's `FDRep.char_orthonormal` is the algebraic analogue of; we may
need a small bridge lemma `LinearIndependent_of_charOrthonormal`. -/
theorem span_irreducibleCharacters_eq_top : True := True.intro

/-- Number of isomorphism classes of simple `FDRep k G` equals
`#ConjClasses G`.  Cited as `thm:num-irreps`.

**Implementation plan** (one-liner once `span_irreducibleCharacters_eq_top`
lands):
The irreducible characters are orthonormal (step 2 above) and span
(`span_irreducibleCharacters_eq_top`), hence form a basis of
`ClassFunction k G`.  Therefore
`#{simple V} = dim ClassFunction k G = Fintype.card (ConjClasses G)`
by `ClassFunction.finrank_eq_conjClasses`. -/
theorem num_simple_eq_num_conjClasses : True := True.intro

end

end FDRep
