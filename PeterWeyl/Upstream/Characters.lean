/-
Copyright (c) 2026.  Released under Apache 2.0 license.
Authors: TBD
-/
import PeterWeyl.Upstream.Decomposition

/-!
# Headline character-theoretic corollaries

> **Upstream target**: extension of
> `Mathlib/RepresentationTheory/Character.lean`, building on the new
> `Mathlib/RepresentationTheory/Decomposition.lean`.
>
> Once `FDRep.SimpleDecomp` and its `mult_eq_inner_char` are in place,
> the two headline statements (characters separate iso-classes;
> simplicity ↔ unit self-inner-product) are short corollaries.

## Main results

* `FDRep.iso_iff_character_eq` — `V ≅ W` iff `V.character = W.character`.

* `FDRep.irreducible_iff_inner_self_eq_one` — `V` is simple iff
  `⅟|G| ∑ χ_V(g) χ_V(g⁻¹) = 1`.  Requires `[CharZero k]` for the cast
  `(n : k) = 1 ↔ n = 1` step in the backward direction; in
  characteristic-`p` settings the statement may need to be reformulated
  in terms of `Module.finrank k (V ⟶ V) = 1` directly.

## Implementation notes

* The forward directions are short:
  - `iso_iff_character_eq` ⇒: `FDRep.char_iso`.
  - `irreducible_iff_inner_self_eq_one` ⇒: `FDRep.char_orthonormal V V` plus
    `Iso.refl V` to collapse the conditional.

* The backward directions both reduce to reading off multiplicities from
  the inner product via `SimpleDecomp.mult_eq_inner_char`:
  - For iso: equal characters ⇒ equal multiplicities for every simple
    class ⇒ matching `SimpleDecomp` data ⇒ iso (using the biproduct
    decomposition iso of each side).
  - For simplicity: `⟨χ_V, χ_V⟩ = ∑ᵢ (mult i)²`; equals `1` (in `ℕ` via
    the cast) plus `mult_pos` forces `|ι| = 1` and `mult i = 1`,
    yielding `V ≅ S i₀` simple.
-/

open CategoryTheory

namespace FDRep

universe u

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

local instance (priority := 100) instInvertibleFintypeCard''' :
    Invertible ((Fintype.card G : k)) :=
  invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact NeZero.ne _)

/-- Characters separate isomorphism classes of finite-dimensional
representations.  See the file's module docstring for the plan. -/
theorem iso_iff_character_eq (V W : FDRep k G) :
    Nonempty (V ≅ W) ↔ V.character = W.character := by
  refine ⟨fun ⟨φ⟩ => char_iso φ, fun _hχ => ?_⟩
  -- Plan:
  -- * Build `DV : SimpleDecomp V` and `DW : SimpleDecomp W`.
  -- * From character equality + `mult_eq_inner_char` on each side, the
  --   multiplicities of every simple class agree.
  -- * Use the iso witness in each `SimpleDecomp` to assemble `V ≅ W`.
  sorry

/-- Irreducibility test: `V : FDRep k G` is simple iff its self-inner
product is `1` in `k`.  See the file's module docstring for the plan. -/
theorem irreducible_iff_inner_self_eq_one [CharZero k] (V : FDRep k G) :
    Simple V ↔
      ⅟(Fintype.card G : k) • ∑ g : G, V.character g * V.character g⁻¹ = 1 := by
  refine ⟨fun hV => ?_, fun _h => ?_⟩
  · haveI := hV
    have hco := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at hco
    exact_mod_cast hco
  -- Backward plan:
  -- * `D := SimpleDecomp V`.
  -- * `character_eq` + `char_orthonormal` give `⟨χ_V, χ_V⟩ = ∑ᵢ (mult i)²`
  --   (in `k`).
  -- * `[CharZero k]` lets us promote that to `∑ (mult i)² = 1` in `ℕ`.
  -- * With `mult_pos`, this forces `|D.ι| = 1` and `D.mult ⟨..⟩ = 1`.
  -- * `D.iso` then witnesses `V ≅ D.S i₀` for that single index, hence
  --   `Simple V` by transport along the iso.
  sorry

end FDRep
