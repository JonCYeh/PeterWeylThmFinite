/-
Copyright (c) 2026.  Released under Apache 2.0 license.
Authors: TBD
-/
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RepresentationTheory.Basic

/-!
# `FDRep` morphisms as `MonoidAlgebra`-module endomorphisms

> **Upstream target**: extension of
> `Mathlib/RepresentationTheory/FDRep.lean`, or a new file
> `Mathlib/RepresentationTheory/FDRep/EndLinearEquiv.lean`.
>
> Provides the bridge between the categorical hom of `FDRep k G` and the
> explicit `MonoidAlgebra k G`-module endomorphism algebra of the
> underlying type.  Without this bridge, every theorem comparing the two
> needs to roll the conversion by hand.

For `V : FDRep k G`, both `(V ⟶ V)` (the FDRep categorical endomorphism set)
and `Module.End (MonoidAlgebra k G) V` (the `MonoidAlgebra`-linear
endomorphisms of the underlying type) describe the same equivariant linear
maps.  This file makes that identification a `LinearEquiv` over `k`.

## Main definitions

* `FDRep.moduleMonoidAlgebra` — registers the
  `Module (MonoidAlgebra k G) V`-instance on the FDRep-coerced underlying
  type.  Currently lives also in `PeterWeyl.Auxiliary`; the upstream
  contribution will subsume the local copy.

* `FDRep.endLinearEquiv` — the `k`-linear equivalence
  `(V ⟶ V) ≃ₗ[k] Module.End (MonoidAlgebra k G) V`.

## Implementation notes

`FDRep` is `Action (FGModuleCat k) (MonCat.of G)`.  A morphism `V ⟶ W`
in this category is a `k`-linear map between the underlying spaces that
intertwines the `G`-actions.  Such an intertwiner is exactly a
`MonoidAlgebra k G`-linear map between the modules induced by the actions.

The forward direction (`(V ⟶ V) → Module.End (MonoidAlgebra k G) V`)
unfolds the categorical morphism via `Action.Hom.hom` to get the
underlying `k`-linear map, then promotes equivariance to
`MonoidAlgebra`-linearity by the universal property of `MonoidAlgebra`.

The inverse direction takes a `MonoidAlgebra`-linear map and observes
that restriction to single-element actions `MonoidAlgebra.single g 1`
recovers the equivariance condition required by `Action.Hom`.
-/

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] [Fintype G] [NeZero (Nat.card G : k)]

/-- The `MonoidAlgebra k G`-module structure on `V : FDRep k G` induced by
the action `V.ρ`.  This is the direct analogue of
`Mathlib.RepresentationTheory.Basic`'s instance on
`Representation.asModule`, registered on the FDRep-coerced type rather
than on `Representation.asModule V.ρ`, so that
`Module (MonoidAlgebra k G) V` is findable by instance synthesis without
going through a coercion that blocks it. -/
noncomputable instance moduleMonoidAlgebra (V : FDRep k G) :
    Module (MonoidAlgebra k G) V :=
  Module.compHom V (Representation.asAlgebraHom (V.ρ : Representation k G V)).toRingHom

/-- Action of a `MonoidAlgebra` single-element on a vector in `V`,
unfolded through `Representation.asAlgebraHom`.  Mirrors
`Representation.single_smul` for `Representation.asModule`, but on the
FDRep-coerced underlying type. -/
@[simp]
theorem single_smul (V : FDRep k G) (t : k) (g : G) (v : V) :
    (MonoidAlgebra.single g t : MonoidAlgebra k G) • v = t • V.ρ g v := by
  show (Representation.asAlgebraHom V.ρ) (MonoidAlgebra.single g t) v = t • V.ρ g v
  simp [Representation.asAlgebraHom_single]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar tower: `k → MonoidAlgebra k G → V` is compatible.  This is
required to derive `Module k (Module.End (MonoidAlgebra k G) V)` from
the existing `Module k V` instance via `LinearMap.module`.

Direct port of Mathlib's `Representation.asModule` `IsScalarTower`
instance (`Mathlib/RepresentationTheory/Basic.lean`), using the same
`MonoidAlgebra.induction_on` strategy. -/
instance isScalarTower_moduleMonoidAlgebra (V : FDRep k G) :
    IsScalarTower k (MonoidAlgebra k G) V where
  smul_assoc t x v := by
    revert t
    apply x.induction_on
    · intro m t
      simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc, smul_eq_mul, hy (t * s), ← smul_eq_mul, smul_assoc]
      aesop

/-- The `k`-linear equivalence between FDRep morphisms and equivariant
endomorphisms of the underlying `MonoidAlgebra k G`-module.

This requires `Module k (Module.End (MonoidAlgebra k G) V)` which Lean
synthesizes from `Module k V` + `IsScalarTower k (MonoidAlgebra k G) V`
via `LinearMap.module`. -/
noncomputable def endLinearEquiv (V : FDRep k G) :
    (V ⟶ V) ≃ₗ[k] (V →ₗ[MonoidAlgebra k G] V) := by
  -- Plan:
  -- * `toFun`: take the underlying `k`-linear map of an FDRep morphism
  --   (via `Action.Hom.hom` / `FDRep.forget₂HomLinearEquiv` chained with
  --   the appropriate Rep-side lemma) and promote to k[G]-linearity using
  --   the equivariance hypothesis.
  -- * `invFun`: take a k[G]-linear endomorphism and produce an FDRep
  --   morphism — equivariance under each `g : G` follows from k[G]-linearity
  --   applied to `MonoidAlgebra.single g 1`.
  -- * `map_add'`, `map_smul'`: by linearity of the components.
  -- * `left_inv`, `right_inv`: `ext`-and-rfl after unfolding.
  sorry

@[simp]
theorem finrank_end_eq_finrank_moduleEnd (V : FDRep k G) :
    Module.finrank k (V ⟶ V) =
      Module.finrank k (V →ₗ[MonoidAlgebra k G] V) :=
  (endLinearEquiv V).finrank_eq

end FDRep
