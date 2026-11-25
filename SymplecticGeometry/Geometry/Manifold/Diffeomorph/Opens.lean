/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Open subsets of open subsets

Let `W` be an open subset of a manifold `M`, `T` an open subset of the manifold `W`, and `S ≤ W`
an open subset of `M` with the same points as `T`. This file shows that the two open submanifolds
`T` and `S` are diffeomorphic through the identity on points (`Diffeomorph.subtypeSubtype`).

This is the smooth form of Mathlib's `Equiv.subtypeSubtypeEquivSubtype`, for open subsets.

## Main definitions

* `Diffeomorph.subtypeSubtype`: the diffeomorphism `T ≃ₘ^n⟮I, I⟯ S` between an open subset `T` of
  `W` and the open subset `S ≤ W` of `M` with the same points.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- An open subset `T` of an open subset `W` of `M` is diffeomorphic to the open subset `S ≤ W`
of `M` with the same points, through the identity on points. -/
def subtypeSubtype {W S : Opens M} (T : Opens W) (hS : S ≤ W)
    (hT : ∀ x : W, x ∈ T ↔ (x : M) ∈ S) : T ≃ₘ^n⟮I, I⟯ S where
  toFun x := ⟨x.val, (hT x).1 x.property⟩
  invFun y := ⟨⟨y, hS y.property⟩, (hT _).2 y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff S _).1 ?_
    exact (contMDiff_subtypeVal.comp contMDiff_subtypeVal :
      ContMDiff I I n fun x : T ↦ ((x : W) : M))
  contMDiff_invFun := by
    refine (TauCeti.ContMDiff.subtypeVal_comp_iff T _).1
      ((TauCeti.ContMDiff.subtypeVal_comp_iff W _).1 ?_)
    exact contMDiff_subtypeVal

variable {W S : Opens M} {T : Opens W} {hS : S ≤ W} {hT : ∀ x : W, x ∈ T ↔ (x : M) ∈ S}

/-- The diffeomorphism `Diffeomorph.subtypeSubtype` is the identity on points of `M`. -/
@[simp]
theorem coe_subtypeSubtype_apply (x : T) :
    (subtypeSubtype (I := I) (n := n) T hS hT x : M) = ((x : W) : M) :=
  (rfl)

/-- The inverse of `Diffeomorph.subtypeSubtype` is the identity on points of `M`. -/
@[simp]
theorem coe_coe_subtypeSubtype_symm_apply (y : S) :
    (((subtypeSubtype (I := I) (n := n) T hS hT).symm y : W) : M) = y :=
  (rfl)

end Diffeomorph
