/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import SymplecticGeometry.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Following a chart into a normed space by an affine map

For a smooth partial diffeomorphism `φ` from a manifold `M` into a real normed space `G`, a point
`p : G` and a continuous linear automorphism `A` of `G`, the chart `φ.transAffine p A` is `φ`
followed by the affine diffeomorphism `z ↦ A (z - p)` of `G`: first the translation by `-p`, then
`A`. When `p` is in the target of `φ`, the new chart sends `φ.symm p` to `0`, so this is how a
chart is recentred at a point and normalized by a linear map.

## Main declarations

* `PartialDiffeomorph.transAffine`: the chart `φ` followed by `z ↦ A (z - p)`.
* `PartialDiffeomorph.transAffine_source`, `PartialDiffeomorph.transAffine_apply`,
  `PartialDiffeomorph.transAffine_symm_apply`, `PartialDiffeomorph.mem_transAffine_target_iff`
  and `PartialDiffeomorph.transAffine_target`: its source, values, inverse and target.
* `PartialDiffeomorph.transAffine_apply_symm_apply_self`: the new chart vanishes at `φ.symm p`.
* `PartialDiffeomorph.transSubRight`: the translation step alone, `φ` followed by Tau Ceti's
  `Diffeomorph.smulAdd ∞ 1 (-p)`, which is `z ↦ z - p`, with
  `PartialDiffeomorph.mvfderiv_transSubRight`: it has the derivative of `φ`.
-/

public section

open scoped Manifold ContDiff

namespace PartialDiffeomorph

variable {E H M G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The smooth partial diffeomorphism `φ` followed by the translation `z ↦ z - p` of `G`, as a
smooth partial diffeomorphism. This is the first step of `transAffine`. -/
noncomputable def transSubRight (φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (p : G) :
    PartialDiffeomorph I 𝓘(ℝ, G) M G ∞ :=
  φ.trans (Diffeomorph.smulAdd ∞ (1 : ℝ) (-p) one_ne_zero).toPartialDiffeomorph

/-- The smooth partial diffeomorphism `φ` followed by the affine map `z ↦ A (z - p)` of `G`. -/
noncomputable def transAffine (φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (p : G) (A : G ≃L[ℝ] G) :
    PartialDiffeomorph I 𝓘(ℝ, G) M G ∞ :=
  (φ.transSubRight p).trans A.toDiffeomorph.toPartialDiffeomorph

variable (φ : PartialDiffeomorph I 𝓘(ℝ, G) M G ∞) (p : G) (A : G ≃L[ℝ] G)

theorem transSubRight_def :
    φ.transSubRight p =
      φ.trans (Diffeomorph.smulAdd ∞ (1 : ℝ) (-p) one_ne_zero).toPartialDiffeomorph :=
  (rfl)

theorem transAffine_def :
    φ.transAffine p A = (φ.transSubRight p).trans A.toDiffeomorph.toPartialDiffeomorph :=
  (rfl)

@[simp]
theorem transSubRight_source : (φ.transSubRight p).source = φ.source := by
  simp [transSubRight]

@[simp]
theorem transSubRight_apply (y : M) : φ.transSubRight p y = φ y - p := by
  simp [transSubRight, sub_eq_add_neg]

theorem transSubRight_symm_apply (z : G) : (φ.transSubRight p).symm z = φ.symm (z + p) := by
  simp [transSubRight, sub_eq_add_neg]

/-- The form of `transSubRight_symm_apply` that `simp` uses, since `simp` writes the inverse of a
partial diffeomorphism through its underlying partial equivalence. -/
@[simp]
theorem transSubRight_toPartialEquiv_symm_apply (z : G) :
    (φ.transSubRight p).toPartialEquiv.symm z = φ.toPartialEquiv.symm (z + p) := by
  simp [transSubRight, sub_eq_add_neg]

@[simp]
theorem mem_transSubRight_target_iff {z : G} :
    z ∈ (φ.transSubRight p).target ↔ z + p ∈ φ.target := by
  simp [transSubRight, sub_eq_add_neg]

@[simp]
theorem transAffine_source : (φ.transAffine p A).source = φ.source := by
  simp [transAffine]

@[simp]
theorem transAffine_apply (y : M) : φ.transAffine p A y = A (φ y - p) := by
  simp [transAffine, sub_eq_add_neg]

theorem transAffine_symm_apply (z : G) :
    (φ.transAffine p A).symm z = φ.symm (A.symm z + p) := by
  simp [transAffine, transSubRight, sub_eq_add_neg]

/-- The form of `transAffine_symm_apply` that `simp` uses, since `simp` writes the inverse of a
partial diffeomorphism through its underlying partial equivalence. -/
@[simp]
theorem transAffine_toPartialEquiv_symm_apply (z : G) :
    (φ.transAffine p A).toPartialEquiv.symm z = φ.toPartialEquiv.symm (A.symm z + p) := by
  simp [transAffine, transSubRight, sub_eq_add_neg]

@[simp]
theorem mem_transAffine_target_iff {z : G} :
    z ∈ (φ.transAffine p A).target ↔ A.symm z + p ∈ φ.target := by
  simp [transAffine, transSubRight, sub_eq_add_neg]

/-- The target of `φ.transAffine p A` is the image of the target of `φ` under
`z ↦ A (z - p)`. -/
theorem transAffine_target :
    (φ.transAffine p A).target = (fun z ↦ A (z - p)) '' φ.target := by
  ext z
  rw [mem_transAffine_target_iff]
  constructor
  · exact fun h ↦ ⟨_, h, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

/-- When `p` is in the target of `φ`, the chart `φ.transAffine p A` sends `φ.symm p` to `0`. -/
theorem transAffine_apply_symm_apply_self (hp : p ∈ φ.target) :
    φ.transAffine p A (φ.symm p) = 0 := by
  simp [φ.right_inv hp]

/-- The derivative of `φ.transSubRight p` is that of `φ`, at every point. -/
theorem mvfderiv_transSubRight (y : M) :
    mvfderiv I (φ.transSubRight p) y = mvfderiv I φ y := by
  rw [show ⇑(φ.transSubRight p) = fun y ↦ φ y - p from funext (φ.transSubRight_apply p),
    mvfderiv_sub_const]

/-- The derivative of `φ.transAffine p A` is `A` composed with the derivative of `φ`, at
every point. -/
theorem mvfderiv_transAffine (y : M) :
    mvfderiv I (φ.transAffine p A) y = A.toContinuousLinearMap.comp (mvfderiv I φ y) := by
  ext v
  rw [show ⇑(φ.transAffine p A) = ⇑A ∘ ⇑(φ.transSubRight p) from
      funext fun y ↦ by simp, A.mvfderiv_comp_apply,
    φ.mvfderiv_transSubRight p y, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

end PartialDiffeomorph

end
