/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The orientation of the area form of a torus of circles

For positive periods `p` and `q`, the area form `ds_p ∧ dt_q` of `AddCircle p × AddCircle q`, the
wedge of the time forms of the two factors, takes the value `1` on the standard frame
`((1, 0), (0, 1))` of every tangent plane (`AddCircle.wedge_timeForm_apply_finTwoProd`), so it
vanishes nowhere (`AddCircle.wedge_timeForm_apply_ne_zero`). Its orientation
`Manifold.Orientation.ofTopForm` is the product of the positive orientations of the two circles
(`AddCircle.orientation_prod_orientation_eq_ofTopForm`), since Tau Ceti's
`AddCircle.orientationAt_orientation_prod_orientation` shows that the standard frame is positive
for that product.

## Main results

* `AddCircle.wedge_timeForm_apply_finTwoProd`: `ds_p ∧ dt_q` is `1` on the standard frame.
* `AddCircle.wedge_timeForm_apply_ne_zero`: `ds_p ∧ dt_q` vanishes nowhere.
* `AddCircle.orientation_prod_orientation_eq_ofTopForm`: the product orientation of the two
  circles is the orientation of `ds_p ∧ dt_q`.
-/

public section

open scoped Manifold ContDiff

namespace AddCircle

open TauCeti

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- The area form `ds_p ∧ dt_q` of `AddCircle p × AddCircle q` takes the value `1` on the standard
frame `((1, 0), (0, 1))` of each tangent plane. -/
theorem wedge_timeForm_apply_finTwoProd (x : AddCircle p × AddCircle q) :
    (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (timeForm p))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm q))).val x
        (Module.Basis.finTwoProd ℝ) = 1 := by
  rw [Module.Basis.coe_finTwoProd]
  refine (SmoothBundleForm.eval₂_apply _ x _ _).symm.trans ?_
  -- The tangent planes of the torus are `ℝ × ℝ`, so the frame is stated in the model.
  exact (eval₂_wedge_timeForm p q x _ _).trans (by norm_num)

/-- The area form `ds_p ∧ dt_q` of `AddCircle p × AddCircle q` vanishes nowhere. -/
theorem wedge_timeForm_apply_ne_zero (x : AddCircle p × AddCircle q) :
    (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (timeForm p))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm q))).val x ≠ 0 := fun h ↦
  one_ne_zero <| (wedge_timeForm_apply_finTwoProd p q x).symm.trans
    ((congrFun (congrArg DFunLike.coe h) _).trans (congrFun ContinuousAlternatingMap.coe_zero _))

/-- The product of the positive orientations of the circles `AddCircle p` and `AddCircle q` is the
orientation of the area form `ds_p ∧ dt_q`, on which that form is positive. -/
theorem orientation_prod_orientation_eq_ofTopForm :
    (AddCircle.orientation p).prod (AddCircle.orientation q) =
      Manifold.Orientation.ofTopForm (by simp)
        (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (timeForm p))
          (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm q))).val
        ((SmoothForm.isSmoothForm _).of_le zero_le) (wedge_timeForm_apply_ne_zero p q) :=
  Manifold.Orientation.ext fun x ↦ by
    rw [orientationAt_orientation_prod_orientation]
    exact (Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ _).2
      ((wedge_timeForm_apply_finTwoProd p q x).symm ▸ one_pos)

end AddCircle

end
