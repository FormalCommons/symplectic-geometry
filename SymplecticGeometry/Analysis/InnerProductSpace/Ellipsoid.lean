/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Ellipsoids in a real inner product space

An ellipsoid centred at `0` in a real inner product space `V` of finite dimension can be given
in two ways: as the sublevel set `{v | Q v ≤ 1}` of a positive definite quadratic form `Q`, or
as the image of a closed ball centred at `0` under a linear isomorphism. This file shows that
the two descriptions agree.

## Main results

* `LinearEquiv.exists_posDef_image_closedBall_eq`: the image of `closedBall 0 r`, `0 < r`,
  under a linear equivalence is `{v | Q v ≤ 1}` for a positive definite `Q`, namely
  `Q v = ‖e⁻¹ v‖² / r²`.
* `QuadraticMap.PosDef.exists_linearEquiv_image_closedBall_eq`: conversely, for `Q` positive
  definite, `{v | Q v ≤ 1}` is the image of `closedBall 0 1` under a linear equivalence.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
-/

public section

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- The image of the closed ball of radius `r > 0` under a linear equivalence `e` is the
sublevel set `{v | Q v ≤ 1}` of a positive definite quadratic form `Q`, namely
`Q v = ‖e.symm v‖² / r²`. -/
theorem LinearEquiv.exists_posDef_image_closedBall_eq (e : E ≃ₗ[ℝ] F) {r : ℝ} (hr : 0 < r) :
    ∃ Q : QuadraticForm ℝ F, Q.PosDef ∧ e '' closedBall 0 r = {v | Q v ≤ 1} := by
  let Q₀ : QuadraticForm ℝ E := (r⁻¹ ^ 2) • LinearMap.BilinMap.toQuadraticMap (innerₗ E)
  have hQ₀ (v : E) : Q₀ v = ‖v‖ ^ 2 / r ^ 2 := by
    simp [Q₀, LinearMap.BilinMap.toQuadraticMap_apply,
      div_eq_inv_mul]
  refine ⟨Q₀.comp (e.symm : F →ₗ[ℝ] E), fun v hv ↦ ?_, ?_⟩
  · have : e.symm v ≠ 0 := by simpa using hv
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, hQ₀]
    positivity
  · rw [← QuadraticMap.image_setOfPred_le_one]
    congr 1
    ext v
    simp [hQ₀, div_le_one (by positivity : 0 < r ^ 2), sq_le_sq₀ (norm_nonneg v) hr.le]

variable [FiniteDimensional ℝ E]

/-- The sublevel set `{v | Q v ≤ 1}` of a positive definite quadratic form on a real inner
product space of finite dimension is the image of the closed unit ball under a linear
equivalence. -/
theorem QuadraticMap.PosDef.exists_linearEquiv_image_closedBall_eq {Q : QuadraticForm ℝ E}
    (hQ : Q.PosDef) : ∃ e : E ≃ₗ[ℝ] E, {v | Q v ≤ 1} = e '' closedBall 0 1 := by
  obtain ⟨φ⟩ := TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
  -- `g` carries `Q` to the squared norm.
  let g : E ≃ₗ[ℝ] E := φ.toLinearEquiv.trans
    ((WithLp.linearEquiv 2 ℝ _).symm.trans (stdOrthonormalBasis ℝ E).repr.symm.toLinearEquiv)
  have hg (v : E) : ‖g v‖ ^ 2 = Q v := by
    rw [← φ.map_app v]
    simp only [g, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
    simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, pow_two]
  refine ⟨g.symm, ?_⟩
  rw [g.symm.image_eq_preimage_symm]
  ext v
  simp [← hg, sq_le_one_iff₀ (norm_nonneg _)]
