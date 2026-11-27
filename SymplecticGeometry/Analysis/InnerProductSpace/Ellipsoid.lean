/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.QuadraticForm.Real
import SymplecticGeometry.LinearAlgebra.QuadraticForm.PosDef

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
* `QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace`: a positive definite form
  `Q` on a real normed space of dimension `n` satisfies `Q (L u) = ‖u‖ ^ 2` for a continuous
  linear equivalence `L` from `EuclideanSpace ℝ (Fin n)`; the second result follows from it.

## Implementation notes

The Euclidean coordinate is Tau Ceti's
`TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef`, which makes a positive definite
form isometric to the sum of squares, read on `EuclideanSpace ℝ (Fin n)`.

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

/-- **A positive definite form is a Euclidean norm.** A positive definite quadratic form `Q` on
a real normed space `V` of dimension `n` is the squared norm of `EuclideanSpace ℝ (Fin n)`
carried over by a continuous linear equivalence: `Q (L u) = ‖u‖ ^ 2`. -/
theorem QuadraticMap.PosDef.exists_continuousLinearEquiv_euclideanSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : Q.PosDef) {n : ℕ} (hn : Module.finrank ℝ V = n) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] V, ∀ u, Q (L u) = ‖u‖ ^ 2 := by
  subst hn
  obtain ⟨φ⟩ := TauCeti.nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
  refine ⟨((WithLp.linearEquiv 2 ℝ _).trans φ.symm.toLinearEquiv).toContinuousLinearEquiv,
    fun u ↦ ?_⟩
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply,
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
  rw [φ.symm.map_app, EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct, pow_two]

variable [FiniteDimensional ℝ E]

/-- The sublevel set `{v | Q v ≤ 1}` of a positive definite quadratic form on a real inner
product space of finite dimension is the image of the closed unit ball under a linear
equivalence. -/
theorem QuadraticMap.PosDef.exists_linearEquiv_image_closedBall_eq {Q : QuadraticForm ℝ E}
    (hQ : Q.PosDef) : ∃ e : E ≃ₗ[ℝ] E, {v | Q v ≤ 1} = e '' closedBall 0 1 := by
  obtain ⟨L, hL⟩ := hQ.exists_continuousLinearEquiv_euclideanSpace rfl
  -- `g` carries the squared norm to `Q`.
  let g : E ≃ₗ[ℝ] E := (stdOrthonormalBasis ℝ E).repr.toLinearEquiv ≪≫ₗ L.toLinearEquiv
  have hg (v : E) : Q (g v) = ‖v‖ ^ 2 := by
    simpa [g] using hL ((stdOrthonormalBasis ℝ E).repr v)
  refine ⟨g, ?_⟩
  rw [g.image_eq_preimage_symm]
  ext v
  obtain ⟨w, rfl⟩ := g.surjective v
  simp [hg, sq_le_one_iff₀ (norm_nonneg _)]
