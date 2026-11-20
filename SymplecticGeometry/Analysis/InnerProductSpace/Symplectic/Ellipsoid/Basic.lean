/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Standard ellipsoids

For radii `r : ι → ℝ`, the standard ellipsoid `E(r) ⊆ ℝ²ⁿ` is
`{z | ∑ⱼ (xⱼ² + yⱼ²) / rⱼ² ≤ 1}`, the sublevel set of a diagonal quadratic form. Every
ellipsoid centred at `0` is carried to one of these by a linear symplectic map
(`SymplecticGeometry.exists_isSymplectomorphism_image_eq_stdEllipsoid`).

## Main definitions

* `SymplecticGeometry.stdEllipsoidForm r`: the quadratic form `∑ⱼ (xⱼ² + yⱼ²) / rⱼ²` on
  `StdSpace ι`.
* `SymplecticGeometry.stdEllipsoid r`: its sublevel set `{z | stdEllipsoidForm r z ≤ 1}`.

## Main results

* `SymplecticGeometry.stdEllipsoidForm_posDef`: the form is positive definite when no radius
  is `0`.
* `SymplecticGeometry.closedBall_subset_stdEllipsoid`: the ellipsoid contains the closed ball
  whose radius is its smallest radius.
* `SymplecticGeometry.stdEllipsoid_eq_image_closedBall`: for positive radii, `E(r)` is the image
  of the closed unit ball under the diagonal map `(xⱼ, yⱼ) ↦ (rⱼ xⱼ, rⱼ yⱼ)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
-/

public section

namespace SymplecticGeometry

open Metric StdSpace

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `∑ⱼ (xⱼ² + yⱼ²) / rⱼ²` on `StdSpace ι`: the weighted sum of squares with
weight `rⱼ⁻²` on both coordinates `xⱼ` and `yⱼ`. -/
noncomputable def stdEllipsoidForm (r : ι → ℝ) : QuadraticForm ℝ (StdSpace ι) :=
  (QuadraticMap.weightedSumSquares ℝ (Sum.elim (fun j ↦ (r j)⁻¹ ^ 2) fun j ↦ (r j)⁻¹ ^ 2)).comp
    (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap

theorem stdEllipsoidForm_def (r : ι → ℝ) :
    stdEllipsoidForm r =
      (QuadraticMap.weightedSumSquares ℝ
        (Sum.elim (fun j ↦ (r j)⁻¹ ^ 2) fun j ↦ (r j)⁻¹ ^ 2)).comp
        (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).toLinearMap :=
  (rfl)

/-- `stdEllipsoidForm r z = ∑ⱼ (xⱼ² + yⱼ²) / rⱼ²`. -/
@[simp]
theorem stdEllipsoidForm_apply (r : ι → ℝ) (z : StdSpace ι) :
    stdEllipsoidForm r z = ∑ j, (z.x j ^ 2 + z.y j ^ 2) / r j ^ 2 := by
  simp only [stdEllipsoidForm_def, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [div_eq_inv_mul]
  ring

/-- `stdEllipsoidForm r` is positive definite when no radius is `0`. -/
theorem stdEllipsoidForm_posDef {r : ι → ℝ} (hr : ∀ j, r j ≠ 0) :
    (stdEllipsoidForm r).PosDef := by
  refine (EuclideanSpace.posDef_iff_of_forall_eq_sum_mul_sq
    (w := Sum.elim (fun j ↦ (r j)⁻¹ ^ 2) fun j ↦ (r j)⁻¹ ^ 2) fun z ↦ ?_).2 ?_
  · simp only [stdEllipsoidForm_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Sum.elim_inl, Sum.elim_inr, x_apply, y_apply]
    field_simp
  · rintro (j | j) <;> exact sq_pos_of_ne_zero (inv_ne_zero (hr j))

/-- The standard ellipsoid `E(r) = {z | ∑ⱼ (xⱼ² + yⱼ²) / rⱼ² ≤ 1}`. -/
def stdEllipsoid (r : ι → ℝ) : Set (StdSpace ι) :=
  {z | stdEllipsoidForm r z ≤ 1}

theorem stdEllipsoid_def (r : ι → ℝ) : stdEllipsoid r = {z | stdEllipsoidForm r z ≤ 1} :=
  (rfl)

@[simp]
theorem mem_stdEllipsoid_iff {r : ι → ℝ} {z : StdSpace ι} :
    z ∈ stdEllipsoid r ↔ ∑ j, (z.x j ^ 2 + z.y j ^ 2) / r j ^ 2 ≤ 1 := by
  rw [stdEllipsoid_def, Set.mem_ofPred_eq, stdEllipsoidForm_apply]

/-- The squared norm of a point of the standard model in coordinates. -/
private theorem norm_sq_eq_sum (z : StdSpace ι) : ‖z‖ ^ 2 = ∑ j, (z.x j ^ 2 + z.y j ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  simp [sq]

/-- If `r i` is a smallest radius and is positive, the ellipsoid `E(r)` contains the closed ball
of radius `r i`. -/
theorem closedBall_subset_stdEllipsoid {r : ι → ℝ} {i : ι} (hi : 0 < r i)
    (hmin : ∀ j, r i ≤ r j) : closedBall 0 (r i) ⊆ stdEllipsoid r := by
  intro z hz
  have hz' : ‖z‖ ^ 2 ≤ r i ^ 2 := by
    rw [mem_closedBall_zero_iff] at hz
    exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [mem_stdEllipsoid_iff]
  calc ∑ j, (z.x j ^ 2 + z.y j ^ 2) / r j ^ 2
      ≤ ∑ j, (z.x j ^ 2 + z.y j ^ 2) / r i ^ 2 := by
        gcongr with j
        exact hmin j
    _ = ‖z‖ ^ 2 / r i ^ 2 := by rw [norm_sq_eq_sum, Finset.sum_div]
    _ ≤ 1 := (div_le_one (by positivity)).2 hz'

variable [DecidableEq ι]

/-- For positive radii, the ellipsoid `E(r)` is the image of the closed unit ball under the
diagonal map `(xⱼ, yⱼ) ↦ (rⱼ xⱼ, rⱼ yⱼ)`. -/
theorem stdEllipsoid_eq_image_closedBall {r : ι → ℝ} (hr : ∀ j, 0 < r j) :
    stdEllipsoid r =
      Matrix.toEuclideanLin (Matrix.diagonal (Sum.elim r r)) '' closedBall 0 1 := by
  have hr' (j : ι) : r j ≠ 0 := (hr j).ne'
  let D (s : ι → ℝ) : StdSpace ι →ₗ[ℝ] StdSpace ι :=
    Matrix.toEuclideanLin (Matrix.diagonal (Sum.elim s s))
  have hD (s : ι → ℝ) (z : StdSpace ι) (k : ι ⊕ ι) : D s z k = Sum.elim s s k * z k := by
    simp [D, Matrix.ofLp_toLpLin, Matrix.mulVec_diagonal]
  have hinv (z : StdSpace ι) : D r (D r⁻¹ z) = z := by
    refine PiLp.ext fun k ↦ ?_
    rcases k with j | j <;> simp [hD, hr' j]
  have hinv' (z : StdSpace ι) : D r⁻¹ (D r z) = z := by
    refine PiLp.ext fun k ↦ ?_
    rcases k with j | j <;> simp [hD, hr' j]
  change _ = D r '' _
  rw [Set.image_eq_preimage_of_inverse (f := D r) (g := D r⁻¹) hinv' hinv]
  ext z
  rw [mem_stdEllipsoid_iff, Set.mem_preimage, mem_closedBall_zero_iff,
    ← sq_le_one_iff₀ (norm_nonneg _), norm_sq_eq_sum]
  refine iff_of_eq (congrArg (· ≤ 1) (Finset.sum_congr rfl fun j _ ↦ ?_))
  simp only [x_apply, y_apply, hD, Sum.elim_inl, Sum.elim_inr, Pi.inv_apply]
  field_simp

end SymplecticGeometry

end
