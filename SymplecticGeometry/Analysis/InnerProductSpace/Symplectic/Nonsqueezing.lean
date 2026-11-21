/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.AffineSymplectic

/-!
# Affine nonsqueezing

An affine symplectic map of the standard model `ℝ²ⁿ` cannot send the closed ball `B²ⁿ(r)` into
a cylinder `Z(R)` over a disc of radius `R < r`.

* `SymplecticGeometry.le_of_image_closedBall_subset_stdCylinder`: the statement for an element
  of `SymplecticGeometry.affineSymplecticGroup (stdForm ι)`.
* `SymplecticGeometry.le_of_mem_symplecticGroup_of_image_closedBall_subset_stdCylinder`: the
  same for the map `z ↦ A z + z₀` of a symplectic matrix `A`.

The radius `r` of the ball is assumed nonnegative: a ball of negative radius is empty, and lies
in every cylinder.

The proof follows McDuff–Salamon, Theorem 2.4.1. Let `e` be the linear part of the map and
`u`, `v` the images of the unit vectors in the `xᵢ` and `yᵢ` directions under the adjoint of
`e`. The adjoint is again symplectic, so `ω₀(u, v) = 1`, and Cauchy–Schwarz for `ω₀` gives
`1 ≤ ‖u‖ ‖v‖`. The `xᵢ`-coordinate of the image of `z` is `⟪z, u⟫` plus a constant, and on
the ball `⟪z, u⟫` takes the values `±r ‖u‖`; so the cylinder's radius is at least `r ‖u‖`, and
likewise at least `r ‖v‖`. Since one of `‖u‖`, `‖v‖` is at least `1`, `r ≤ R`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

open TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the coordinate `c` of an affine map of `StdSpace ι` is bounded by `R` on the closed ball
of radius `r ≥ 0`, then `r ‖w‖ ≤ R`, where `w` is the image of the unit vector at `c` under the
adjoint of the linear part. -/
private theorem mul_norm_adjoint_le [DecidableEq ι] {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    {c : ι ⊕ ι} {r R : ℝ}
    (hr : 0 ≤ r) (h : ∀ z ∈ Metric.closedBall (0 : StdSpace ι) r, |f z c| ≤ R) :
    r * ‖ContinuousLinearEquiv.adjointEquiv f.linear.toContinuousLinearEquiv
      (EuclideanSpace.single c 1)‖ ≤ R := by
  set w := ContinuousLinearEquiv.adjointEquiv f.linear.toContinuousLinearEquiv
    (EuclideanSpace.single c 1)
  have hf : ∀ z, f z c = inner ℝ z w + f 0 c := by
    intro z
    have hz : f z = f.linear z + f 0 := congr_fun f.toAffineMap.decomp z
    have hw : inner ℝ z w = inner ℝ (f.linear z) (EuclideanSpace.single c (1 : ℝ)) := by
      simp only [w, ContinuousLinearEquiv.adjointEquiv_apply,
        ContinuousLinearMap.adjoint_inner_right]
      rfl
    rw [hz, PiLp.add_apply, hw, EuclideanSpace.inner_single_right]
    simp
  have h0 := h 0 (Metric.mem_closedBall_self hr)
  by_cases hw : w = 0
  · rw [hw, norm_zero, mul_zero]
    exact (abs_nonneg _).trans h0
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  set z := (r / ‖w‖) • w
  have hz : z ∈ Metric.closedBall (0 : StdSpace ι) r := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hw'.ne']
  have hzw : inner ℝ z w = r * ‖w‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have h₁ := h z hz
  have h₂ := h (-z) (by rwa [Metric.mem_closedBall, dist_zero_right, norm_neg,
    ← dist_zero_right])
  rw [hf, hzw] at h₁
  rw [hf, inner_neg_left, hzw] at h₂
  linarith [(abs_le.1 h₁).2, (abs_le.1 h₂).1]

/-- **Affine nonsqueezing.** If an affine symplectic map of `StdSpace ι` sends the closed ball
of radius `r ≥ 0` into the cylinder `stdCylinder i R`, then `r ≤ R`. -/
theorem le_of_image_closedBall_subset_stdCylinder
    {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι} (hf : f ∈ affineSymplecticGroup (stdForm ι))
    {i : ι} {r R : ℝ} (hr : 0 ≤ r) (h : f '' Metric.closedBall 0 r ⊆ stdCylinder i R) :
    r ≤ R := by
  classical
  set a := ContinuousLinearEquiv.adjointEquiv f.linear.toContinuousLinearEquiv
  have ha := SymplecticForm.isSymplectomorphism_iff.1
    (mem_affineSymplecticGroup_iff.1 hf).adjoint
  -- the coordinates `xᵢ` and `yᵢ` of the image of the ball are bounded by `R`
  have hcoord : ∀ c, (c = Sum.inl i ∨ c = Sum.inr i) →
      ∀ z ∈ Metric.closedBall (0 : StdSpace ι) r, |f z c| ≤ R := by
    intro c hc z hz
    have hmem := mem_stdCylinder_iff.1 (h ⟨z, hz, rfl⟩)
    refine le_trans (Real.abs_le_sqrt ?_) hmem
    rcases hc with rfl | rfl
    · have := sq_nonneg ((f z).y i)
      rw [StdSpace.x_apply] at *
      linarith
    · have := sq_nonneg ((f z).x i)
      rw [StdSpace.y_apply] at *
      linarith
  have hu := mul_norm_adjoint_le hr (hcoord (Sum.inl i) (Or.inl rfl))
  have hv := mul_norm_adjoint_le hr (hcoord (Sum.inr i) (Or.inr rfl))
  set u := a (EuclideanSpace.single (Sum.inl i) 1)
  set v := a (EuclideanSpace.single (Sum.inr i) 1)
  -- `ω₀(u, v) = 1`, so `1 ≤ ‖u‖ ‖v‖`
  have huv : stdForm ι u v = 1 := by
    refine (ha (EuclideanSpace.single (Sum.inl i) 1) (EuclideanSpace.single (Sum.inr i) 1)).trans ?_
    rw [stdForm_apply]
    simp [StdSpace.x_apply, StdSpace.y_apply]
  have h1 : 1 ≤ ‖u‖ * ‖v‖ := huv ▸ (le_abs_self _).trans (abs_stdForm_apply_le u v)
  have hR : 0 ≤ R := (mul_nonneg hr (norm_nonneg _)).trans hu
  by_contra hlt
  push Not at hlt
  have : r * r * (‖u‖ * ‖v‖) ≤ R * R := by
    calc r * r * (‖u‖ * ‖v‖) = (r * ‖u‖) * (r * ‖v‖) := by ring
      _ ≤ R * R := mul_le_mul hu hv (by positivity) hR
  nlinarith

/-- **Affine nonsqueezing**, for matrices: if `A` is a symplectic matrix and the map
`z ↦ A z + z₀` sends the closed ball of radius `r ≥ 0` of `StdSpace ι` into the cylinder
`stdCylinder i R`, then `r ≤ R`.

Milestone: *Affine nonsqueezing theorem*. -/
theorem le_of_mem_symplecticGroup_of_image_closedBall_subset_stdCylinder [DecidableEq ι]
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hA : A ∈ Matrix.symplecticGroup ι ℝ) (z₀ : StdSpace ι) {i : ι} {r R : ℝ}
    (hr : 0 ≤ r)
    (h : (fun z ↦ Matrix.toEuclideanLin A z + z₀) '' Metric.closedBall 0 r ⊆
      stdCylinder i R) :
    r ≤ R := by
  have hω := mem_symplecticGroup_iff_forall_stdForm.1 hA
  set e := LinearEquiv.ofBijective (Matrix.toEuclideanLin A)
    ((stdForm ι).bijective_of_forall_apply_eq_or_forall_apply_eq_neg (Or.inl hω))
  have he : (stdForm ι).IsSymplectomorphism (stdForm ι) e :=
    SymplecticForm.isSymplectomorphism_iff.2 hω
  set f := e.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (StdSpace ι) z₀)
  have hf : ⇑f = fun z ↦ Matrix.toEuclideanLin A z + z₀ := by
    funext z
    simp [f, e, add_comm]
  exact le_of_image_closedBall_subset_stdCylinder
    (mem_affineSymplecticGroup_iff_exists.2 ⟨e, he, z₀, by rw [hf]; rfl⟩) hr (hf ▸ h)

end SymplecticGeometry

end
