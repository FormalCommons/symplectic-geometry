/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.AffineSymplectic
import SymplecticGeometry.Analysis.InnerProductSpace.Symplectic.Nonsqueezing
import SymplecticGeometry.Geometry.Symplectic.SymplecticTransport
import Mathlib.Algebra.Order.Star.Real

/-!
# The linear symplectic width

For a subset `A` of the standard model `StdSpace ι = ℝ²ⁿ`, the linear symplectic width
`w_L(A)` is the supremum of `π r²` over the radii `r ≥ 0` of the closed balls `B²ⁿ(r)` that some
affine symplectic map sends into `A`. It takes values in `ℝ≥0∞`: it is `0` for a set that
contains no image of a ball, and `∞` for the whole space.

## Main definitions

* `SymplecticGeometry.linearSymplecticWidth A`: the linear symplectic width of `A`.

## Main results

* `SymplecticGeometry.linearSymplecticWidth_mono`: monotonicity.
* `SymplecticGeometry.nonempty_interior_of_linearSymplecticWidth_ne_zero`: a set of positive
  width has nonempty interior.
* `SymplecticGeometry.linearSymplecticWidth_image`: invariance under affine symplectic maps.
* `SymplecticGeometry.linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg`:
  invariance under linear maps `Ψ` with `Ψ^* ω₀ = ±ω₀`.
* `SymplecticGeometry.linearSymplecticWidth_smul`: conformality, `w_L(c A) = c² w_L(A)` for
  `c ≠ 0`.
* `SymplecticGeometry.linearSymplecticWidth_image_closedBall` and
  `SymplecticGeometry.linearSymplecticWidth_image_stdCylinder`: the images of balls and of
  cylinders of radius `r` under affine symplectic maps have width `π r²`.
* `SymplecticGeometry.linearSymplecticWidth_stdCylinder_le`: a cylinder of radius `R` has width
  at most `π R²`, for every real `R`.
* `SymplecticGeometry.ofReal_pi_mul_sq_le_linearSymplecticWidth_of_closedBall_subset`: a set
  containing the ball of radius `r` about `0` has width at least `π r²`.
* `SymplecticGeometry.linearSymplecticWidth_eq_iSup_image_closedBall`: the width of a set is
  the supremum of the widths of the symplectic balls inside it.

In dimension zero (`ι` empty) the space is a point, and every nonempty set has width `∞`; this is
why the statement for balls assumes `Nonempty ι`, and the conformality `c ≠ 0`.

These are the properties of the linear symplectic width in McDuff–Salamon, Section 2.4; the
value on cylinders is the affine nonsqueezing theorem, and the invariance under anti-symplectic
maps is the second half of their Exercise 2.4.3.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

open TauCeti Metric
open scoped ENNReal NNReal Real Pointwise

variable {ι : Type*} [Fintype ι]

/-- The linear symplectic width of a subset `A` of the standard model: the supremum of `π r²`
over the radii `r ≥ 0` of the closed balls about `0` whose image under some affine symplectic
map lies in `A`. -/
noncomputable def linearSymplecticWidth (A : Set (StdSpace ι)) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (f ∈ affineSymplecticGroup (stdForm ι))
    (_ : f '' closedBall 0 (r : ℝ) ⊆ A), ENNReal.ofReal (π * (r : ℝ) ^ 2)

theorem linearSymplecticWidth_def (A : Set (StdSpace ι)) :
    linearSymplecticWidth A =
      ⨆ (r : ℝ≥0) (f ∈ affineSymplecticGroup (stdForm ι))
        (_ : f '' closedBall 0 (r : ℝ) ⊆ A), ENNReal.ofReal (π * (r : ℝ) ^ 2) :=
  (rfl)

/-- A ball of radius `r ≥ 0` whose image under an affine symplectic map lies in `A` bounds the
width of `A` from below by `π r²`. -/
theorem le_linearSymplecticWidth {A : Set (StdSpace ι)} {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    (hf : f ∈ affineSymplecticGroup (stdForm ι)) {r : ℝ} (hr : 0 ≤ r)
    (h : f '' closedBall 0 r ⊆ A) :
    ENNReal.ofReal (π * r ^ 2) ≤ linearSymplecticWidth A := by
  rw [linearSymplecticWidth_def]
  exact le_iSup₂_of_le (⟨r, hr⟩ : ℝ≥0) f (le_iSup₂_of_le hf h le_rfl)

/-- A set that contains the closed ball of radius `r ≥ 0` about `0` has width at least `π r²`. -/
theorem ofReal_pi_mul_sq_le_linearSymplecticWidth_of_closedBall_subset {A : Set (StdSpace ι)}
    {r : ℝ} (hr : 0 ≤ r) (h : closedBall 0 r ⊆ A) :
    ENNReal.ofReal (π * r ^ 2) ≤ linearSymplecticWidth A :=
  le_linearSymplecticWidth (one_mem _) hr (by rwa [AffineEquiv.coe_one, Set.image_id])

/-- The width of `A` is at most `c` if and only if `π r² ≤ c` for every ball of radius `r ≥ 0`
whose image under an affine symplectic map lies in `A`. -/
theorem linearSymplecticWidth_le_iff {A : Set (StdSpace ι)} {c : ℝ≥0∞} :
    linearSymplecticWidth A ≤ c ↔
      ∀ f ∈ affineSymplecticGroup (stdForm ι), ∀ r : ℝ, 0 ≤ r →
        f '' closedBall 0 r ⊆ A → ENNReal.ofReal (π * r ^ 2) ≤ c := by
  refine ⟨fun h f hf r hr hA ↦ (le_linearSymplecticWidth hf hr hA).trans h, fun h ↦ ?_⟩
  rw [linearSymplecticWidth_def]
  exact iSup_le fun r ↦ iSup₂_le fun f hf ↦ iSup_le fun hA ↦ h f hf r r.property hA

/-- The width is monotone. -/
theorem linearSymplecticWidth_mono {A B : Set (StdSpace ι)} (h : A ⊆ B) :
    linearSymplecticWidth A ≤ linearSymplecticWidth B :=
  linearSymplecticWidth_le_iff.2 fun _ hf _ hr hA ↦ le_linearSymplecticWidth hf hr (hA.trans h)

/-- The empty set has width `0`. -/
@[simp]
theorem linearSymplecticWidth_empty : linearSymplecticWidth (∅ : Set (StdSpace ι)) = 0 := by
  refine le_antisymm (linearSymplecticWidth_le_iff.2 fun f _ r hr hA ↦ ?_) bot_le
  have h0 : f 0 ∈ f '' closedBall (0 : StdSpace ι) r := ⟨0, mem_closedBall_self hr, rfl⟩
  exact absurd (hA h0) (Set.notMem_empty _)

/-- The whole space contains balls of every radius, so its width is `∞`. -/
@[simp]
theorem linearSymplecticWidth_univ :
    linearSymplecticWidth (Set.univ : Set (StdSpace ι)) = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun c ↦ ?_
  have h := le_linearSymplecticWidth (A := (Set.univ : Set (StdSpace ι))) (one_mem _)
    (Real.sqrt_nonneg c) (Set.subset_univ _)
  refine le_trans ?_ h
  rw [Real.sq_sqrt c.coe_nonneg, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left c.coe_nonneg (by linarith [Real.two_le_pi]))

/-- A set of positive width contains a nonempty open set: the image of an open ball under an
affine symplectic map. -/
theorem nonempty_interior_of_linearSymplecticWidth_ne_zero {A : Set (StdSpace ι)}
    (h : linearSymplecticWidth A ≠ 0) : (interior A).Nonempty := by
  have h' : ¬linearSymplecticWidth A ≤ 0 := by simpa using h
  rw [linearSymplecticWidth_le_iff] at h'
  push Not at h'
  obtain ⟨f, -, r, hr, hA, hpos⟩ := h'
  have hr' : 0 < r := by
    rcases hr.eq_or_lt with rfl | hr'
    · simp at hpos
    · exact hr'
  have hopen : IsOpen (f '' ball 0 r) := by
    rw [Set.image_eq_preimage_of_inverse f.symm_apply_apply f.apply_symm_apply]
    exact isOpen_ball.preimage (AffineMap.continuous_of_finiteDimensional f.symm.toAffineMap)
  exact ⟨f 0, mem_interior.2 ⟨f '' ball 0 r, (Set.image_mono ball_subset_closedBall).trans hA,
    hopen, 0, mem_ball_self hr', rfl⟩⟩

/-! ### Invariance -/

/-- Affine symplectic maps do not decrease the width. -/
private theorem linearSymplecticWidth_le_image {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    (hf : f ∈ affineSymplecticGroup (stdForm ι)) (A : Set (StdSpace ι)) :
    linearSymplecticWidth A ≤ linearSymplecticWidth (f '' A) := by
  refine linearSymplecticWidth_le_iff.2 fun g hg r hr hA ↦ ?_
  refine le_linearSymplecticWidth (Subgroup.mul_mem _ hf hg) hr ?_
  rw [AffineEquiv.coe_mul, Set.image_comp]
  exact Set.image_mono hA

/-- The width is invariant under affine symplectic maps. -/
theorem linearSymplecticWidth_image {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    (hf : f ∈ affineSymplecticGroup (stdForm ι)) (A : Set (StdSpace ι)) :
    linearSymplecticWidth (f '' A) = linearSymplecticWidth A := by
  refine le_antisymm ?_ (linearSymplecticWidth_le_image hf A)
  have h := linearSymplecticWidth_le_image (inv_mem hf) (f '' A)
  simpa [AffineEquiv.inv_def, Set.image_image] using h

/-- Linear equivalences with `Ψ^* ω₀ = -ω₀` do not decrease the width: if `g` maps a ball into
`A`, then `z ↦ Ψ (g (z̄))` is affine symplectic and maps the ball into `Ψ '' A`. -/
private theorem linearSymplecticWidth_le_image_of_forall_apply_eq_neg
    {Ψ : StdSpace ι ≃ₗ[ℝ] StdSpace ι} (hΨ : ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w)
    (A : Set (StdSpace ι)) :
    linearSymplecticWidth A ≤ linearSymplecticWidth (Ψ '' A) := by
  refine linearSymplecticWidth_le_iff.2 fun g hg r hr hA ↦ ?_
  set e := (stdConj ι).toLinearEquiv.trans (g.linear.trans Ψ)
  have he : (stdForm ι).IsSymplectomorphism (stdForm ι) e :=
    isSymplectomorphism_stdConj_trans_of_forall_apply_eq_neg (Ψ := g.linear.trans Ψ)
      fun z w ↦ by simp [hΨ, (mem_affineSymplecticGroup_iff.1 hg).apply]
  refine le_linearSymplecticWidth (f := e.toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (StdSpace ι) (Ψ (g 0)))) (mem_affineSymplecticGroup_iff.2 he) hr ?_
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨g (stdConj ι z), hA ⟨stdConj ι z, ?_, rfl⟩, ?_⟩
  · simpa using hz
  · have hd : g (stdConj ι z) = g.linear (stdConj ι z) + g 0 :=
      congr_fun g.toAffineMap.decomp _
    simp [e, hd, add_comm]

/-- The width is invariant under linear maps `Ψ` with `Ψ^* ω₀ = ω₀` or `Ψ^* ω₀ = -ω₀`. -/
theorem linearSymplecticWidth_image_of_forall_apply_eq_or_forall_apply_eq_neg
    {Ψ : StdSpace ι →ₗ[ℝ] StdSpace ι}
    (hΨ : (∀ z w, stdForm ι (Ψ z) (Ψ w) = stdForm ι z w) ∨
      ∀ z w, stdForm ι (Ψ z) (Ψ w) = -stdForm ι z w)
    (A : Set (StdSpace ι)) :
    linearSymplecticWidth (Ψ '' A) = linearSymplecticWidth A := by
  set e := LinearEquiv.ofBijective Ψ
    ((stdForm ι).bijective_of_forall_apply_eq_or_forall_apply_eq_neg hΨ)
  have hcoe : ⇑Ψ = ⇑e := funext fun z ↦ (LinearEquiv.ofBijective_apply Ψ z).symm
  rw [hcoe] at hΨ ⊢
  rcases hΨ with h | h
  · have he : (stdForm ι).IsSymplectomorphism (stdForm ι) e :=
      SymplecticForm.isSymplectomorphism_iff.2 h
    exact linearSymplecticWidth_image
      ((LinearEquiv.toAffineEquiv_mem_affineSymplecticGroup_iff e).2 he) A
  · have hsymm : ∀ z w, stdForm ι (e.symm z) (e.symm w) = -stdForm ι z w := fun z w ↦ by
      have := h (e.symm z) (e.symm w)
      simp only [LinearEquiv.apply_symm_apply] at this
      linarith
    refine le_antisymm ?_ (linearSymplecticWidth_le_image_of_forall_apply_eq_neg h A)
    have h' := linearSymplecticWidth_le_image_of_forall_apply_eq_neg hsymm (e '' A)
    simpa [Set.image_image] using h'

/-! ### Conformality -/

/-- Scaling by `c` multiplies the width by at least `c²`: if `g` maps the ball of radius `r`
into `A`, then `z ↦ g.linear z + c • g 0` maps the ball of radius `|c| r` into `c • A`. -/
private theorem ofReal_sq_mul_linearSymplecticWidth_le (c : ℝ) (A : Set (StdSpace ι)) :
    ENNReal.ofReal (c ^ 2) * linearSymplecticWidth A ≤ linearSymplecticWidth (c • A) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc2 : ENNReal.ofReal (c ^ 2) ≠ 0 := by simp [hc]
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hc2) (Or.inl ENNReal.ofReal_ne_top)]
  refine linearSymplecticWidth_le_iff.2 fun g hg r hr hA ↦ ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc2) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul (by positivity)]
  have hball : closedBall (0 : StdSpace ι) (|c| * r) = c • closedBall 0 r := by
    rw [smul_closedBall c 0 hr, smul_zero, Real.norm_eq_abs]
  have key := le_linearSymplecticWidth (A := c • A)
    (f := g.linear.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (StdSpace ι) (c • g 0)))
    (mem_affineSymplecticGroup_iff.2 ((mem_affineSymplecticGroup_iff (f := g)).1 hg))
    (mul_nonneg (abs_nonneg c) hr) (by
      rw [hball]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hd : g z = g.linear z + g 0 := congr_fun g.toAffineMap.decomp _
      refine ⟨g z, hA ⟨z, hz, rfl⟩, ?_⟩
      simp [hd, smul_add, add_comm])
  convert key using 2
  rw [mul_pow, sq_abs]
  ring

/-- Conformality: for `c ≠ 0`, the width of `c • A` is `c²` times that of `A`. For `c = 0` this
fails in dimension zero, where the point `{0}` has width `∞`. -/
theorem linearSymplecticWidth_smul {c : ℝ} (hc : c ≠ 0) (A : Set (StdSpace ι)) :
    linearSymplecticWidth (c • A) = ENNReal.ofReal (c ^ 2) * linearSymplecticWidth A := by
  refine le_antisymm ?_ (ofReal_sq_mul_linearSymplecticWidth_le c A)
  have h := ofReal_sq_mul_linearSymplecticWidth_le c⁻¹ (c • A)
  rw [inv_smul_smul₀ hc] at h
  have hone : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (c⁻¹ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c), ← mul_pow, mul_inv_cancel₀ hc, one_pow,
      ENNReal.ofReal_one]
  calc linearSymplecticWidth (c • A)
      = ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (c⁻¹ ^ 2) * linearSymplecticWidth (c • A)) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal (c ^ 2) * linearSymplecticWidth A := by gcongr

/-! ### Balls and cylinders -/

/-- The cylinder `Z²ⁿ(R)` over the `i`-th coordinate plane has width at most `π R²`, for every
real `R`: an affine symplectic image of a ball of radius `r` inside it has `r ≤ R`. -/
theorem linearSymplecticWidth_stdCylinder_le (i : ι) (R : ℝ) :
    linearSymplecticWidth (stdCylinder i R) ≤ ENNReal.ofReal (π * R ^ 2) := by
  refine linearSymplecticWidth_le_iff.2 fun f hf r hr hA ↦ ENNReal.ofReal_le_ofReal ?_
  have := le_of_image_closedBall_subset_stdCylinder hf hr hA
  gcongr

/-- The image of a cylinder of radius `R ≥ 0` under an affine symplectic map has width `π R²`.
For `R < 0` the cylinder is empty (`stdCylinder_eq_empty`). -/
theorem linearSymplecticWidth_image_stdCylinder {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    (hf : f ∈ affineSymplecticGroup (stdForm ι)) (i : ι) {R : ℝ} (hR : 0 ≤ R) :
    linearSymplecticWidth (f '' stdCylinder i R) = ENNReal.ofReal (π * R ^ 2) := by
  rw [linearSymplecticWidth_image hf]
  refine le_antisymm (linearSymplecticWidth_stdCylinder_le i R) ?_
  exact ofReal_pi_mul_sq_le_linearSymplecticWidth_of_closedBall_subset hR
    (closedBall_subset_stdCylinder i R)

/-- The image of a closed ball of radius `r ≥ 0` under an affine symplectic map has width
`π r²`. In dimension zero a ball is a point, of width `∞`, hence the assumption `Nonempty ι`. -/
theorem linearSymplecticWidth_image_closedBall [Nonempty ι] {f : StdSpace ι ≃ᵃ[ℝ] StdSpace ι}
    (hf : f ∈ affineSymplecticGroup (stdForm ι)) (z : StdSpace ι) {r : ℝ} (hr : 0 ≤ r) :
    linearSymplecticWidth (f '' closedBall z r) = ENNReal.ofReal (π * r ^ 2) := by
  have hz : closedBall z r = AffineEquiv.constVAdd ℝ (StdSpace ι) z '' closedBall 0 r := by
    rw [show ⇑(AffineEquiv.constVAdd ℝ (StdSpace ι) z) = (z +ᵥ ·) from
      funext fun _ ↦ AffineEquiv.constVAdd_apply .., Set.image_vadd,
      Metric.vadd_closedBall, vadd_eq_add, add_zero]
  rw [hz, linearSymplecticWidth_image hf,
    linearSymplecticWidth_image (AffineEquiv.constVAdd_mem_affineSymplecticGroup z)]
  refine le_antisymm ((linearSymplecticWidth_mono
    (closedBall_subset_stdCylinder (Classical.arbitrary ι) r)).trans
      (linearSymplecticWidth_stdCylinder_le _ r)) ?_
  exact ofReal_pi_mul_sq_le_linearSymplecticWidth_of_closedBall_subset hr subset_rfl

/-- The width of a set `A` is the supremum of the widths of the images of
closed balls about `0` under affine symplectic maps that lie in `A`. -/
theorem linearSymplecticWidth_eq_iSup_image_closedBall (A : Set (StdSpace ι)) :
    linearSymplecticWidth A =
      ⨆ (f ∈ affineSymplecticGroup (stdForm ι)) (r : ℝ≥0)
        (_ : f '' closedBall 0 (r : ℝ) ⊆ A),
        linearSymplecticWidth (f '' closedBall 0 (r : ℝ)) := by
  refine le_antisymm ?_ (iSup₂_le fun _ _ ↦ iSup₂_le fun _ hr ↦ linearSymplecticWidth_mono hr)
  rw [linearSymplecticWidth_def]
  refine iSup_le fun r ↦ iSup₂_le fun f hf ↦ iSup_le fun hr ↦ ?_
  refine le_iSup₂_of_le f hf (le_iSup₂_of_le r hr ?_)
  exact le_linearSymplecticWidth hf r.coe_nonneg subset_rfl

end SymplecticGeometry

end
