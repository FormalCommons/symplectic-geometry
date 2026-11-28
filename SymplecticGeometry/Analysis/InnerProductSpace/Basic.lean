/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.Analysis.Normed.Module.Dual.Basic

/-!
# Real inner products: bounds on balls, complex scalars

Facts about real inner product spaces that complement Mathlib's
`Mathlib.Analysis.InnerProductSpace.Basic`.

* `mul_norm_le_of_abs_inner_add_le`: if the affine function `z ↦ ⟪z, w⟫ + c` is bounded in
  absolute value by `R` on the closed ball of radius `r ≥ 0` about `0`, then `r ‖w‖ ≤ R`.
  It follows from Tau Ceti's `StrongDual.re_apply_add_mul_norm_le_iff`, applied to the
  functionals `⟪·, w⟫` and `⟪·, -w⟫`, whose norms are `‖w‖`.
* `real_inner_I_smul_self_eq_zero`, `real_inner_complex_smul_self`: on a complex normed space
  whose norm comes from a real inner product, such as a fibre of a Hermitian vector bundle,
  multiplication by `i` is an isometry, so `⟪i • u, u⟫ = 0` and `⟪c • u, u⟫ = re c * ‖u‖ ^ 2`.
  They complement Mathlib's `real_inner_smul_self_left` and `real_inner_I_smul_self`, which is
  stated only for the real inner product `Inner.rclikeToReal`.
* `norm_add_I_smul_eq_norm_sub_I_smul`: on such a space of complex dimension one, if `a` and `b`
  are orthogonal to a nonzero `u`, then `‖a + i • b‖ = ‖a - i • b‖`.
* `eq_I_mul_real_inner_smul_of_real_inner_eq_zero`: on such a space of complex dimension one, a
  vector `w` orthogonal to a unit vector `u` is `(i ⟪i • u, w⟫) • u`.
-/

public section

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `|⟪z, w⟫ + c| ≤ R` for every `z` in the closed ball of radius `r ≥ 0` about `0`, then
`r ‖w‖ ≤ R`. -/
theorem mul_norm_le_of_abs_inner_add_le {w : E} {c r R : ℝ} (hr : 0 ≤ r)
    (h : ∀ z ∈ Metric.closedBall (0 : E) r, |inner ℝ z w + c| ≤ R) :
    r * ‖w‖ ≤ R := by
  have h1 := (StrongDual.re_apply_add_mul_norm_le_iff (𝕜 := ℝ) (f := innerSL ℝ w) (x := 0)
    (u := R - c) hr).2 fun y hy ↦ by
      simpa [real_inner_comm] using
        (by linarith [(abs_le.1 (h y hy)).2] : inner ℝ y w ≤ R - c)
  have h2 := (StrongDual.re_apply_add_mul_norm_le_iff (𝕜 := ℝ) (f := innerSL ℝ (-w)) (x := 0)
    (u := R + c) hr).2 fun y hy ↦ by
      simpa [real_inner_comm, inner_neg_right] using
        (by linarith [(abs_le.1 (h y hy)).1] : -inner ℝ y w ≤ R + c)
  simp at h1 h2
  linarith

section ComplexScalars

open scoped RealInnerProductSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [NormedSpace ℂ L]

/-- In a complex normed space whose norm comes from a real inner product, `i • u` is orthogonal
to `u`: multiplication by `i` is an isometry, so `‖i • u + u‖ = ‖i • u - u‖`. -/
theorem real_inner_I_smul_self_eq_zero (u : L) : ⟪Complex.I • u, u⟫ = 0 := by
  have h : ‖Complex.I • u + u‖ = ‖Complex.I • u - u‖ := by
    rw [show Complex.I • u + u = (Complex.I + 1) • u by rw [add_smul, one_smul],
      show Complex.I • u - u = (Complex.I - 1) • u by rw [sub_smul, one_smul], norm_smul,
      norm_smul, ← Complex.norm_conj (Complex.I + 1), map_add, Complex.conj_I, map_one, ← norm_neg]
    ring_nf
  have h₁ := real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
    (Complex.I • u) u
  have h₂ := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
    (Complex.I • u) u
  rw [h] at h₁
  linarith

variable [IsScalarTower ℝ ℂ L]

/-- In a complex normed space whose norm comes from a real inner product, the real inner product
of `c • u` with `u` is `re c * ‖u‖ ^ 2`. -/
theorem real_inner_complex_smul_self (c : ℂ) (u : L) : ⟪c • u, u⟫ = c.re * ‖u‖ ^ 2 := by
  have hr (r : ℝ) (w : L) : (r : ℂ) • w = r • w := by simpa using algebraMap_smul ℂ r w
  conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_comm, ← smul_smul, smul_comm, hr, hr,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_I_smul_self_eq_zero,
    real_inner_self_eq_norm_sq]
  simp

/-- Let `L` be a complex line whose norm comes from a real inner product. If `a` and `b` are both
orthogonal to a nonzero `u`, then `‖a + i • b‖ = ‖a - i • b‖`: both are imaginary multiples of
`u`, `a = i α • u` and `b = i β • u` with `α`, `β` real, and `|i α - β| = |i α + β|`. -/
theorem norm_add_I_smul_eq_norm_sub_I_smul (hL : Module.finrank ℂ L = 1) {u a b : L}
    (hu : u ≠ 0) (ha : ⟪a, u⟫ = 0) (hb : ⟪b, u⟫ = 0) :
    ‖a + Complex.I • b‖ = ‖a - Complex.I • b‖ := by
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu).1 hL a
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu).1 hL b
  have hu2 : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [real_inner_complex_smul_self, mul_eq_zero, or_iff_left hu2] at ha hb
  rw [smul_smul, ← add_smul, ← sub_smul, norm_smul, norm_smul, ← Complex.norm_conj,
    ← norm_neg (c - _)]
  congr 2
  apply Complex.ext <;> simp [ha, hb]

/-- Let `L` be a complex line whose norm comes from a real inner product, and `u` a unit vector.
Every `w` orthogonal to `u` is the imaginary multiple `(i ⟪i • u, w⟫) • u` of `u`. -/
theorem eq_I_mul_real_inner_smul_of_real_inner_eq_zero (hL : Module.finrank ℂ L = 1)
    {u w : L} (hu : ‖u‖ = 1) (hw : ⟪w, u⟫ = 0) :
    w = (Complex.I * (⟪Complex.I • u, w⟫ : ℂ)) • u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' u hu0).1 hL w
  rw [real_inner_complex_smul_self, hu, one_pow, mul_one] at hw
  have h : ⟪Complex.I • u, c • u⟫ = c.im := by
    rw [real_inner_comm, show c • u = (c * -Complex.I) • Complex.I • u by
      rw [smul_smul, mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, mul_one],
      real_inner_complex_smul_self, norm_smul, Complex.norm_I, one_mul, hu]
    simp
  rw [h]
  congr 1
  apply Complex.ext <;> simp [hw]

end ComplexScalars

end SymplecticGeometry

end
