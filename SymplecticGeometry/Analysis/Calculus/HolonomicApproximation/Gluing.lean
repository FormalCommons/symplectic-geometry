/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Holonomic approximation: estimates for Taylor sections and transverse gluing

Let `f : E → F`, `G : E → E →L[ℝ] F` be a formal section, as in
`HolonomicApproximation/Basic.lean`. Holonomic approximation over a segment, following
[EliashbergMishachev2002], Chapter 3, covers the segment by first-order Taylor sections
`x ↦ f a + G a (x - a)`, which are holonomic, and glues neighbouring ones by a cutoff `χ` in a
linear coordinate `ℓ` transverse to the segment. This file proves the three estimates that this
construction needs, for arbitrary real normed spaces `E` and `F`.

## Main results

* `SymplecticGeometry.norm_add_smul_sub_sub_le_max` and
  `SymplecticGeometry.norm_fderiv_add_smul_sub_sub_le`: the map
  `s y = s₁ y + χ (ℓ y) • (s₂ y - s₁ y)` is as close to `f` as the worse of `s₁`, `s₂`, and its
  derivative is as close to `G` as the worse of theirs, up to the error
  `L * ‖ℓ‖ * ‖s₂ x - s₁ x‖` coming from the slope `L` of the cutoff;
  `SymplecticGeometry.hasFDerivAt_add_smul_sub` computes that derivative.
* `SymplecticGeometry.taylor_sub_taylor_eq` and `SymplecticGeometry.norm_taylor_sub_taylor_le`:
  two Taylor sections at `a` and `b` differ by the Taylor remainder of `f` from `a` to `b` plus
  `(G a - G b) (x - b)`.
* `IsCompact.exists_pos_norm_taylor_remainder_le`: over a compact set `K`, for a `C¹` map `f` and
  a continuous `G`, the Taylor remainder `f x - f a - G a (x - a)` is at most
  `(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and `G x` is `η`-close to `G a`, for all `a ∈ K` and
  `x` in a ball of radius independent of `a`. It combines the mean value inequality
  `Convex.norm_image_sub_le_of_norm_fderiv_le'` with
  `IsCompact.uniformContinuousAt_of_continuousAt`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SymplecticGeometry

/-! ### Gluing two sections by a cutoff in a transverse coordinate -/

/-- The derivative of the map `y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)` that glues `s₁` and `s₂` by a
cutoff `χ` in the linear coordinate `ℓ`. -/
theorem hasFDerivAt_add_smul_sub {s₁ s₂ : E → F} {s₁' s₂' : E →L[ℝ] F} {χ : ℝ → ℝ} {χ' : ℝ}
    {ℓ : E →L[ℝ] ℝ} {x : E} (h₁ : HasFDerivAt s₁ s₁' x) (h₂ : HasFDerivAt s₂ s₂' x)
    (hχ : HasDerivAt χ χ' (ℓ x)) :
    HasFDerivAt (fun y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y))
      (s₁' + χ (ℓ x) • (s₂' - s₁') + (χ' • ℓ).smulRight (s₂ x - s₁ x)) x := by
  have hc : HasFDerivAt (fun y ↦ χ (ℓ y)) (χ' • ℓ) x := by
    exact hχ.comp_hasFDerivAt x ℓ.hasFDerivAt
  exact (h₁.add (hc.smul (h₂.sub h₁))).congr_fderiv (add_assoc _ _ _).symm

/-- **Gluing estimate for values.** Where the cutoff takes values in `[0, 1]`, the map
`y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)` is a convex combination of `s₁` and `s₂`, so its distance to
`f` is at most the larger of theirs. -/
theorem norm_add_smul_sub_sub_le_max (f s₁ s₂ : E → F) {χ : ℝ → ℝ} (ℓ : E →L[ℝ] ℝ) {x : E}
    (hχ₀ : 0 ≤ χ (ℓ x)) (hχ₁ : χ (ℓ x) ≤ 1) :
    ‖s₁ x + χ (ℓ x) • (s₂ x - s₁ x) - f x‖ ≤ max ‖s₁ x - f x‖ ‖s₂ x - f x‖ := by
  have h := (convexOn_norm (convex_univ (𝕜 := ℝ) (E := F))).le_on_segment' trivial trivial
    (sub_nonneg.2 hχ₁) hχ₀ (sub_add_cancel 1 (χ (ℓ x))) (x := s₁ x - f x) (y := s₂ x - f x)
  convert h using 2
  simp only [sub_smul, one_smul, smul_sub]
  abel

/-- **Gluing estimate for derivatives.** If the cutoff takes values in `[0, 1]` and has slope at
most `L` in absolute value at `ℓ x`, then the derivative at `x` of
`y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)` is as close to `G x` as the worse of the derivatives of `s₁`
and `s₂`, up to `L * ‖ℓ‖ * ‖s₂ x - s₁ x‖`. -/
theorem norm_fderiv_add_smul_sub_sub_le {s₁ s₂ : E → F} (G : E → E →L[ℝ] F) {χ : ℝ → ℝ}
    (ℓ : E →L[ℝ] ℝ) {x : E} {L : ℝ} (h₁ : DifferentiableAt ℝ s₁ x) (h₂ : DifferentiableAt ℝ s₂ x)
    (hχ : DifferentiableAt ℝ χ (ℓ x)) (hχ₀ : 0 ≤ χ (ℓ x)) (hχ₁ : χ (ℓ x) ≤ 1)
    (hL : |deriv χ (ℓ x)| ≤ L) :
    ‖fderiv ℝ (fun y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)) x - G x‖ ≤
      max ‖fderiv ℝ s₁ x - G x‖ ‖fderiv ℝ s₂ x - G x‖ + L * ‖ℓ‖ * ‖s₂ x - s₁ x‖ := by
  rw [(hasFDerivAt_add_smul_sub h₁.hasFDerivAt h₂.hasFDerivAt hχ.hasDerivAt).fderiv]
  set c := χ (ℓ x)
  have hmax := (convexOn_norm (convex_univ (𝕜 := ℝ) (E := E →L[ℝ] F))).le_on_segment'
    trivial trivial (sub_nonneg.2 hχ₁) hχ₀ (sub_add_cancel 1 c)
    (x := fderiv ℝ s₁ x - G x) (y := fderiv ℝ s₂ x - G x)
  have hsmul : ‖(deriv χ (ℓ x) • ℓ).smulRight (s₂ x - s₁ x)‖ ≤ L * ‖ℓ‖ * ‖s₂ x - s₁ x‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
    gcongr
  have heq : fderiv ℝ s₁ x + c • (fderiv ℝ s₂ x - fderiv ℝ s₁ x) +
      (deriv χ (ℓ x) • ℓ).smulRight (s₂ x - s₁ x) - G x =
      ((1 - c) • (fderiv ℝ s₁ x - G x) + c • (fderiv ℝ s₂ x - G x)) +
      (deriv χ (ℓ x) • ℓ).smulRight (s₂ x - s₁ x) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hmax hsmul)

/-! ### Neighbouring Taylor sections -/

/-- The first-order Taylor sections `x ↦ f a + G a (x - a)` and `x ↦ f b + G b (x - b)` of a
formal section differ by the Taylor remainder of `f` from `a` to `b` plus `(G a - G b) (x - b)`.
-/
theorem taylor_sub_taylor_eq (f : E → F) (G : E → E →L[ℝ] F) (a b x : E) :
    (f a + G a (x - a)) - (f b + G b (x - b)) =
      (f a + G a (b - a) - f b) + (G a - G b) (x - b) := by
  have : x - a = (b - a) + (x - b) := by abel
  rw [this, map_add, sub_apply]
  abel

/-- Two first-order Taylor sections `x ↦ f a + G a (x - a)` and `x ↦ f b + G b (x - b)` of a
formal section differ at `x` by at most the Taylor remainder `‖f b - f a - G a (b - a)‖` plus
`‖G a - G b‖ * ‖x - b‖`. -/
theorem norm_taylor_sub_taylor_le (f : E → F) (G : E → E →L[ℝ] F) (a b x : E) :
    ‖(f a + G a (x - a)) - (f b + G b (x - b))‖ ≤
      ‖f b - f a - G a (b - a)‖ + ‖G a - G b‖ * ‖x - b‖ := by
  rw [taylor_sub_taylor_eq]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ((G a - G b).le_opNorm _))
  rw [← norm_neg]
  congr 1
  abel

end SymplecticGeometry

/-! ### A uniform Taylor estimate over a compact set -/

/-- **Uniform Taylor estimate.** Let `f` be `C¹`, `G` continuous, `K` compact and `η > 0`. There
is `ρ > 0` such that for every `a ∈ K` and every `x` with `‖x - a‖ < ρ`, the Taylor remainder
`f x - f a - G a (x - a)` has norm at most `(‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖`, and
`‖G x - G a‖ ≤ η`. -/
theorem IsCompact.exists_pos_norm_taylor_remainder_le {f : E → F} {G : E → E →L[ℝ] F}
    {K : Set E} (hK : IsCompact K) (hf : ContDiff ℝ 1 f) (hG : Continuous G) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ a ∈ K, ∀ x, ‖x - a‖ < ρ →
      ‖f x - f a - G a (x - a)‖ ≤ (‖fderiv ℝ f a - G a‖ + η) * ‖x - a‖ ∧ ‖G x - G a‖ ≤ η := by
  have hunif : ∀ g : E → E →L[ℝ] F, Continuous g →
      ∃ ρ > 0, ∀ a ∈ K, ∀ y, ‖y - a‖ < ρ → ‖g y - g a‖ ≤ η := by
    intro g hg
    obtain ⟨ρ, hρ, h⟩ := Metric.mem_uniformity_dist.1
      (hK.uniformContinuousAt_of_continuousAt g (fun a _ ↦ hg.continuousAt)
        (Metric.dist_mem_uniformity hη))
    refine ⟨ρ, hρ, fun a ha y hy ↦ ?_⟩
    have : dist (g a) (g y) < η := h (a := a) (b := y) (by rwa [dist_comm, dist_eq_norm]) ha
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  obtain ⟨ρ₁, hρ₁, h₁⟩ := hunif _ (hf.continuous_fderiv one_ne_zero)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := hunif G hG
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun a ha x hx ↦
    ⟨?_, h₂ a ha x (hx.trans_le (min_le_right _ _))⟩⟩
  have hmvt : ‖f x - f a - fderiv ℝ f a (x - a)‖ ≤ η * ‖x - a‖ :=
    (convex_ball a ρ₁).norm_image_sub_le_of_norm_fderiv_le'
      (fun y _ ↦ (hf.differentiable one_ne_zero).differentiableAt)
      (fun y hy ↦ h₁ a ha y (by rwa [mem_ball, dist_eq_norm] at hy)) (mem_ball_self hρ₁)
      (by rw [mem_ball, dist_eq_norm]; exact hx.trans_le (min_le_left _ _))
  have heq : f x - f a - G a (x - a) =
      (f x - f a - fderiv ℝ f a (x - a)) + (fderiv ℝ f a - G a) (x - a) := by
    rw [sub_apply]
    abel
  rw [heq, add_mul, add_comm (‖fderiv ℝ f a - G a‖ * _)]
  exact (norm_add_le _ _).trans (add_le_add hmvt ((fderiv ℝ f a - G a).le_opNorm _))

end
