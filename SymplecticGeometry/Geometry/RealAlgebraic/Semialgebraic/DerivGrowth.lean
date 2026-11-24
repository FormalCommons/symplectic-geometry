/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Differentiable
public import SymplecticGeometry.Geometry.RealAlgebraic.Semialgebraic.Growth
import SymplecticGeometry.Analysis.SpecialFunctions.Log.Unbounded

/-!
# The derivative of a bounded one-variable semialgebraic function near `0⁺`

Let `f` be a real function of one variable that is semialgebraic and bounded on the points
`![t]`, `0 < t < ε₀`. Then the derivative of `t ↦ f ![t]` is bounded by a multiple of
`t ^ (p - 1)` near `0⁺`, for some `p > 0`
(`TauCeti.IsSemialgebraicOn.exists_abs_deriv_le_mul_rpow`). So the derivative may blow up at
`0`, but strictly slower than `t⁻¹`.

The proof: by `TauCeti.IsSemialgebraicOn.exists_pos_differentiableOn_Ioo` the function is
differentiable on some `(0, ε)` with a semialgebraic derivative `D`. If `D` vanishes near
`0⁺` there is nothing to show. Otherwise `D t / t ^ r → a ≠ 0` for some rational `r`
(`TauCeti.IsSemialgebraicOn.exists_tendsto_div_rpow_nhdsGT`), and `p = r + 1` works once
`r > -1`. If `r ≤ -1`, then `a * D t ≥ k / t` near `0⁺` with `k = a ^ 2 / 2 > 0`, so
`t ↦ a * f ![t]` is not bounded below there
(`Real.not_bddBelow_image_Ioo_of_div_le_deriv`), against the hypothesis.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 2.6.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 7.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Let `f` be a real function of one variable that is semialgebraic and bounded on the points
`![t]`, `0 < t < ε₀`. Then near `0⁺` the derivative of `t ↦ f ![t]` is bounded by
`C * t ^ (p - 1)`, for some `p > 0` and some `C`. -/
theorem IsSemialgebraicOn.exists_abs_deriv_le_mul_rpow {f : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn (fun x (_ : Unit) ↦ f x) s) {ε₀ M : ℝ}
    (hε₀ : 0 < ε₀) (hs : ∀ t ∈ Ioo 0 ε₀, ![t] ∈ s) (hM : ∀ t ∈ Ioo 0 ε₀, |f ![t]| ≤ M) :
    ∃ p : ℝ, 0 < p ∧ ∃ C ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ioo 0 ε, |_root_.deriv (fun t ↦ f ![t]) t| ≤ C * t ^ (p - 1) := by
  obtain ⟨ε₁, hε₁, hd, hds⟩ := hf.exists_pos_differentiableOn_Ioo hε₀ hs
  set D := _root_.deriv (fun t ↦ f ![t])
  by_cases hne : ∃ᶠ t in 𝓝[>] 0, D t ≠ 0
  swap
  · -- `D` vanishes on some interval `(0, ε)`.
    obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (not_frequently.1 hne)
    refine ⟨1, one_pos, 0, ε, hε, fun t ht ↦ ?_⟩
    simp [show D t = 0 by simpa using hsub ht]
  obtain ⟨q, a, ha, hlim⟩ := hds.exists_tendsto_div_rpow_nhdsGT
    (eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun t ht ↦ by simpa using ht) (by simpa using hne)
  simp only [Matrix.cons_val_zero] at hlim
  set r : ℝ := (q : ℝ)
  have ha' : 0 < |a| := abs_pos.2 ha
  have hclose : ∀ᶠ t in 𝓝[>] 0, |D t / t ^ r - a| < |a| / 2 := by
    have := hlim.eventually (Metric.ball_mem_nhds a (half_pos ha'))
    simpa [Metric.mem_ball, Real.dist_eq] using this
  have hr : -1 < r := by
    by_contra hr
    replace hr := not_lt.1 hr
    obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hclose.and (eventually_mem_set.2 (Ioo_mem_nhdsGT (lt_min (lt_min hε₀ hε₁) one_pos))))
    have hδ' : ∀ t ∈ Ioo 0 δ, t < ε₀ ∧ t < ε₁ ∧ t < 1 := fun t ht ↦ by
      have := (hsub ht).2.2
      simp only [lt_min_iff] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have hdδ : ∀ t ∈ Ioo 0 δ, DifferentiableAt ℝ (fun t ↦ f ![t]) t := fun t ht ↦
      (hd t ⟨ht.1, (hδ' t ht).2.1⟩).differentiableAt (Ioo_mem_nhds ht.1 (hδ' t ht).2.1)
    -- `t ↦ a * f ![t]` is bounded, but its derivative is at least `(a ^ 2 / 2) / t`.
    refine Real.not_bddBelow_image_Ioo_of_div_le_deriv (g := fun t ↦ a * f ![t])
      (half_pos (pow_pos ha' 2)) hδ (fun t ht ↦ ((hdδ t ht).const_mul a).differentiableWithinAt)
      (fun t ht ↦ ?_) ⟨-(|a| * M), forall_mem_image.2 fun t ht ↦ ?_⟩
    swap
    · have h2 : |a * f ![t]| ≤ |a| * M := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t ⟨ht.1, (hδ' t ht).1⟩) (abs_nonneg a)
      linarith [neg_abs_le (a * f ![t])]
    rw [deriv_const_mul a (hdδ t ht)]
    have ht0 := ht.1
    have hpow : 0 < t ^ r := Real.rpow_pos_of_pos ht0 r
    -- `a * (D t / t ^ r) ≥ a ^ 2 / 2`, and `t ^ r ≥ t⁻¹`.
    have h1 : |a| ^ 2 / 2 ≤ a * (D t / t ^ r) := by
      have h := (hsub ht).1
      have h2 : |a * (D t / t ^ r - a)| ≤ |a| * (|a| / 2) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left h.le (abs_nonneg a)
      have h3 : a * (D t / t ^ r) = a ^ 2 + a * (D t / t ^ r - a) := by ring
      rw [h3, ← sq_abs a]
      linarith [neg_abs_le (a * (D t / t ^ r - a))]
    have h4 : t⁻¹ ≤ t ^ r := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_ge ht0 (hδ' t ht).2.2.le hr
    have h5 : a * D t = a * (D t / t ^ r) * t ^ r := by rw [mul_assoc, div_mul_cancel₀ _ hpow.ne']
    rw [h5, div_eq_mul_inv]
    calc |a| ^ 2 / 2 * t⁻¹ ≤ |a| ^ 2 / 2 * t ^ r := by gcongr
      _ ≤ a * (D t / t ^ r) * t ^ r := by gcongr
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hclose
  refine ⟨r + 1, by linarith, 2 * |a|, ε, hε, fun t ht ↦ ?_⟩
  have hpow : 0 < t ^ r := Real.rpow_pos_of_pos ht.1 r
  have h : |D t / t ^ r - a| < |a| / 2 := hsub ht
  have h1 : |D t / t ^ r| < 2 * |a| := by
    have := abs_sub_abs_le_abs_sub (D t / t ^ r) a
    linarith
  rw [abs_div, abs_of_pos hpow, div_lt_iff₀ hpow] at h1
  rw [add_sub_cancel_right]
  exact h1.le

end TauCeti

end
