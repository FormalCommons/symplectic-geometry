/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.Deriv.MeanValue

/-!
# Functions whose derivative is at least `k / t` near `0⁺`

A real function whose derivative is at least `k / t`, with `k > 0`, on an interval `(0, δ)`
stays below `C + k * log t` there, so it tends to `-∞` as `t → 0⁺`
(`Real.tendsto_atBot_nhdsGT_zero_of_div_le_deriv`): the function minus `k * log` is monotone,
and `log t → -∞` as `t → 0⁺`.

As a consequence, if `g` is bounded and differentiable on some `(0, ε)` and
`deriv g t / t ^ r` has a nonzero limit as `t → 0⁺`, then `r > -1`
(`Real.neg_one_lt_of_tendsto_deriv_div_rpow`): for `r ≤ -1`, the function `a * g`, where `a`
is the limit, would have derivative at least `(a ^ 2 / 2) / t` near `0⁺`.
-/

public section

open Filter Set Topology

namespace Real

/-- A real function `g`, differentiable on `(0, δ)`, whose derivative is at least `k / t` with
`k > 0` at each `t` of that interval, tends to `-∞` as `t → 0⁺`. -/
theorem tendsto_atBot_nhdsGT_zero_of_div_le_deriv {g : ℝ → ℝ} {k δ : ℝ} (hk : 0 < k)
    (hδ : 0 < δ) (hd : DifferentiableOn ℝ g (Ioo 0 δ))
    (hD : ∀ t ∈ Ioo 0 δ, k / t ≤ deriv g t) : Tendsto g (𝓝[>] 0) atBot := by
  -- `t ↦ g t - k * log t` is monotone on `(0, δ)`.
  have hφ : ∀ t ∈ Ioo 0 δ, HasDerivAt (fun u ↦ g u - k * log u) (deriv g t - k * t⁻¹) t :=
    fun t ht ↦ ((hd t ht).differentiableAt (Ioo_mem_nhds ht.1 ht.2)).hasDerivAt.sub
      ((hasDerivAt_log ht.1.ne').const_mul k)
  have hmono : MonotoneOn (fun u ↦ g u - k * log u) (Ioo 0 δ) := by
    refine TauCeti.monotoneOn_of_hasDerivAt_nonneg (convex_Ioo 0 δ) hφ fun t ht ↦ ?_
    rw [interior_Ioo] at ht
    have := hD t ht
    rw [div_eq_mul_inv] at this
    linarith
  -- Compare `g u` with `g (δ / 2) - k * log (δ / 2) + k * log u` for `u < δ / 2`.
  have ht : δ / 2 ∈ Ioo 0 δ := ⟨by positivity, by linarith⟩
  refine tendsto_atBot_mono' _ ?_ (tendsto_atBot_add_const_left _
    (g (δ / 2) - k * log (δ / 2)) (tendsto_log_nhdsGT_zero.const_mul_atBot hk))
  filter_upwards [Ioo_mem_nhdsGT ht.1] with u hu
  have := hmono ⟨hu.1, hu.2.trans ht.2⟩ ht hu.2.le
  simp only at this
  linarith

/-- If `g` is differentiable and bounded on `(0, ε)`, with `ε > 0`, and `deriv g t / t ^ r`
tends to a nonzero limit as `t → 0⁺`, then `r > -1`. -/
theorem neg_one_lt_of_tendsto_deriv_div_rpow {g : ℝ → ℝ} {ε r a M : ℝ} (hε : 0 < ε)
    (hd : DifferentiableOn ℝ g (Ioo 0 ε)) (hM : ∀ t ∈ Ioo 0 ε, |g t| ≤ M) (ha : a ≠ 0)
    (hlim : Tendsto (fun t ↦ deriv g t / t ^ r) (𝓝[>] 0) (𝓝 a)) : -1 < r := by
  by_contra hr
  replace hr := not_lt.1 hr
  have h1 : ∀ᶠ t in 𝓝[>] 0, a ^ 2 / 2 < a * (deriv g t / t ^ r) :=
    (hlim.const_mul a).eventually_const_lt (by nlinarith [pow_pos (abs_pos.2 ha) 2, sq_abs a])
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (h1.and (Ioo_mem_nhdsGT (lt_min hε one_pos)))
  have hδ' : ∀ t ∈ Ioo 0 δ, t ∈ Ioo 0 ε ∧ t < 1 := fun t ht ↦ by
    have := (hsub ht).2.2
    simp only [lt_min_iff] at this
    exact ⟨⟨ht.1, this.1⟩, this.2⟩
  have hdδ : ∀ t ∈ Ioo 0 δ, DifferentiableAt ℝ g t := fun t ht ↦
    (hd t (hδ' t ht).1).differentiableAt (Ioo_mem_nhds ht.1 (hδ' t ht).1.2)
  -- The derivative of `a * g` is at least `(a ^ 2 / 2) / t` on `(0, δ)`.
  have htend := tendsto_atBot_nhdsGT_zero_of_div_le_deriv (g := fun t ↦ a * g t)
    (k := a ^ 2 / 2) (by positivity) hδ
    (fun t ht ↦ ((hdδ t ht).const_mul a).differentiableWithinAt)
    fun t ht ↦ by
      rw [deriv_const_mul a (hdδ t ht)]
      have hpow : 0 < t ^ r := rpow_pos_of_pos ht.1 r
      have h4 : t⁻¹ ≤ t ^ r := by
        rw [← rpow_neg_one]
        exact rpow_le_rpow_of_exponent_ge ht.1 (hδ' t ht).2.le hr
      have h5 : a * deriv g t = a * (deriv g t / t ^ r) * t ^ r := by
        rw [mul_assoc, div_mul_cancel₀ _ hpow.ne']
      rw [h5, div_eq_mul_inv]
      calc a ^ 2 / 2 * t⁻¹ ≤ a ^ 2 / 2 * t ^ r := by gcongr
        _ ≤ a * (deriv g t / t ^ r) * t ^ r := by gcongr; exact ((hsub ht).1).le
  -- But `a * g` is bounded below by `-(|a| * M)` there.
  obtain ⟨t, ht, hlt⟩ := ((eventually_mem_set.2 (Ioo_mem_nhdsGT hε)).and
    (htend.eventually_lt_atBot (-(|a| * M)))).exists
  have h2 : |a * g t| ≤ |a| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg a)
  linarith [neg_abs_le (a * g t)]

end Real

end
