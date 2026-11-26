/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# Set averages bounded through lower integrals

* `MeasureTheory.sub_setAverage_le_of_setLIntegral_ofReal_sub_le`: if a real function `u` is
  integrable on a set `s` of finite positive measure and at most `K` almost everywhere on it,
  then a bound `∫⁻ x in s, ofReal (K - u x) ∂μ ≤ μ s * ofReal L` gives `K - ⨍ x in s, u x ∂μ ≤ L`.

Such bounds on lower integrals are what one gets from a sub-mean value inequality whose integrand
`K - u` is nonnegative, and this lemma turns them into a lower bound on the average of `u`.
-/

public section

namespace MeasureTheory

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- If `u` is integrable on a set `s` with `0 < μ s < ∞` and `u ≤ K` almost everywhere on `s`,
then `∫⁻ x in s, ofReal (K - u x) ∂μ ≤ μ s * ofReal L`, with `0 ≤ L`, gives
`K - ⨍ x in s, u x ∂μ ≤ L`. -/
theorem sub_setAverage_le_of_setLIntegral_ofReal_sub_le
    {μ : Measure α} {s : Set α} {u : α → ℝ} {K L : ℝ}
    (h0 : μ s ≠ 0) (hfin : μ s ≠ ∞) (hu : IntegrableOn u s μ)
    (hK : ∀ᵐ x ∂μ.restrict s, u x ≤ K) (hL : 0 ≤ L)
    (h : ∫⁻ x in s, ENNReal.ofReal (K - u x) ∂μ ≤ μ s * ENNReal.ofReal L) :
    K - ⨍ x in s, u x ∂μ ≤ L := by
  have hint : IntegrableOn (fun x => K - u x) s μ := (integrableOn_const hfin).sub hu
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin),
    ← ofReal_setAverage hint (hK.mono fun _ => sub_nonneg.2), ENNReal.ofReal_le_ofReal_iff hL,
    setAverage_fun_sub (integrableOn_const hfin) hu, setAverage_const h0 hfin] at h
  exact h

end MeasureTheory

end
