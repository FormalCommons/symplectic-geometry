/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exponentially weighted means of finitely many reals

Given finitely many reals `c i` with nonnegative weights `p i`, not all zero, the mean of the
`c i` weighted by `p i * exp (t * c i)` tends to the largest `c i` of positive weight as
`t → ∞`: dividing the weights by `exp (t * a)`, with `a` that largest value, the weights of the
`c i < a` tend to `0` and the others stay constant. This is the limit of the Rayleigh quotient
of a Hermitian matrix along its exponential curve, [GeorgoulasRobbinSalamon2021], Lemma 8.4.

## Main results

* `Real.tendsto_sum_mul_exp_div_sum_exp`: the exponentially weighted mean tends to the largest
  value of positive weight.

## References

* [V. Georgoulas, J. W. Robbin, D. A. Salamon, *The moment-weight inequality and the
  Hilbert–Mumford criterion*][GeorgoulasRobbinSalamon2021]
-/

public section

open Filter Finset
open scoped Topology

namespace Real

/-- For finitely many reals `c i` with nonnegative weights `p i`, if `a` is the largest `c i`
with `p i ≠ 0`, the mean of the `c i` weighted by `p i * exp (t * c i)` tends to `a` as
`t → ∞`. -/
theorem tendsto_sum_mul_exp_div_sum_exp {ι : Type*} [Fintype ι] {p c : ι → ℝ} {a : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hle : ∀ i, p i ≠ 0 → c i ≤ a) (ha : ∃ i, p i ≠ 0 ∧ c i = a) :
    Tendsto (fun t ↦ (∑ i, c i * p i * exp (t * c i)) / ∑ i, p i * exp (t * c i)) atTop
      (𝓝 a) := by
  classical
  set q : ι → ℝ := fun i ↦ if c i = a then p i else 0 with hq
  have hf (i : ι) : Tendsto (fun t ↦ p i * exp (t * (c i - a))) atTop (𝓝 (q i)) := by
    by_cases h0 : p i = 0
    · simp [hq, h0]
    by_cases hca : c i = a
    · simp [hq, hca]
    have hlt : c i - a < 0 := sub_neg.mpr ((hle i h0).lt_of_ne hca)
    simpa [hq, hca] using (tendsto_exp_atBot.comp
      (tendsto_id.atTop_mul_const_of_neg hlt)).const_mul (p i)
  have hpos : 0 < ∑ i, q i := by
    obtain ⟨j, hj, hja⟩ := ha
    refine sum_pos' (fun i _ ↦ ?_) ⟨j, mem_univ j, ?_⟩
    · simp only [hq]; split_ifs <;> simp [hp i]
    · simpa [hq, hja] using (hp j).lt_of_ne' hj
  have hnum : ∑ i, c i * q i = a * ∑ i, q i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hq]; split_ifs with h <;> simp [h]
  have hlim := (tendsto_finsetSum univ fun i _ ↦ (hf i).const_mul (c i)).div
    (tendsto_finsetSum univ fun i _ ↦ hf i) hpos.ne'
  rw [hnum, mul_div_cancel_right₀ _ hpos.ne'] at hlim
  refine hlim.congr fun t ↦ ?_
  have he (i : ι) : exp (t * c i) = exp (t * (c i - a)) * exp (t * a) := by
    rw [← exp_add]; ring_nf
  simp only [he, ← mul_assoc, ← sum_mul]
  rw [mul_div_mul_right _ _ (exp_pos _).ne', Pi.div_apply]

end Real

end
