/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous functions with vanishing integrals over initial intervals

A continuous function `g : ℝ → E` all of whose integrals `∫ u in a..s, g u`, `s ∈ [a, b]`,
vanish is zero on `[a, b]`, for `a < b`
(`Continuous.eqOn_zero_of_forall_intervalIntegral_eq_zero`). On `(a, b)`, `g` is the derivative
of these integrals (Mathlib's `Continuous.deriv_integral`), which are constant; at the ends it
vanishes by continuity.
-/

public section

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {g : ℝ → E} {a b : ℝ}

/-- A continuous function whose integrals over `[a, s]` vanish for every `s ∈ [a, b]`, where
`a < b`, is zero on `[a, b]`. -/
theorem Continuous.eqOn_zero_of_forall_intervalIntegral_eq_zero (hg : Continuous g)
    (hab : a < b) (h : ∀ s ∈ Icc a b, ∫ u in a..s, g u = 0) : EqOn g 0 (Icc a b) := by
  have hzero : EqOn g 0 (Ioo a b) := fun s hs ↦ by
    have hF : (fun r ↦ ∫ u in a..r, g u) =ᶠ[𝓝 s] fun _ ↦ 0 :=
      mem_of_superset (Ioo_mem_nhds hs.1 hs.2) fun r hr ↦ h r (Ioo_subset_Icc_self hr)
    rw [← hg.deriv_integral g a s, hF.deriv_eq, deriv_const, Pi.zero_apply]
  exact hzero.of_subset_closure hg.continuousOn continuousOn_const Ioo_subset_Icc_self
    (closure_Ioo hab.ne).ge

end
