/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Functions with vanishing integrals over initial intervals

A function `g : ℝ → E`, continuous on `[a, b]`, all of whose integrals `∫ u in a..s, g u`,
`s ∈ [a, b]`, vanish is zero on `[a, b]`, for `a < b`
(`ContinuousOn.eqOn_zero_of_forall_intervalIntegral_eq_zero`). On `(a, b)`, `g` is the
derivative of these integrals (Mathlib's `intervalIntegral.integral_hasDerivAt_right`), which
are constant; at the ends it vanishes by continuity.
-/

public section

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {g : ℝ → E} {a b : ℝ}

/-- A function continuous on `[a, b]`, where `a < b`, whose integrals over `[a, s]` vanish for
every `s ∈ [a, b]`, is zero on `[a, b]`. -/
theorem ContinuousOn.eqOn_zero_of_forall_intervalIntegral_eq_zero
    (hg : ContinuousOn g (Icc a b)) (hab : a < b) (h : ∀ s ∈ Icc a b, ∫ u in a..s, g u = 0) :
    EqOn g 0 (Icc a b) := by
  have hzero : EqOn g 0 (Ioo a b) := fun s hs ↦ by
    have hs' : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hd := intervalIntegral.integral_hasDerivAt_right
      ((hg.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
      (nhdsWithin_eq_nhds.2 hs' ▸ hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s)
      (hg.continuousAt hs')
    have hF : (fun r ↦ ∫ u in a..r, g u) =ᶠ[𝓝 s] fun _ ↦ 0 :=
      mem_of_superset (Ioo_mem_nhds hs.1 hs.2) fun r hr ↦ h r (Ioo_subset_Icc_self hr)
    exact hd.unique ((hasDerivAt_const s (0 : E)).congr_of_eventuallyEq hF)
  exact hzero.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (closure_Ioo hab.ne).ge

end
