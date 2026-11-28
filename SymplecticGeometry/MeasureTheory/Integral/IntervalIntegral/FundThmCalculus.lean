/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Consequences of the fundamental theorem of calculus

A function `g : ℝ → E`, continuous on `[a, b]`, all of whose integrals `∫ u in a..s, g u`,
`s ∈ [a, b]`, vanish is zero on `[a, b]`, for `a < b`
(`ContinuousOn.eqOn_zero_of_forall_intervalIntegral_eq_zero`). On `(a, b)`, `g` is the
derivative of these integrals (Tau Ceti's `ContinuousOn.integral_hasDerivAt_of_mem_Ioo`), which
are constant; at the ends it vanishes by continuity.

The derivative of a `T`-periodic function, differentiable on an interval of length `T` with an
integrable derivative there, integrates to zero over that interval
(`Function.Periodic.intervalIntegral_deriv_eq_zero`), by Mathlib's
`intervalIntegral.integral_deriv_eq_sub`.
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
    have hd := hg.integral_hasDerivAt_of_mem_Ioo hs
    have hF : (fun r ↦ ∫ u in a..r, g u) =ᶠ[𝓝 s] fun _ ↦ 0 :=
      mem_of_superset (Ioo_mem_nhds hs.1 hs.2) fun r hr ↦ h r (Ioo_subset_Icc_self hr)
    exact hd.unique ((hasDerivAt_const s (0 : E)).congr_of_eventuallyEq hF)
  exact hzero.of_subset_closure hg continuousOn_const Ioo_subset_Icc_self
    (closure_Ioo hab.ne).ge

/-- The derivative of a `T`-periodic function, differentiable on `[a, a + T]` with an integrable
derivative there, integrates to zero over `[a, a + T]`. -/
theorem Function.Periodic.intervalIntegral_deriv_eq_zero {T : ℝ} (hg : Function.Periodic g T)
    (hd : ∀ x ∈ uIcc a (a + T), DifferentiableAt ℝ g x)
    (hint : IntervalIntegrable (deriv g) MeasureTheory.volume a (a + T)) :
    ∫ x in a..a + T, deriv g x = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub hd hint, hg a, sub_self]

end
