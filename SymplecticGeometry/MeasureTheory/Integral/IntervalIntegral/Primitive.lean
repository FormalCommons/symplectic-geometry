/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitives of functions on an open interval

Let `s ⊆ ℝ` be order-connected, `c ∈ s`, and `f : ℝ → E` a function into a complete real
normed space. This file studies the primitive `t ↦ ∫ u in c..t, f u` of `f` on `s`, where `f`
need not be continuous, or even defined in a useful way, outside `s`. For the derivative as a
function and for smoothness, `s` is moreover open (an open interval, possibly unbounded).

## Main results

* `ContinuousOn.integral_hasStrictDerivAt_of_ordConnected`: if `f` is continuous on `s`, the
  primitive has strict derivative `f t` at every `t` of which `s` is a neighbourhood.
* `ContinuousOn.eqOn_deriv_integral_of_ordConnected`: for open `s`, the derivative of the
  primitive is `f` on `s`.
* `ContDiffOn.contDiffOn_add_one_integral`: for open `s`, if `f` is `C^k` on `s`, the primitive
  is `C^(k+1)` on `s`.

These are the versions on an interval of Mathlib's `Continuous.integral_hasStrictDerivAt` and
`Continuous.deriv_integral`, and of Tau Ceti's `ContDiff.contDiff_add_one_integral`, whose
proof `ContDiffOn.contDiffOn_add_one_integral` follows, with `contDiffOn_succ_iff_deriv_of_isOpen`
in place of `contDiff_succ_iff_deriv`. The first one also contains Tau Ceti's
`ContinuousOn.integral_hasDerivAt_of_mem_Ioo`, the case `s = Icc a b`, `t ∈ Ioo a b`.
-/

public section

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E} {s : Set ℝ} {c t : ℝ}

/-- **FTC-1 on an order-connected set.** If `f` is continuous on an order-connected set `s`
containing `c`, and `s` is a neighbourhood of `t`, then `u ↦ ∫ x in c..u, f x` has strict
derivative `f t` at `t`. -/
theorem ContinuousOn.integral_hasStrictDerivAt_of_ordConnected (hf : ContinuousOn f s)
    (hs : s.OrdConnected) (hc : c ∈ s) (ht : s ∈ 𝓝 t) :
    HasStrictDerivAt (fun u ↦ ∫ x in c..u, f x) (f t) t :=
  intervalIntegral.integral_hasStrictDerivAt_right
    (hf.mono (hs.uIcc_subset hc (mem_of_mem_nhds ht))).intervalIntegrable
    ((hf.mono interior_subset).stronglyMeasurableAtFilter isOpen_interior t
      (mem_interior_iff_mem_nhds.2 ht))
    (hf.continuousAt ht)

/-- If `f` is continuous on an open order-connected set `s` and `c ∈ s`, then the derivative of
`u ↦ ∫ x in c..u, f x` is `f` on `s`. -/
theorem ContinuousOn.eqOn_deriv_integral_of_ordConnected (hf : ContinuousOn f s)
    (hs : IsOpen s) (hs' : s.OrdConnected) (hc : c ∈ s) :
    EqOn (deriv fun u ↦ ∫ x in c..u, f x) f s := fun _ ht ↦
  (hf.integral_hasStrictDerivAt_of_ordConnected hs' hc (hs.mem_nhds ht)).hasDerivAt.deriv

/-- If `f` is `C^k` on an open order-connected set `s` and `c ∈ s`, then its primitive
`u ↦ ∫ x in c..u, f x` is `C^(k+1)` on `s`. -/
theorem ContDiffOn.contDiffOn_add_one_integral {k : ℕ∞} (hf : ContDiffOn ℝ k f s)
    (hs : IsOpen s) (hs' : s.OrdConnected) (hc : c ∈ s) :
    ContDiffOn ℝ (k + 1) (fun u ↦ ∫ x in c..u, f x) s :=
  (contDiffOn_succ_iff_deriv_of_isOpen hs).2
    ⟨fun _ ht ↦ (hf.continuousOn.integral_hasStrictDerivAt_of_ordConnected hs' hc
      (hs.mem_nhds ht)).hasDerivAt.differentiableAt.differentiableWithinAt, by simp,
      hf.congr (hf.continuousOn.eqOn_deriv_integral_of_ordConnected hs hs' hc)⟩

end
