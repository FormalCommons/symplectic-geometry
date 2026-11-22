/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The support of the tempered distribution of an `Lᵖ` function

If an `Lᵖ` function `f` vanishes almost everywhere outside a closed set `K`, then every Schwartz
function supported away from `K` pairs to zero with `f`, so the support of the tempered
distribution of `f` lies in `K` (`MeasureTheory.Lp.dsupport_toTemperedDistribution_subset`).
Multiplying that distribution by a function of temperate growth that equals `1` on `K` does not
change it (`MeasureTheory.Lp.smulLeftCLM_toTemperedDistribution_of_eqOn`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2 (support of a
  distribution) and §7.1 (tempered distributions).
-/

public section

open scoped SchwartzMap

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {μ : Measure E}
  [μ.HasTemperateGrowth] {p : ENNReal} [Fact (1 ≤ p)]

/-- The tempered distribution of an `Lᵖ` function that vanishes almost everywhere outside a
closed set `K` is supported in `K`. -/
theorem dsupport_toTemperedDistribution_subset {f : Lp F p μ} {K : Set E} (hK : IsClosed K)
    (hf : ∀ᵐ x ∂μ, x ∉ K → f x = 0) :
    Distribution.dsupport (f : 𝓢'(E, F)) ⊆ K := by
  refine fun x hx ↦ (Distribution.mem_dsupport_iff x).1 hx K (fun g hg ↦ ?_) hK
  rw [toTemperedDistribution_apply]
  refine integral_eq_zero_of_ae (hf.mono fun y hy ↦ ?_)
  by_cases hyK : y ∈ K
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hg h hyK]
  · simp [hy hyK]

/-- Multiplying the tempered distribution of an `Lᵖ` function that vanishes almost everywhere
outside a set `K` by a function of temperate growth equal to `1` on `K` leaves it unchanged. -/
theorem smulLeftCLM_toTemperedDistribution_of_eqOn {f : Lp F p μ} {K : Set E} {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hgK : Set.EqOn g 1 K) (hf : ∀ᵐ x ∂μ, x ∉ K → f x = 0) :
    TemperedDistribution.smulLeftCLM F g (f : 𝓢'(E, F)) = f := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, toTemperedDistribution_apply,
    toTemperedDistribution_apply]
  refine integral_congr_ae (hf.mono fun y hy ↦ ?_)
  by_cases hyK : y ∈ K
  · simp [SchwartzMap.smulLeftCLM_apply_apply hg, hgK hyK]
  · simp [hy hyK]

end MeasureTheory.Lp

end
