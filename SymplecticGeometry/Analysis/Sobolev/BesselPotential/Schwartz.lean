/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Directional derivatives of Schwartz functions in `H^{s,p}`

For a Schwartz function `u` and a vector `v`, the element of `H^{s,p}` given by `∂_v u` is the
image of the element of `H^{s+1,p}` given by `u` under Tau Ceti's directional derivative
`BesselPotentialSpace.lineDerivCLM` (`SchwartzMap.toBesselPotentialSpaceCLM_lineDerivOp`). Both
are determined by their tempered distributions (`BesselPotentialSpace.ext`), and the tempered
distribution of `∂_v u` is `∂_v` of that of `u` (Mathlib's
`TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq`).

This moves the bounds of Tau Ceti's `lineDerivCLM` to Schwartz functions: with
`BesselPotentialSpace.norm_lineDerivCLM_apply_le` it gives
`‖∂_v u‖_{H^s} ≤ 2π ‖v‖ ‖u‖_{H^{s+1}}` at `p = 2`.

## Main results

* `SchwartzMap.toBesselPotentialSpaceCLM_lineDerivOp`: `∂_v` commutes with the inclusion of
  Schwartz functions into the Bessel potential scale.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the Sobolev spaces `H_s` and their Fourier description).
-/

public section

open scoped SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace SchwartzMap

/-- For `1 < p < ∞`, the element of `H^{s,p}` given by the directional derivative `∂_v u` of a
Schwartz function `u` is `∂_v` applied to the element of `H^{s+1,p}` given by `u`. -/
theorem toBesselPotentialSpaceCLM_lineDerivOp {s : ℝ} {p : ENNReal} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ⊤) (v : E) (u : 𝓢(E, F)) :
    toBesselPotentialSpaceCLM s p (∂_{v} u) =
      BesselPotentialSpace.lineDerivCLM hp hp_top v (toBesselPotentialSpaceCLM (s + 1) p u) := by
  ext1
  rw [BesselPotentialSpace.toDistr_lineDerivCLM, toDistr_toBesselPotentialSpaceCLM,
    toDistr_toBesselPotentialSpaceCLM,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]

end SchwartzMap

end
