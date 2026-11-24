/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure

/-!
# Integrating the symplectic volume form

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M` modelled on a space of dimension
`2 * n`, with its symplectic orientation
(`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`),
the orientation on which the volume form `σⁿ / n!` is positive. This file shows that integrating
the top form `f σⁿ / n!` against the symplectic orientation is integrating `f` against the
Liouville measure `|σⁿ / n!|` (`TauCeti.SmoothTwoForm.liouvilleMeasure`), for every continuous
compactly supported function `f`:

`∫_M f σⁿ / n! = ∫ f dλ_σ`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_smul_volumeForm`). It is the case of the
symplectic volume form of `TauCeti.integralTopForm_smul_eq_integral_measure`, and holds in every
dimension, including dimension `0`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press (2017), §5.6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16.
-/

public section

noncomputable section

open Module MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [hn : Fact (finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M}

/-- **Integrating the symplectic volume form is integrating against the Liouville measure.** For
a fiberwise nondegenerate two-form `σ` on a manifold modelled on a space of dimension `2 * n`,
and a continuous compactly supported function `f`, the integral of the top form `f σⁿ / n!`
against the symplectic orientation is the integral of `f` against the Liouville measure. -/
theorem IsNondegenerate.integralTopForm_smul_volumeForm (h : σ.IsNondegenerate) {f : M → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    integralTopForm (h.volumeOrientation hn.out) (fun x ↦ f x • (σ.volumeForm n).val x) =
      ∫ x, f x ∂σ.liouvilleMeasure n := by
  rw [liouvilleMeasure_def]
  -- The volume form is positive exactly on the bases of the symplectic orientation.
  exact integralTopForm_smul_eq_integral_measure _ ((σ.volumeForm n).isSmoothForm.of_le bot_le)
    (signBasis_orientationAt_mul_nonneg_of_iff _
      fun _ c ↦ h.orientation_eq_orientationAt_volumeOrientation_iff hn.out c) hf hc

end SmoothTwoForm

end TauCeti
