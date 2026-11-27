/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Norms of Sobolev sections of chart data

Basic facts about the norm on `TauCeti.SectionChartData.sobolevSections`, the space of chart data
of Sobolev sections of a vector bundle, with the maximum over the charts of the `W^{k,p}` norms of
the chart parts as its norm.

## Main results

* `TauCeti.SectionChartData.norm_coe_apply_le`: the chart-`i` part of an element of the Sobolev
  sections of chart data has norm at most that of the element. Tau Ceti's
  `TauCeti.SectionChartData.norm_component_le` is the same bound for a single coordinate of the
  chart-`i` part.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] {C : SectionChartData E F S}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- The chart-`i` part of an element of the Sobolev sections has norm at most the norm of the
element, the maximum over the charts. -/
theorem norm_coe_apply_le (w : C.sobolevSections μ p k) (i : Fin C.n) :
    ‖(w : C.SobolevData μ p k) i‖ ≤ ‖w‖ :=
  norm_le_pi_norm _ i

end SectionChartData

end TauCeti

end
