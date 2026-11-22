/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability under a homeomorphism and under scaling of the measure

If `f` is locally integrable on a set `t` for the image `μ.map e` of a measure `μ` under a
homeomorphism `e`, then `f ∘ e` is locally integrable for `μ` on every set that `e` maps into `t`
(`MeasureTheory.LocallyIntegrableOn.comp_homeomorph_of_mapsTo`). This is the local form, on a
subset, of Mathlib's `MeasureTheory.locallyIntegrable_map_homeomorph`, whose proof it adapts.

It also shows that multiplying the measure by a nonzero finite constant does not change local
integrability (`MeasureTheory.locallyIntegrableOn_smul_measure_iff`), the local form of Mathlib's
`MeasureTheory.integrable_smul_measure`.
-/

public section

open Set

namespace MeasureTheory.LocallyIntegrableOn

variable {X Y ε : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace ε]
  [ContinuousENorm ε]

/-- If `f` is locally integrable on `t` for the image of `μ` under a homeomorphism `e`, then
`f ∘ e` is locally integrable for `μ` on any set `s` that `e` maps into `t`. -/
theorem comp_homeomorph_of_mapsTo {μ : Measure X} {f : Y → ε} {s : Set X} {t : Set Y}
    {e : X ≃ₜ Y} (hf : LocallyIntegrableOn f t (μ.map e)) (hst : MapsTo e s t) :
    LocallyIntegrableOn (f ∘ e) s μ := by
  intro x hx
  obtain ⟨u, hu, hfu⟩ := hf (e x) (hst hx)
  exact ⟨e ⁻¹' u, e.continuous.continuousWithinAt.tendsto_nhdsWithin hst hu,
    (integrableOn_map_equiv e.toMeasurableEquiv).1 hfu⟩

end MeasureTheory.LocallyIntegrableOn

namespace MeasureTheory

/-- For `c ≠ 0` and `c ≠ ∞`, `u` is locally integrable on `s` for `c • μ` if and only if it is
for `μ`. -/
theorem locallyIntegrableOn_smul_measure_iff {X ε : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [TopologicalSpace ε] [ESeminormedAddMonoid ε] {μ : Measure X}
    {s : Set X} {u : X → ε} {c : ENNReal} (h0 : c ≠ 0) (htop : c ≠ ⊤) :
    LocallyIntegrableOn u s (c • μ) ↔ LocallyIntegrableOn u s μ :=
  ⟨fun h ↦ by
    simpa [smul_smul, ENNReal.inv_mul_cancel h0 htop] using
      h.smul_measure (ENNReal.inv_ne_top.2 h0),
    fun h ↦ h.smul_measure htop⟩

end MeasureTheory

end
