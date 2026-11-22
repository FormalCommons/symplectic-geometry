/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability under a change of variables by a homeomorphism

If `f` is locally integrable on a set `t` for the image `μ.map e` of a measure `μ` under a
homeomorphism `e`, then `f ∘ e` is locally integrable for `μ` on every set that `e` maps into `t`
(`MeasureTheory.LocallyIntegrableOn.comp_homeomorph_of_mapsTo`). This is the local form, on a
subset, of Mathlib's `MeasureTheory.locallyIntegrable_map_homeomorph`, whose proof it adapts.
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

end
