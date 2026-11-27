/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict

/-!
# The extended chart at a point, centred at that point

For a manifold `M` modelled on a boundaryless `I : ModelWithCorners 𝕜 E H` and a point `x : M`,
`SymplecticGeometry.centeredExtChartAt I x : OpenPartialHomeomorph M E` is the extended chart
of `M` at `x` followed by the translation of `E` that sends the coordinate of `x` to the origin,
built with Tau Ceti's `OpenPartialHomeomorph.extendTrans`. Its source is that of the chart at
`x` (`centeredExtChartAt_source`), it sends `y` to `extChartAt I x y - extChartAt I x x`
(`centeredExtChartAt_apply`), its inverse and target are given by
`centeredExtChartAt_symm_apply` and `centeredExtChartAt_target`, and, restricted to its source,
it vanishes at `x` only (`sourceRestrict_centeredExtChartAt_preimage_zero`, from
`OpenPartialHomeomorph.sourceRestrict_preimage_singleton`).

## Main definitions

* `SymplecticGeometry.centeredExtChartAt`: the extended chart of a manifold at a point,
  translated in the model space so that the point goes to the origin.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace SymplecticGeometry


variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (x : M)

/-- The extended chart of `M` at `x`, translated in the model space so that `x` goes to the
origin: `y ↦ extChartAt I x y - extChartAt I x x` on the source of the chart at `x`
(`centeredExtChartAt_apply`). -/
def centeredExtChartAt : OpenPartialHomeomorph M E :=
  (chartAt H x).extendTrans I (Homeomorph.subRight (extChartAt I x x))

/-- The centred chart at `x` is the chart at `x`, read in the model space through `I` and
translated by the coordinate of `x`. -/
theorem centeredExtChartAt_def :
    centeredExtChartAt I x =
      (chartAt H x).extendTrans I (Homeomorph.subRight (extChartAt I x x)) :=
  (rfl)

/-- The source of the centred chart at `x` is that of the chart at `x`. -/
@[simp]
theorem centeredExtChartAt_source : (centeredExtChartAt I x).source = (chartAt H x).source := by
  simp [centeredExtChartAt_def]

/-- The point `x` lies in the source of its centred chart. -/
theorem mem_centeredExtChartAt_source : x ∈ (centeredExtChartAt I x).source := by
  simp

/-- The centred chart at `x` sends `y` to the coordinate of `y` minus that of `x`. -/
@[simp]
theorem centeredExtChartAt_apply (y : M) :
    centeredExtChartAt I x y = extChartAt I x y - extChartAt I x x := by
  simp [centeredExtChartAt_def]

/-- The centred chart at `x` sends `x` to the origin. -/
theorem centeredExtChartAt_self : centeredExtChartAt I x x = 0 := by
  simp

/-- The inverse of the centred chart at `x` translates back by the coordinate of `x` and applies
the inverse of the extended chart at `x`. -/
@[simp]
theorem centeredExtChartAt_symm_apply (v : E) :
    (centeredExtChartAt I x).symm v = (extChartAt I x).symm (v + extChartAt I x x) := by
  simp [centeredExtChartAt_def]

/-- The target of the centred chart at `x` is that of the extended chart at `x`, translated by
minus the coordinate of `x`. -/
theorem centeredExtChartAt_target :
    (centeredExtChartAt I x).target = (· + extChartAt I x x) ⁻¹' (extChartAt I x).target := by
  ext v
  simp [centeredExtChartAt_def, I.range_eq_univ]

/-- On its source, the centred chart at `x` vanishes at `x` only. -/
theorem sourceRestrict_centeredExtChartAt_preimage_zero :
    (centeredExtChartAt I x).sourceRestrict ⁻¹' {0} = {⟨x, mem_centeredExtChartAt_source I x⟩} := by
  rw [← centeredExtChartAt_self I x]
  exact (centeredExtChartAt I x).sourceRestrict_preimage_singleton _

end SymplecticGeometry

end

end
