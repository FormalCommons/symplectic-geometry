/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import SymplecticGeometry.Topology.OpenPartialHomeomorph.Ball

/-!
# The extended chart at a point, centred at that point

For a manifold `M` modelled on a boundaryless `I : ModelWithCorners 𝕜 E H` and a point `x : M`,
`SymplecticGeometry.centeredExtChartAt I x : OpenPartialHomeomorph M E` is the extended chart
of `M` at `x` followed by the translation of `E` that sends the coordinate of `x` to the origin,
built with Tau Ceti's `OpenPartialHomeomorph.extendTrans`. Its source is that of the chart at
`x` (`centeredExtChartAt_source`), it sends `y` to `extChartAt I x y - extChartAt I x x`
(`centeredExtChartAt_apply`), its inverse and target are given by
`centeredExtChartAt_symm_apply` and `centeredExtChartAt_target`, it is smooth on its source
(`contMDiffOn_centeredExtChartAt`, a case of Tau Ceti's
`OpenPartialHomeomorph.contMDiffOn_extendTrans`), and, restricted to its source,
it vanishes at `x` only (`sourceRestrict_centeredExtChartAt_preimage_zero`, from
`OpenPartialHomeomorph.sourceRestrict_preimage_singleton`). Its inverse carries some ball about
the origin into any given neighbourhood of `x`
(`exists_ball_mapsTo_centeredExtChartAt_symm`, a case of
`OpenPartialHomeomorph.exists_ball_subset_target_mapsTo_symm`).

## Main definitions

* `SymplecticGeometry.centeredExtChartAt`: the extended chart of a manifold at a point,
  translated in the model space so that the point goes to the origin.
-/

public section

noncomputable section

open Set
open scoped Manifold Topology

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

/-- The centred chart at `x` is `C^n` on its source, on a `C^n` manifold. -/
theorem contMDiffOn_centeredExtChartAt {n : WithTop ℕ∞} [IsManifold I n M] :
    ContMDiffOn I 𝓘(𝕜, E) n (centeredExtChartAt I x) (centeredExtChartAt I x).source := by
  rw [centeredExtChartAt_def]
  exact (chartAt H x).contMDiffOn_extendTrans (IsManifold.chart_mem_maximalAtlas x)
    (contDiff_id.sub contDiff_const)

/-- Near a point `x` of a manifold, the centred chart at `x` has a ball about `0` in its
target that its inverse carries into any given neighbourhood `T` of `x`. -/
theorem exists_ball_mapsTo_centeredExtChartAt_symm {T : Set M} (hT : T ∈ 𝓝 x) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ (centeredExtChartAt I x).target ∧
      MapsTo (centeredExtChartAt I x).symm (Metric.ball 0 ε) T := by
  simpa only [centeredExtChartAt_self] using
    (centeredExtChartAt I x).exists_ball_subset_target_mapsTo_symm
      (mem_centeredExtChartAt_source I x) hT

end SymplecticGeometry

end

end
