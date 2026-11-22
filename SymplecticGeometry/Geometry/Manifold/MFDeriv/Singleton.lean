/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Tangent coordinate changes and chart differentials when charts coincide

On a manifold whose atlas has a single chart, such as one built with
`OpenPartialHomeomorph.singletonChartedSpace` or `Topology.IsOpenEmbedding.singletonChartedSpace`,
the tangent bundle is trivialized by that chart, and the differentials of the chart and of its
inverse are the identity of the model vector space. This file states these facts for any charted
space, at points whose preferred charts coincide; on a one-chart manifold that hypothesis holds by
`rfl`.

## Main results

* `tangentCoordChange_of_chartAt_eq`: if `chartAt H x = chartAt H y`, the tangent coordinate
  change from `x` to `y` is the identity on the source of that chart.
* `mfderiv_chartAt_of_chartAt_eq`: if `chartAt H x = chartAt H y`, the differential at `x` of the
  chart at `y` is the identity.
* `mfderiv_chartAt_symm_eq_tangentCoordChange`: at a point `z` of the target of the chart at `x`,
  the differential of the inverse chart is a tangent coordinate change. It needs no hypothesis on
  the charts.
* `mfderiv_chartAt_symm_of_chartAt_eq`: at a point `z` of the target of the chart at `x` whose
  preimage has the same preferred chart, the differential of the inverse chart is the identity.

The proofs reduce to Mathlib's `tangentCoordChange_self` and
`mfderiv_chartAt_eq_tangentCoordChange`. For the inverse chart, the chain rule applied to the
chart composed with its inverse, which is the identity near `z`, and `tangentCoordChange_comp` give
its differential as a tangent coordinate change.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- If the preferred charts at `x` and `y` coincide, the tangent coordinate change from `x` to `y`
is the identity at every point `z` of the source of that chart. -/
theorem tangentCoordChange_of_chartAt_eq {x y z : M} (h : chartAt H x = chartAt H y)
    (hz : z ∈ (chartAt H x).source) :
    tangentCoordChange I x y z = ContinuousLinearMap.id 𝕜 E := by
  have hext : extChartAt I y = extChartAt I x := by simp only [extChartAt, h]
  ext v
  rw [tangentCoordChange_def, hext, ← tangentCoordChange_def,
    tangentCoordChange_self (by simpa using hz), ContinuousLinearMap.id_apply]

/-- If the preferred charts at `x` and `y` coincide, the differential at `x` of the chart at `y`
is the identity of the model vector space. -/
@[simp]
theorem mfderiv_chartAt_of_chartAt_eq {x y : M} (h : chartAt H x = chartAt H y) :
    mfderiv I I (chartAt H y) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [mfderiv_chartAt_eq_tangentCoordChange (h ▸ mem_chart_source H x),
    tangentCoordChange_of_chartAt_eq h (mem_chart_source H x)]
  rfl

/-- At a point `z` of the target of the chart at `x`, the differential of the inverse of that
chart is the tangent coordinate change from `x` to the preimage `(chartAt H x).symm z`, taken at
that preimage. This is the counterpart for inverse charts of
`mfderiv_chartAt_eq_tangentCoordChange`. -/
theorem mfderiv_chartAt_symm_eq_tangentCoordChange {x : M} {z : H}
    (hz : z ∈ (chartAt H x).target) :
    mfderiv I I (chartAt H x).symm z =
      tangentCoordChange I x ((chartAt H x).symm z) ((chartAt H x).symm z) := by
  have hp := (chartAt H x).map_target hz
  have hsymm := mdifferentiableAt_atlas_symm (I := I) (chart_mem_atlas H x) hz
  have hchart := mdifferentiableAt_atlas (I := I) (chart_mem_atlas H x) hp
  have hid : mfderiv I I (chartAt H x ∘ (chartAt H x).symm) z =
      ContinuousLinearMap.id 𝕜 (TangentSpace I z) :=
    ((hasMFDerivAt_id z).congr_of_eventuallyEq_abuse
      ((chartAt H x).eventually_right_inverse hz)).mfderiv
  have hcomp := mfderiv_comp z hchart hsymm
  rw [hid, mfderiv_chartAt_eq_tangentCoordChange hp] at hcomp
  have hpx : (chartAt H x).symm z ∈ (extChartAt I x).source := by simpa using hp
  have hpp : (chartAt H x).symm z ∈ (extChartAt I ((chartAt H x).symm z)).source :=
    mem_extChartAt_source _
  ext v
  -- `ContinuousLinearMap.comp_apply` does not rewrite here, since the tangent spaces of `H` and of
  -- `M` carry different instances, though both are those of `E`; the sides agree by definition.
  have hv : v = tangentCoordChange I ((chartAt H x).symm z) x ((chartAt H x).symm z)
      (mfderiv I I (chartAt H x).symm z v) := congr($hcomp v)
  have key : ∀ u : E, tangentCoordChange I x ((chartAt H x).symm z) ((chartAt H x).symm z)
      (tangentCoordChange I ((chartAt H x).symm z) x ((chartAt H x).symm z) u) = u := fun u => by
    rw [tangentCoordChange_comp ⟨⟨hpp, hpx⟩, hpp⟩, tangentCoordChange_self hpp]
  have hk := key (mfderiv I I (chartAt H x).symm z v)
  rw [← hv] at hk
  exact hk.symm

/-- Let `z` be a point of the target of the chart at `x` whose preimage under that chart has the
same preferred chart. Then the differential at `z` of the inverse of the chart at `x` is the
identity of the model vector space. -/
@[simp]
theorem mfderiv_chartAt_symm_of_chartAt_eq {x : M} {z : H} (hz : z ∈ (chartAt H x).target)
    (h : chartAt H ((chartAt H x).symm z) = chartAt H x) :
    mfderiv I I (chartAt H x).symm z = ContinuousLinearMap.id 𝕜 (TangentSpace I z) := by
  rw [mfderiv_chartAt_symm_eq_tangentCoordChange hz,
    tangentCoordChange_of_chartAt_eq h.symm ((chartAt H x).map_target hz)]
  rfl
