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
* `mfderiv_chartAt_symm_of_chartAt_eq`: at a point `z` of the target of the chart at `x` whose
  preimage has the same preferred chart, the differential of the inverse chart is the identity.

The proofs reduce to Mathlib's `tangentCoordChange_self` and
`mfderiv_chartAt_eq_tangentCoordChange`, and, for the inverse chart, to the chain rule applied to
the chart composed with its inverse, which is the identity near `z`.
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

/-- Let `z` be a point of the target of the chart at `x` whose preimage under that chart has the
same preferred chart. Then the differential at `z` of the inverse of the chart at `x` is the
identity of the model vector space. -/
@[simp]
theorem mfderiv_chartAt_symm_of_chartAt_eq {x : M} {z : H} (hz : z ∈ (chartAt H x).target)
    (h : chartAt H ((chartAt H x).symm z) = chartAt H x) :
    mfderiv I I (chartAt H x).symm z = ContinuousLinearMap.id 𝕜 (TangentSpace I z) := by
  have hsymm := mdifferentiableAt_atlas_symm (I := I) (chart_mem_atlas H x) hz
  have hchart := mdifferentiableAt_atlas (I := I) (chart_mem_atlas H x)
    ((chartAt H x).map_target hz)
  have hid : mfderiv I I (chartAt H x ∘ (chartAt H x).symm) z =
      ContinuousLinearMap.id 𝕜 (TangentSpace I z) :=
    ((hasMFDerivAt_id z).congr_of_eventuallyEq_abuse
      ((chartAt H x).eventually_right_inverse hz)).mfderiv
  have hcomp := mfderiv_comp z hchart hsymm
  rw [hid, mfderiv_chartAt_of_chartAt_eq h] at hcomp
  ext v
  -- `ContinuousLinearMap.comp_apply` does not rewrite here, since the tangent spaces of `H` and of
  -- `M` carry different instances, though both are those of `E`; the sides agree by definition.
  exact congr($hcomp v).symm
