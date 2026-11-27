/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The flow of a complete vector field read in a chart

Let `v` be a complete `C¹` vector field on a Hausdorff manifold with a boundaryless model `I`,
with flow `φ = TauCeti.globalFlow v`, and let `e` be the extended chart at a point `p`. Write
`V w = mpullback 𝓘(ℝ, E) I e.symm v (e p + w)` for the coordinate field of `v` in `e`,
recentred so that `p` sits at the origin. This file identifies the forward solutions of the
ordinary differential equation `y' = V y` on `[0, ∞)` that stay in the chart with the forward
orbits of `φ` that stay in the chart:

* `TauCeti.extChartAt_symm_add_eq_globalFlow`: if `y` is an integral curve of `V` on `[0, ∞)`
  with `e p + y t` in the chart target for `t ≥ 0`, then
  `e.symm (e p + y t) = φ_t (e.symm (e p + y 0))` for `t ≥ 0`;
* `TauCeti.isIntegralCurveOn_extChartAt_globalFlow_sub`: conversely, on a set of times at which
  the orbit of `x` stays in the chart source, `t ↦ e (φ_t x) - e p` is an integral curve of `V`.

When `v p = 0`, `V` vanishes at `0` with derivative the linearization of `v` at `p`
(`VectorField.mpullback_extChartAt_symm_self`,
`MDifferentiableAt.hasFDerivAt_mpullback_extChartAt_symm`), so these statements carry results
on the forward solutions near a rest point of a field on a normed space, such as local stable
graphs, over to the flow.

The first statement carries `y` to an integral curve of `v` by Tau Ceti's
`isMIntegralCurveOn_chartField` and then uses `IsMIntegralCurveOn.globalFlow_sub_eq_Ici`; the
second reads the orbit in the chart by Tau Ceti's
`HasMFDerivAt.hasDerivAt_extChartAt_comp_mpullbackWithin`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer, 2012, Chapter 9
  (integral curves in coordinates, Theorem 9.12).
-/

public section

open Set VectorField
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I 1 M] {v : (x : M) → TangentSpace I x}
  (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v)

/-- **Forward solutions in a chart are orbits.** Let `e` be the extended chart at `p`, and let
`y` be an integral curve on `[0, ∞)` of the coordinate field `w ↦ mpullback 𝓘(ℝ, E) I e.symm v
(e p + w)` of a complete `C¹` field `v`, recentred at `p`, with `e p + y t` in the chart target
for every `t ≥ 0`. Then for `t ≥ 0` the point `e.symm (e p + y t)` is the image of
`e.symm (e p + y 0)` under the flow of `v` at time `t`. -/
theorem extChartAt_symm_add_eq_globalFlow {p : M} {y : ℝ → E}
    (hy : IsIntegralCurveOn y
      (fun _ w ↦ mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v (extChartAt I p p + w)) (Ici 0))
    (hmem : ∀ t, 0 ≤ t → extChartAt I p p + y t ∈ (extChartAt I p).target) {t : ℝ}
    (ht : 0 ≤ t) :
    (extChartAt I p).symm (extChartAt I p p + y t) =
      globalFlow v hv hcomplete t ((extChartAt I p).symm (extChartAt I p p + y 0)) := by
  set e := extChartAt I p
  have hz : IsMIntegralCurveOn (fun s ↦ e p + y s) (mpullback 𝓘(ℝ, E) I e.symm v) (Ici 0) := by
    rw [isMIntegralCurveOn_iff_isIntegralCurveOn]
    exact fun s hs ↦ (hy s hs).const_add _
  have hc := isMIntegralCurveOn_chartField (I := I) (x := p) (fun s hs ↦ hmem s hs) hz
  -- On the chart target, the chart field of the coordinate field of `v` is `v`.
  have hγ : IsMIntegralCurveOn (fun s ↦ e.symm (e p + y s)) v (Ici 0) := fun s hs ↦ by
    have h := hc s hs
    have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := I) (hmem s hs)
    rw [I.range_eq_univ, mfderivWithin_univ] at hinv
    rwa [chartField_extChartAt_symm (hmem s hs) rfl, I.range_eq_univ, mfderivWithin_univ,
      mpullback_apply, hinv.self_apply_inverse] at h
  simpa using (hγ.globalFlow_sub_eq_Ici hv hcomplete ht).symm

/-- **Orbits in a chart are solutions.** Let `e` be the extended chart at `p`. On a set `s` of
times at which the orbit of `x` under the flow of a complete `C¹` field `v` lies in the chart
source, the curve `t ↦ e (φ_t x) - e p` is an integral curve of the coordinate field
`w ↦ mpullback 𝓘(ℝ, E) I e.symm v (e p + w)` of `v`, recentred at `p`. -/
theorem isIntegralCurveOn_extChartAt_globalFlow_sub {p x : M} {s : Set ℝ}
    (hmem : ∀ t ∈ s, globalFlow v hv hcomplete t x ∈ (extChartAt I p).source) :
    IsIntegralCurveOn (fun t ↦ extChartAt I p (globalFlow v hv hcomplete t x) - extChartAt I p p)
      (fun _ w ↦ mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v (extChartAt I p p + w)) s := by
  intro t ht
  have h := ((isMIntegralCurve_globalFlow hv hcomplete x t
    ).hasDerivAt_extChartAt_comp_mpullbackWithin (hmem t ht)).sub_const (extChartAt I p p)
  rw [I.range_eq_univ, mpullbackWithin_univ] at h
  -- The two derivatives differ only by `e p + (q - e p) = q`, inside a dependent type.
  exact h.hasDerivWithinAt.congr_deriv
    (congrArg (fun w : E ↦ (mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v w : E))
      (add_sub_cancel _ _).symm)

end TauCeti

end
