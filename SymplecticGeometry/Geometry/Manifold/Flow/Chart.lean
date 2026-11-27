/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import SymplecticGeometry.Geometry.Manifold.CenteredExtChartAt
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.VectorField.Chart
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.VectorField.Chart.Basic

/-!
# Integral curves and flows read in a chart

Let `v` be a vector field on a manifold with a boundaryless model `I`, let `e` be the extended
chart at a point `p`, and write `V = mpullback 𝓘(ℝ, E) I e.symm v` for the coordinate field of `v`
in `e`. This file relates the solutions of the ordinary differential equation `z' = V z` that
stay in the chart with the integral curves of `v` that stay in it:

* `IsIntegralCurveOn.isMIntegralCurveOn_extChartAt_symm`: a solution `z` of `V` on `J` with
  values in the chart target gives the integral curve `t ↦ e.symm (z t)` of `v` on `J`;
* `IsMIntegralCurveOn.isIntegralCurveOn_centeredExtChartAt`: if `γ` is an integral curve of `v`
  on a set of times at which it lies in the chart source, then `t ↦ c (γ t)` solves the
  recentred equation `y' = V (e p + y)` there, for `c` the centred chart `y ↦ e y - e p`
  (`SymplecticGeometry.centeredExtChartAt`).

For a complete `C¹` field on a Hausdorff manifold, with flow `φ = TauCeti.globalFlow v`, these
give:

* `TauCeti.extChartAt_symm_add_eq_globalFlow`: if `y` solves `y' = V (e p + y)` on `[0, ∞)`
  with `e p + y t` in the chart target for `t ≥ 0`, then
  `e.symm (e p + y t) = φ_t (e.symm (e p + y 0))` for `t ≥ 0`, by
  `IsMIntegralCurveOn.globalFlow_sub_eq_Ici`;
* `TauCeti.isIntegralCurveOn_centeredExtChartAt_globalFlow`: on a set of times at which the
  orbit of `x` stays in the chart source, `t ↦ c (φ_t x)` solves `y' = V (e p + y)`.

When `v p = 0`, `V` vanishes at `e p` with derivative the linearization of `v` at `p`
(`VectorField.mpullback_extChartAt_symm_self`,
`MDifferentiableAt.hasFDerivAt_mpullback_extChartAt_symm`), so these statements carry results
on the forward solutions near a rest point of a field on a normed space, such as local stable
graphs, over to the flow.

The first statement follows Tau Ceti's `TauCeti.isMIntegralCurveOn_chartField`, using that on
the chart target the chart field of `V` is `v`; the second reads the curve in the chart by
`HasMFDerivWithinAt.hasDerivWithinAt_extChartAt_comp_mpullbackWithin`, the within-set form of
Tau Ceti's `HasMFDerivAt.hasDerivAt_extChartAt_comp_mpullbackWithin`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapters 8 and 9 (vector fields and integral curves in coordinates).
-/

public section

open Set VectorField
open scoped Manifold

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {v : (x : M) → TangentSpace I x} {p : M} {J : Set ℝ}

/-- **Solutions in a chart are integral curves.** Let `e` be the extended chart at `p`. A
solution `z` on `J` of the coordinate field `mpullback 𝓘(ℝ, E) I e.symm v` of `v` that stays
in the chart target is carried by `e.symm` to an integral curve of `v` on `J`. -/
theorem IsIntegralCurveOn.isMIntegralCurveOn_extChartAt_symm {z : ℝ → E}
    (hz : IsIntegralCurveOn z (fun _ w ↦ mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v w) J)
    (hmem : ∀ t ∈ J, z t ∈ (extChartAt I p).target) :
    IsMIntegralCurveOn (fun t ↦ (extChartAt I p).symm (z t)) v J := fun t ht ↦ by
  have h := TauCeti.isMIntegralCurveOn_chartField (I := I) (x := p) hmem
    (TauCeti.isMIntegralCurveOn_iff_isIntegralCurveOn.2 hz) t ht
  -- On the chart target, the chart field of the coordinate field of `v` is `v`.
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := I) (hmem t ht)
  rw [I.range_eq_univ, mfderivWithin_univ] at hinv
  rwa [TauCeti.chartField_extChartAt_symm (hmem t ht) rfl, I.range_eq_univ, mfderivWithin_univ,
    mpullback_apply, hinv.self_apply_inverse] at h

/-- **Integral curves in a chart are solutions.** Let `e` be the extended chart at `p` and `c`
the centred chart `y ↦ e y - e p` at `p` (`SymplecticGeometry.centeredExtChartAt`). If `γ` is an
integral curve of `v` on a set `s` of times at which it lies in the source of `c`, then the
curve `t ↦ c (γ t)` is an integral curve on `s` of the coordinate field
`w ↦ mpullback 𝓘(ℝ, E) I e.symm v (e p + w)` of `v`, recentred at `p`. -/
theorem IsMIntegralCurveOn.isIntegralCurveOn_centeredExtChartAt {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ v s)
    (hmem : ∀ t ∈ s, γ t ∈ (SymplecticGeometry.centeredExtChartAt I p).source) :
    IsIntegralCurveOn (fun t ↦ SymplecticGeometry.centeredExtChartAt I p (γ t))
      (fun _ w ↦ mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v (extChartAt I p p + w)) s := by
  intro t ht
  have hγt : γ t ∈ (extChartAt I p).source :=
    (SymplecticGeometry.centeredExtChartAt_source_eq_extChartAt_source I p).subset (hmem t ht)
  have h := (hγ t ht).hasDerivWithinAt_extChartAt_comp_mpullbackWithin hγt
    |>.sub_const (extChartAt I p p)
  rw [I.range_eq_univ, mpullbackWithin_univ] at h
  have hc : (fun t ↦ SymplecticGeometry.centeredExtChartAt I p (γ t)) =
      fun t ↦ (extChartAt I p ∘ γ) t - extChartAt I p p :=
    funext fun _ ↦ SymplecticGeometry.centeredExtChartAt_apply I p _
  rw [hc]
  -- The two derivatives differ by `e p + (q - e p) = q`, inside a dependent type.
  exact h.congr_deriv (congrArg
    (fun w : E ↦ (mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v w : E)) (add_sub_cancel _ _).symm)

end General

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
  have hγ := IsIntegralCurveOn.isMIntegralCurveOn_extChartAt_symm
    (z := fun s ↦ extChartAt I p p + y s) (fun s hs ↦ (hy s hs).const_add _)
    (fun s hs ↦ hmem s hs)
  simpa using (hγ.globalFlow_sub_eq_Ici hv hcomplete ht).symm

/-- **Orbits in a chart are solutions.** Let `e` be the extended chart at `p` and `c` the
centred chart `y ↦ e y - e p` at `p` (`SymplecticGeometry.centeredExtChartAt`). On a set `s` of
times at which the orbit of `x` under the flow of a complete `C¹` field `v` lies in the source
of `c`, the curve `t ↦ c (φ_t x)` is an integral curve of the coordinate field
`w ↦ mpullback 𝓘(ℝ, E) I e.symm v (e p + w)` of `v`, recentred at `p`. -/
theorem isIntegralCurveOn_centeredExtChartAt_globalFlow {p x : M} {s : Set ℝ}
    (hmem : ∀ t ∈ s,
      globalFlow v hv hcomplete t x ∈ (SymplecticGeometry.centeredExtChartAt I p).source) :
    IsIntegralCurveOn
      (fun t ↦ SymplecticGeometry.centeredExtChartAt I p (globalFlow v hv hcomplete t x))
      (fun _ w ↦ mpullback 𝓘(ℝ, E) I (extChartAt I p).symm v (extChartAt I p p + w)) s :=
  ((isMIntegralCurve_globalFlow hv hcomplete x).isMIntegralCurveOn s)
    |>.isIntegralCurveOn_centeredExtChartAt hmem

end TauCeti

end
