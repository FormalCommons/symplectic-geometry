/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Weinstein.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Analysis.ODE.Linear
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.EnergyBarrier
import SymplecticGeometry.Geometry.Manifold.Flow.Chart
import SymplecticGeometry.Geometry.Manifold.IsManifold.ChartBall
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Chart
import SymplecticGeometry.Geometry.Manifold.VectorField.Chart
import SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization
import SymplecticGeometry.Analysis.ODE.LyapunovPerron.ParameterDerivative
import SymplecticGeometry.Analysis.ODE.LyapunovBilinForm
import SymplecticGeometry.Analysis.Calculus.FDeriv.Graph
import SymplecticGeometry.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import TauCeti.Analysis.ODE.ExponentialDichotomy
import Mathlib.Analysis.ODE.Transform
import TauCeti.Geometry.Symplectic.Liouville.Scaling
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Flow.Stable

/-!
# The flow of a Weinstein structure and its stable sets

Let `(ω, X, f)` be a Weinstein structure on a Hausdorff boundaryless manifold `M`. Its Liouville
field `X` is smooth and complete, so it generates a flow `φ` of `ℝ` on `M`. This file names that
flow and gives it the API that later files use, so that none of them unfolds it: the orbits are
integral curves of `X`, every integral curve is an orbit, each time map is smooth and a
diffeomorphism, and its differential carries `X` to itself. Since `X` is gradient-like for `f`,
the function `f` increases along every orbit; so on the stable set of a point `p`, the set of
points whose orbits tend to `p`, the function `f` is at most `f p`. Near a nondegenerate critical
point `p`, read in the chart at `p`, an orbit of the stable set that starts close to `p`, at a
value of `f` close to `f p`, never moves far from `p`. From this and the local stable graph of the
field read in that chart, the stable set of `p` near `p` is the image of a smooth disc in the
stable subspace of the linearization of `X` at `p`, along which the derivative of the flow, read
in the chart at `p`, stays bounded for all positive times.

From this the file proves that the stable sets of the nondegenerate critical points are
isotropic. The conformal scaling `φ_t^* ω = e^t ω` and `φ_t^* (ι_X ω) = e^t ι_X ω` of the flow is
Tau Ceti's `TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul` and
`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`. They are stated for `globalFlow`, and
apply to `SymplecticGeometry.IsWeinsteinStructure.flow` after a rewrite with
`SymplecticGeometry.IsWeinsteinStructure.flow_def`. With them,
`Flow.mpullback_eq_zero_of_mpullback_eq_exp_smul` shows that a map into the stable set along
which the derivative of the flow, read in the chart at `p`, stays bounded for all large times
pulls both forms back to zero. A map `γ` into the stable set of `p`, differentiable at `y`, has
such a bound: the orbit of `γ y` enters the part of the stable set covered by the local disc at
some time `T`, and by continuity so do the orbits of the points `γ z` with `z` near `y`; the left
inverse of the disc then writes the time-`T` map composed with `γ` near `y` as the disc composed
with a map differentiable at `y`, and the chain rule carries the bound of the disc over to `γ`.

## Main declarations

* `SymplecticGeometry.IsWeinsteinStructure.flow`: the flow of the Liouville field, Tau Ceti's
  `TauCeti.globalFlow`, with `SymplecticGeometry.IsWeinsteinStructure.flow_def` and
  `SymplecticGeometry.IsWeinsteinStructure.flow_apply`.
* `SymplecticGeometry.IsWeinsteinStructure.isMIntegralCurve_flow` and
  `SymplecticGeometry.IsWeinsteinStructure.flow_apply_eq_of_isMIntegralCurve`: the orbits are
  integral curves of `X`, and every integral curve of `X` is an orbit.
* `SymplecticGeometry.IsWeinsteinStructure.contMDiff_flow_uncurry`,
  `SymplecticGeometry.IsWeinsteinStructure.contMDiff_flow_apply` and
  `SymplecticGeometry.IsWeinsteinStructure.flowDiffeomorph`: the flow is smooth in time and space,
  and each time map is a diffeomorphism, with inverse the map at the opposite time.
* `SymplecticGeometry.IsWeinsteinStructure.mfderiv_flow_apply_self`: the differential of each time
  map carries `X` to `X`.
* `SymplecticGeometry.IsWeinsteinStructure.flow_apply_of_mvfderiv_eq_zero`: the critical points of
  `f` are rest points of the flow.
* `SymplecticGeometry.IsWeinsteinStructure.hasDerivAt_comp_flow` and
  `SymplecticGeometry.IsWeinsteinStructure.monotone_comp_flow`: along an orbit, `f` has
  derivative `df(X)`, which is nonnegative, so it is monotone.
* `SymplecticGeometry.IsWeinsteinStructure.apply_le_of_mem_stableSet`: `f x ≤ f p` for every `x`
  in the stable set of `p`.
* `SymplecticGeometry.IsWeinsteinStructure.apply_lt_of_mem_stableSet` and
  `SymplecticGeometry.IsWeinsteinStructure.notMem_criticalPoints_of_mem_stableSet`: a point
  `x ≠ p` of the stable set of `p` has `f x < f p` and is not a critical point.
* `SymplecticGeometry.IsWeinsteinStructure.exists_forall_flow_mem_source_and_norm_extChartAt_sub_le`
  states that at a nondegenerate critical point `p`, the orbits of the points of the stable set
  of `p` that start in a small ball of the chart at `p`, with `f` close to `f p`, stay in a
  slightly larger ball.
* `SymplecticGeometry.IsWeinsteinStructure.LocalStableDisc`: a local stable disc of `p`, a
  smooth map from the stable subspace of an operator `A` with injective differential on a ball,
  whose image there lies in the stable set of `p` and contains every point of it near `p` at
  which `f` is close to `f p`, whose orbits in positive time stay in the chart at `p`, and along
  which the derivative of the flow, read in that chart, exists and is bounded in positive time;
  it comes with the projection `P` onto the stable subspace along the unstable one, for which
  `x ↦ P (e x - e p)` is a left inverse of the disc on the chart `e` at `p`.
* `SymplecticGeometry.IsWeinsteinStructure.LocalStableDisc.Q`: the corestriction of `P` to the
  stable subspace, with `.coe_Q_apply` and the left inverse `.Q_extChartAt_ι_sub`.
* `SymplecticGeometry.IsWeinsteinStructure.exists_localStableDisc`: a nondegenerate critical
  point `p` has a local stable disc over the stable subspace of the linearization at `p`.
* `SymplecticGeometry.IsWeinsteinStructure.LocalStableDisc.contMDiffOn_Q_extChartAt_sub`,
  `.exists_norm_extChartAt_sub_le` and `.exists_forall_Q_flow_mem_ball_and_ι_eq`: the left
  inverse is smooth on the source of the chart, the chart image of the disc grows at most
  linearly near `0`, and orbits of points of the disc close to `p` stay in the disc at small
  values of the left inverse.
* `SymplecticGeometry.IsWeinsteinStructure.LocalStableDisc.exists_forall_flow_strictAntiOn`: on
  every local stable disc of a nondegenerate critical point `p`, for `H` the second derivative of
  `f` read in the chart at `p`, the value of `-H` at the left inverse strictly decreases along
  each orbit through a nonzero point of a small ball, with a negative derivative at every time
  `t ≥ 0`.
* `SymplecticGeometry.IsWeinsteinStructure.mpullback_interior_eq_zero_of_bounded` and
  `SymplecticGeometry.IsWeinsteinStructure.mpullback_eq_zero_of_bounded`: a map `γ` with `γ y`
  in the stable set of `p` pulls `ι_X ω` and `ω` back to zero at `y`, if the derivative at `y`
  of `γ` followed by the flow, read in the chart at `p`, is bounded for all large times on each
  tangent vector.
* `IsWeinsteinStructure.exists_eventually_norm_mvfderiv_le_of_range_subset_stableSet`: that bound
  holds for every map `γ` into the stable set of a nondegenerate critical point that is
  differentiable at `y`.
* `IsWeinsteinStructure.interior_apply_mfderiv_eq_zero_of_range_subset_stableSet` and
  `IsWeinsteinStructure.apply_mfderiv_mfderiv_eq_zero_of_range_subset_stableSet`: for such a
  map, `ι_X ω` and `ω` vanish at `γ y` on the image of the differential of `γ` at `y`; the
  stable sets of the nondegenerate critical points are isotropic.

## Implementation notes

The definitions and lemmas follow those of Tau Ceti's `TauCeti.IsAdaptedPseudoGradient.flow`,
which names the flow of an adapted pseudo-gradient in the same way. Tau Ceti's pseudo-gradients
decrease the function, while a Weinstein field increases it; the bound on the stable set is
therefore `TauCeti.Flow.le_of_mem_stableSet_of_antitone` applied to `-f`. A critical point is a
rest point, so by `Flow.eq_of_mem_stableSet` it lies on no stable set but its own; the orbit of
a point `x ≠ p` of the stable set of `p` thus meets no critical point, and
`TauCeti.IsGradientLike.strictMono_comp` makes the bound strict. The confinement near a
critical point is `TauCeti.IsGradientLike.exists_forall_mem_source_and_norm_extChartAt_sub_le`
(`SymplecticGeometry.Geometry.Manifold.Morse.EnergyBarrier`), applied to the orbits of the flow;
a nondegenerate critical point is isolated by Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints`.
The disc is built in the extended chart `e` at `p`. The dichotomy for the linearization `A`
(`TauCeti.IsGradientLike.exists_projection_exponential_bounds`, in
`SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization`) gives a projection `P`
onto the stable subspace, and `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_infty`,
applied to the smooth field read in `e` with a confinement radius within the chart target, gives
the graph map `g`, `C^1` on a ball and `C^m` on a smaller ball for each `m`, and the confined
forward solutions over `range P`. The disc is
`z ↦ e.symm (e p + z + g z)`. Its orbits are the solutions read back through `e`, by
`TauCeti.extChartAt_symm_add_eq_globalFlow`; the covering statement combines the confinement of
the stable set with the description of the confined solutions as the graph, and the differential
is injective since `P ∘ g = 0`, by
`ContinuousLinearMap.injective_fderiv_add_comp_subtype`.
The disc is smooth on the whole ball although `g` is known to be `C^m` only near `0`: the orbit
of a point `ι z` of the disc enters, at some time `T`, the region where `g` is `C^m`, and the
confined solutions there lie on the graph, so that `ι = φ_{-T} ∘ ι ∘ h` near `z`, with
`h w = P (e (φ_T (ι w)) - e p)`. The map `h` is differentiable at `z` and has the `C^m` left
inverse `u ↦ P (e (φ_{-T} (ι u)) - e p)`, so it is `C^m` at `z` by
`ContDiffAt.of_local_left_inverse_of_finrank_eq`, and then so is `ι`.
The covering step, which first confines the orbits of the stable set near `p` and then identifies
them with the local stable graph, follows the plan of Tau Ceti's
`TauCeti.IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_stableSet`
(`TauCeti.Analysis.Calculus.Morse.GlobalChart`), for negative gradient flows on a vector space.

Along an orbit of the disc, with `w t = e (φ_t (ι z)) - e p` and `ζ t = Q (w t)`, the derivative
of `-H (ζ t) (ζ t)` is `-2 * H (P w) (P (Y w))`, where `Y` is the field read in `e` and recentred
at `p` (`ContinuousLinearMap.hasDerivAt_neg_apply_self_comp`). The linear bound on the disc puts
`w t` in a cone `‖w‖ ≤ C * ‖P w‖`, on which
`ContinuousLinearMap.exists_forall_half_mul_norm_sq_le_apply`, applied with the bound
`c * ‖v‖ ^ 2 ≤ H v (A v)` of
`TauCeti.IsGradientLike.exists_pos_mul_norm_sq_le_fderiv_fderiv`, makes the derivative at most
`-c * ‖ζ t‖ ^ 2`; the forward invariance of small discs keeps the orbit in that region.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11; this file proves Proposition 11.9 (a), the isotropy of the stable manifolds
* C. Chicone, *Ordinary Differential Equations with Applications*, second edition,
  Springer, 2006, §4.3, for the local stable manifold of a hyperbolic rest point
-/

public section

open Filter Function Metric Set TauCeti
open scoped Manifold Topology

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) (⊤ : ℕ∞) M]
  [T2Space M]
  {ω : SmoothTwoForm 𝓘(ℝ, E) M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}

namespace IsWeinsteinStructure

/-- The **flow of a Weinstein structure** `(ω, X, f)`: the flow of its complete smooth Liouville
field `X`, whose value at time `t` and point `y` is the value at `t` of the integral curve of `X`
through `y`. -/
noncomputable def flow (hW : IsWeinsteinStructure ω X f) : Flow ℝ M :=
  globalFlow X (hW.contMDiff_field.of_le (by simp)) hW.isCompleteVectorField

variable (hW : IsWeinsteinStructure ω X f)

/-- The flow of a Weinstein structure is Tau Ceti's global flow of its Liouville field. -/
theorem flow_def :
    hW.flow = globalFlow X (hW.contMDiff_field.of_le (by simp)) hW.isCompleteVectorField :=
  (rfl)

/-- The flow of a Weinstein structure is the maximal flow `flowOf X` of its Liouville field. -/
theorem flowOf_eq_flow : flowOf X = ⇑hW.flow :=
  (flowOf_eq_globalFlow _ _).trans (congrArg _ hW.flow_def.symm)

/-- The flow at time `t` is the maximal integral curve of the Liouville field at time `t`. -/
theorem flow_apply (t : ℝ) (y : M) : hW.flow t y = maximalIntegralCurve X y t := by
  rw [flow_def, globalFlow_apply]

/-- The orbits of the flow are integral curves of the Liouville field. -/
theorem isMIntegralCurve_flow (y : M) : IsMIntegralCurve (fun t ↦ hW.flow t y) X :=
  isMIntegralCurve_globalFlow _ hW.isCompleteVectorField y

/-- **Integral curves are orbits.** Every integral curve of the Liouville field is the orbit of
its value at time `0`. -/
theorem flow_apply_eq_of_isMIntegralCurve {γ : ℝ → M} (hγ : IsMIntegralCurve γ X) (t : ℝ) :
    hW.flow t (γ 0) = γ t :=
  globalFlow_eq_of_isMIntegralCurve _ hW.isCompleteVectorField hγ t

/-- The flow of a Weinstein structure is smooth in time and space. -/
theorem contMDiff_flow_uncurry :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) (⊤ : ℕ∞) fun p : ℝ × M ↦ hW.flow p.1 p.2 :=
  contMDiff_globalFlow_uncurry hW.isCompleteVectorField (n := ⊤) le_top hW.contMDiff_field

/-- For a fixed time `t`, the time-`t` map of the flow is smooth. -/
theorem contMDiff_flow_apply (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞) (hW.flow t) :=
  contMDiff_globalFlow_apply hW.isCompleteVectorField (n := ⊤) le_top hW.contMDiff_field t

/-- The time-`t` map of the flow of a Weinstein structure, as a diffeomorphism. Its inverse is
the time-`(-t)` map. -/
noncomputable def flowDiffeomorph (t : ℝ) : M ≃ₘ^(⊤ : ℕ∞)⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  globalFlowDiffeomorph hW.isCompleteVectorField (n := ⊤) le_top hW.contMDiff_field t

/-- The diffeomorphism `flowDiffeomorph t` is Tau Ceti's global flow diffeomorphism at time `t`. -/
theorem flowDiffeomorph_def (t : ℝ) :
    hW.flowDiffeomorph t =
      globalFlowDiffeomorph hW.isCompleteVectorField (n := ⊤) le_top hW.contMDiff_field t :=
  (rfl)

/-- The diffeomorphism `flowDiffeomorph t` is the time-`t` map of the flow. -/
@[simp]
theorem flowDiffeomorph_apply (t : ℝ) (y : M) : hW.flowDiffeomorph t y = hW.flow t y := by
  rw [flowDiffeomorph_def, globalFlowDiffeomorph_apply, hW.flow_apply, globalFlow_apply]

/-- The inverse of `flowDiffeomorph t` is the time-`(-t)` map of the flow. -/
@[simp]
theorem flowDiffeomorph_symm_apply (t : ℝ) (y : M) :
    (hW.flowDiffeomorph t).symm y = hW.flow (-t) y := by
  rw [flowDiffeomorph_def, globalFlowDiffeomorph_symm_apply, hW.flow_apply, globalFlow_apply]

/-- **The flow preserves the Liouville field.** The differential of the time-`t` map of the flow
carries `X y` to `X` at the image of `y`. -/
theorem mfderiv_flow_apply_self (t : ℝ) (y : M) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hW.flow t) y (X y) = X (hW.flow t y) :=
  mfderiv_globalFlow_apply_self _ hW.isCompleteVectorField t y

/-- The critical points of `f` are rest points of the flow, since the gradient-like field `X`
vanishes there. -/
theorem flow_apply_of_mvfderiv_eq_zero {x : M} (hx : mvfderiv 𝓘(ℝ, E) f x = 0) (t : ℝ) :
    hW.flow t x = x :=
  (forall_globalFlow_eq_self_iff _ hW.isCompleteVectorField x).2
    (hW.isGradientLike.eq_zero_iff.2 hx) t

/-- The derivative of `f` along an orbit of the flow is `df(X)`. -/
theorem hasDerivAt_comp_flow (y : M) (t : ℝ) :
    HasDerivAt (fun s ↦ f (hW.flow s y)) (mvfderiv 𝓘(ℝ, E) f (hW.flow t y) (X (hW.flow t y))) t :=
  Manifold.hasDerivAt_comp_curve (γ := fun s ↦ hW.flow s y)
    (hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp) _) (hW.isMIntegralCurve_flow y t)

/-- The function of a Weinstein structure is monotone along every orbit of its flow. -/
theorem monotone_comp_flow (y : M) : Monotone fun t ↦ f (hW.flow t y) :=
  hW.isGradientLike.monotone_comp (hW.isMIntegralCurve_flow y)
    fun _ ↦ hW.isGeneralizedMorse.contMDiff.mdifferentiable (by simp) _

/-- **The function is bounded on a stable set by its value at the limit.** If the orbit of `x`
under the flow of a Weinstein structure `(ω, X, f)` tends to `p`, then `f x ≤ f p`. -/
theorem apply_le_of_mem_stableSet {p x : M} (hx : x ∈ hW.flow.stableSet p) : f x ≤ f p := by
  have hanti : Antitone fun t ↦ (-f) (hW.flow t x) := fun a b hab ↦ by
    simpa using hW.monotone_comp_flow x hab
  simpa using Flow.le_of_mem_stableSet_of_antitone hx
    (hW.isGeneralizedMorse.contMDiff.continuous.neg.continuousAt) hanti

/-- **No other critical point on a stable set.** A point `x ≠ p` of the stable set
of `p` under the flow of a Weinstein structure `(ω, X, f)` is not a critical point of `f`. -/
theorem notMem_criticalPoints_of_mem_stableSet {p x : M} (hx : x ∈ hW.flow.stableSet p)
    (hxp : x ≠ p) : x ∉ criticalPoints 𝓘(ℝ, E) f := fun h ↦
  hxp (Flow.eq_of_mem_stableSet (hW.flow_apply_of_mvfderiv_eq_zero (mem_criticalPoints.1 h)) hx)

/-- **The function is strictly below its limit on a stable set.** If the orbit of `x ≠ p` under
the flow of a Weinstein structure `(ω, X, f)` tends to `p`, then `f x < f p`. -/
theorem apply_lt_of_mem_stableSet {p x : M} (hx : x ∈ hW.flow.stableSet p) (hxp : x ≠ p) :
    f x < f p := by
  -- The orbit of `x` never reaches the rest point `p`, so it meets no critical point.
  have hcrit (t : ℝ) : mvfderiv 𝓘(ℝ, E) f (hW.flow t x) ≠ 0 := fun h ↦ by
    refine hW.notMem_criticalPoints_of_mem_stableSet ((Flow.apply_mem_stableSet_iff _ t).2 hx)
      (fun hpt ↦ hxp ?_) (mem_criticalPoints.2 h)
    have hfix := Flow.fixed_of_mem_stableSet hx (-t)
    rw [← hpt, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at hfix
    exact hfix.trans hpt
  calc f x = f (hW.flow 0 x) := by rw [Flow.map_zero_apply]
    _ < f (hW.flow 1 x) :=
      hW.isGradientLike.strictMono_comp (hW.isMIntegralCurve_flow x) hcrit one_pos
    _ ≤ f p := hW.apply_le_of_mem_stableSet ((Flow.apply_mem_stableSet_iff _ 1).2 hx)

/-- **Confinement of the stable set in the chart at a critical point.** Let `p` be a
nondegenerate critical point of the function of a Weinstein structure, and `e` the extended chart
at `p`. There is `r₀ > 0` with the closed ball of radius `r₀` about `e p` in the chart target,
such that for every `r ∈ (0, r₀]` there is `ε > 0` with the following property: the orbit of a
point `x` of the stable set of `p`, with `x` in the chart within `r / 2` of `e p` and
`f p - ε < f x`, lies in the chart within `r` of `e p` at every time `t ≥ 0`. -/
theorem exists_forall_flow_mem_source_and_norm_extChartAt_sub_le {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) :
    ∃ r₀ > 0, closedBall (extChartAt 𝓘(ℝ, E) p p) r₀ ⊆ (extChartAt 𝓘(ℝ, E) p).target ∧
      ∀ r ∈ Ioc 0 r₀, ∃ ε > 0, ∀ x ∈ hW.flow.stableSet p, x ∈ (extChartAt 𝓘(ℝ, E) p).source →
        ‖extChartAt 𝓘(ℝ, E) p x - extChartAt 𝓘(ℝ, E) p p‖ ≤ r / 2 → f p - ε < f x →
        ∀ t, 0 ≤ t → hW.flow t x ∈ (extChartAt 𝓘(ℝ, E) p).source ∧
          ‖extChartAt 𝓘(ℝ, E) p (hW.flow t x) - extChartAt 𝓘(ℝ, E) p p‖ ≤ r := by
  obtain ⟨r₀, hr₀, hsub, h⟩ :=
    hW.isGradientLike.exists_forall_mem_source_and_norm_extChartAt_sub_le
      (hW.isGeneralizedMorse.contMDiff.of_le (by simp)) hW.contMDiff_field.continuous
      (hp.eventually_notMem_criticalPoints.mono fun _ hy ↦ by rwa [mem_criticalPoints] at hy)
  refine ⟨r₀, hr₀, hsub, fun r hr ↦ ?_⟩
  obtain ⟨ε, hε, hconf⟩ := h r hr
  have h₀ (x : M) : hW.flow 0 x = x := hW.flow.map_zero_apply x
  exact ⟨ε, hε, fun x hx hxs hxr hfx t ht ↦ hconf (fun s ↦ hW.flow s x)
    (hW.isMIntegralCurve_flow x) (Flow.mem_stableSet.1 hx) (by rwa [h₀]) (by rwa [h₀])
    (by rwa [h₀]) t ht⟩

/-- A **local stable disc** of a point `p` for the flow `φ` of a Weinstein structure `(ω, X, f)`,
over the stable subspace `S` of an operator `A` on `E`, read in the extended chart `e` at `p`.
It is a map `ι : S → M` with `ι 0 = p` and a radius `ρ > 0` such that:
* on the ball of radius `ρ`, `ι` is smooth and its differential is injective;
* `ι` maps that ball into the stable set of `p`;
* the image of that ball contains every point of the stable set of `p` that lies in some
  neighbourhood `U` of `p` and at which `f` exceeds `f p - ε`, for some `ε > 0`;
* at each point `z` of that ball and each `t ≥ 0`, the point `φ_t (ι z)` lies in the source of
  `e`, the map `w ↦ e (φ_t (ι w))` is differentiable at `z`, and its derivative there is bounded
  independently of `t`;

together with an idempotent `P : E →L[ℝ] E` commuting with `A`, with range `S` and kernel the
unstable subspace of `A`, such that `x ↦ P (e x - e p)` is a left inverse of `ι` on the ball of
radius `ρ`. The corestriction `Q : E →L[ℝ] S` of `P` is `IsWeinsteinStructure.LocalStableDisc.Q`.

`IsWeinsteinStructure.exists_localStableDisc` gives one at every nondegenerate critical point
`p`, for `A` the linearization of the Liouville field at `p`. -/
@[ext]
structure LocalStableDisc (hW : IsWeinsteinStructure ω X f) (p : M) (A : E →L[ℝ] E) where
  /-- The disc, a map from the stable subspace of `A` to `M`. -/
  ι : A.stableSubspace → M
  /-- The radius of the ball of the stable subspace on which the disc has its properties. -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  ι_zero : ι 0 = p
  contMDiffAt_ι : ∀ z ∈ ball (0 : A.stableSubspace) ρ,
    ContMDiffAt 𝓘(ℝ, A.stableSubspace) 𝓘(ℝ, E) (⊤ : ℕ∞) ι z
  injective_mfderiv_ι : ∀ z ∈ ball (0 : A.stableSubspace) ρ,
    Injective (mfderiv 𝓘(ℝ, A.stableSubspace) 𝓘(ℝ, E) ι z)
  image_ball_subset_stableSet : ι '' ball 0 ρ ⊆ hW.flow.stableSet p
  exists_stableSet_inter_subset_image_ball :
    ∃ U ∈ 𝓝 p, ∃ ε > 0, hW.flow.stableSet p ∩ U ∩ {x | f p - ε < f x} ⊆ ι '' ball 0 ρ
  exists_forall_flow_mem_source_and_norm_fderiv_le : ∀ z ∈ ball (0 : A.stableSubspace) ρ,
    ∃ C : ℝ, ∀ t, 0 ≤ t →
      hW.flow t (ι z) ∈ (extChartAt 𝓘(ℝ, E) p).source ∧
        DifferentiableAt ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (ι w))) z ∧
        ‖fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (ι w))) z‖ ≤ C
  /-- The projection onto the stable subspace of `A` along its unstable subspace. -/
  P : E →L[ℝ] E
  isIdempotentElem_P : IsIdempotentElem P
  commute_P : Commute A P
  range_P : (P : E →ₗ[ℝ] E).range = A.stableSubspace
  ker_P : (P : E →ₗ[ℝ] E).ker = A.unstableSubspace
  P_extChartAt_ι_sub : ∀ z ∈ ball (0 : A.stableSubspace) ρ,
    P (extChartAt 𝓘(ℝ, E) p (ι z) - extChartAt 𝓘(ℝ, E) p p) = z

attribute [simp] LocalStableDisc.ι_zero

/-- **The local stable disc of a nondegenerate critical point.** Let `p` be a nondegenerate
critical point of the function of a Weinstein structure, and `A` the linearization of the
Liouville field at `p`. Then `p` has a local stable disc over the stable subspace of `A`
(`IsWeinsteinStructure.LocalStableDisc`). -/
theorem exists_localStableDisc {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    Nonempty (hW.LocalStableDisc p A) := by
  have hXp := hW.mdifferentiableAt_field p
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 (mem_criticalPoints.1 hp.mem_criticalPoints)
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) :=
    hW.contMDiff_field.of_le (by simp)
  -- The dichotomy of the linearization, and the confinement radius `r₀`.
  obtain ⟨P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    hW.isGradientLike.exists_projection_exponential_bounds hp hXp hA
  have hPS : (P : E →ₗ[ℝ] E).range = A.stableSubspace :=
    ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds hα hP hAP hs hu
  have hPU : (P : E →ₗ[ℝ] E).ker = A.unstableSubspace := by
    rw [LinearMap.IsIdempotentElem.ker_eq_range
        (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP),
      ← ContinuousLinearMap.range_id_sub_eq_unstableSubspace_of_exponential_bounds hα hP hAP hs hu,
      ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.coe_id]
  obtain ⟨r₀, hr₀, hr₀t, hconf⟩ := hW.exists_forall_flow_mem_source_and_norm_extChartAt_sub_le hp
  -- The local stable graph of the coordinate field, with confinement radius at most `r₀`; the
  -- graph map is `C^1` on the ball of radius `ρ`, and `C^m` on a smaller ball for every `m`.
  obtain ⟨r, hr, hrr₀, ρ, hρ, g, -, -, hg0, -, hg1, hgn, hPg, -, hset, htend, y, hy⟩ :=
    ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_infty hs hu hα hP hAP
      (hW.contMDiff_field p).contDiffAt_mpullback_extChartAt_symm
      ((VectorField.mpullback_extChartAt_symm_self X p).trans hp0)
      (hA ▸ hXp.hasFDerivAt_mpullback_extChartAt_symm) hr₀
  set e := extChartAt 𝓘(ℝ, E) p with he
  set S := A.stableSubspace
  have hPz (z : S) : P z = z :=
    (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hP)).1 (hPS.ge z.property)
  have hball (z : S) (hz : z ∈ ball (0 : S) ρ) : (z : E) ∈ Set.range P ∩ closedBall 0 ρ :=
    ⟨⟨z, hPz z⟩, by simpa using (mem_ball_zero_iff.1 hz).le⟩
  set ι : S → M := fun z ↦ e.symm (e p + ((z : E) + g z)) with hι
  -- On the ball, the orbits of the disc are the confined solutions `y z` read in the chart.
  have horb (z : S) (hz : z ∈ ball (0 : S) ρ) (t : ℝ) (ht : 0 ≤ t) :
      e p + y z t ∈ e.target ∧ hW.flow t (ι z) = e.symm (e p + y z t) := by
    obtain ⟨hyi, hymaps, hy0, -⟩ := hy z (hball z hz)
    have htarget (s : ℝ) (hs : 0 ≤ s) : e p + y z s ∈ e.target :=
      hr₀t (closedBall_subset_closedBall hrr₀
        (by simpa [mem_closedBall, dist_eq_norm] using hymaps (mem_Ici.2 hs)))
    refine ⟨htarget t ht, ?_⟩
    have h := TauCeti.extChartAt_symm_add_eq_globalFlow hv hW.isCompleteVectorField hyi htarget ht
    rw [hy0, ← hW.flow_def] at h
    exact h.symm
  have hq (z : S) (hz : z ∈ ball (0 : S) ρ) : e p + ((z : E) + g z) ∈ e.target := by
    obtain ⟨-, -, hy0, -⟩ := hy z (hball z hz)
    simpa [hy0] using (horb z hz 0 le_rfl).1
  -- Where `g` is `C^m`, so is `ι`.
  have hF (m : ℕ) (z : S) (hgz : ContDiffAt ℝ m g z) :
      ContDiffAt ℝ m (fun w : S ↦ e p + ((w : E) + g w)) z :=
    contDiffAt_const.add (S.subtypeL.contDiff.contDiffAt.add
      (hgz.comp (f := S.subtypeL) z S.subtypeL.contDiff.contDiffAt))
  have hιC (m : ℕ) (z : S) (hz : z ∈ ball (0 : S) ρ) (hgz : ContDiffAt ℝ m g z) :
      ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) m ι z := by
    have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) m e.symm (e p + ((z : E) + g z)) :=
      ((contMDiffOn_extChartAt_symm (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) p).of_le
        (by exact_mod_cast le_top)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (hq z hz))
    exact hsymm.comp z (hF m z hgz).contMDiffAt
  -- A confined forward solution that starts over the ball starts on the graph of `g`.
  have hgraph (c : ℝ → E) (hc : IsIntegralCurveOn c
      (fun _ w ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X (e p + w)) (Ici 0))
      (hcr : MapsTo c (Ici 0) (closedBall 0 r)) (hcP : ‖P (c 0)‖ ≤ ρ) :
      c 0 = P (c 0) + g (P (c 0)) := by
    have hmem : c 0 ∈ {u : E | (∃ c : ℝ → E, IsIntegralCurveOn c
        (fun _ w ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X (e p + w)) (Ici 0) ∧
          c 0 = u ∧ MapsTo c (Ici 0) (closedBall 0 r)) ∧ ‖P u‖ ≤ ρ} :=
      ⟨⟨c, hc, rfl, hcr⟩, hcP⟩
    rw [hset] at hmem
    obtain ⟨u, ⟨⟨v, hv⟩, -⟩, hu⟩ := hmem
    simp only at hu
    have hPu : P (c 0) = u := by
      rw [← hu, map_add, hPg, add_zero, ← hv, ← mul_apply_eq_comp, hP.eq]
    rw [hPu, hu]
  have hinv (T : ℝ) (x : M) : hW.flow (-T) (hW.flow T x) = x := by simp
  have hQ (x : E) : P x ∈ S := hPS ▸ LinearMap.mem_range_self (P : E →ₗ[ℝ] E) x
  set Q : E →L[ℝ] S := P.codRestrict S hQ
  have hQP (x : E) : (Q x : E) = P x := ContinuousLinearMap.coe_codRestrict_apply _ _ _ x
  -- The map `x ↦ Q (e x - e p)` is a left inverse of `ι` on the ball.
  have hQι (z : S) (hz : z ∈ ball (0 : S) ρ) : Q (e (ι z) - e p) = z := by
    ext
    simp [hQP, hι, e.right_inv (hq z hz), hPg, hPz]
  -- Smoothness spreads from a small ball to the ball of radius `ρ` along the flow: for `T`
  -- large, `ι = φ_{-T} ∘ ι ∘ h` near `z`, with `h` landing where `g` is `C^m`, and `h` has the
  -- `C^m` left inverse `u ↦ Q (e (φ_{-T} (ι u)) - e p)`.
  have hsmooth (m : ℕ) (hm : m ≠ 0) (z : S) (hz : z ∈ ball (0 : S) ρ) :
      ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) m ι z := by
    have hm0 : (m : WithTop ℕ∞) ≠ 0 := by exact_mod_cast hm
    obtain ⟨ρm, hρm, hgm⟩ := hgn m
    obtain ⟨hyi, hymaps, -, hyd, -⟩ := hy z (hball z hz)
    have hlim : Tendsto (fun t ↦ ‖P (y z t)‖) atTop (𝓝 0) := by
      simpa using ((P.continuous.tendsto 0).comp (htend _ hyi hymaps)).norm
    obtain ⟨T, hT0, hTz⟩ :=
      ((eventually_ge_atTop 0).and (hlim.eventually (gt_mem_nhds (lt_min hρ hρm)))).exists
    set h : S → S := fun w ↦ Q (y w T) with hh
    have hhd : DifferentiableAt ℝ h z :=
      Q.differentiableAt.comp z ((hyd T hT0).comp (f := S.subtypeL) z S.subtypeL.differentiableAt)
    have hnorm (w : S) : ‖h w‖ = ‖P (y w T)‖ := by
      rw [← Submodule.norm_coe, hQP]
    have hev : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : S) ρ ∧ ‖h w‖ < min ρ ρm :=
      (isOpen_ball.eventually_mem hz).and
        ((continuous_norm.continuousAt.comp hhd.continuousAt).eventually
          (gt_mem_nhds (by rwa [Function.comp_apply, hnorm])))
    -- Along the flow, `φ_T ∘ ι = ι ∘ h` near `z`.
    have hιh : ∀ᶠ w in 𝓝 z, ι (h w) = hW.flow T (ι w) := hev.mono fun w ⟨hw, hhw⟩ ↦ by
      rw [hnorm] at hhw
      obtain ⟨hwi, hwmaps, -⟩ := hy w (hball w hw)
      have hgw := hgraph (fun s ↦ y w (s + T))
        ((hwi.comp_add T).mono fun s hs ↦ by
          rw [mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add, mem_Ici]
          exact add_nonneg hT0 hs)
        (fun s hs ↦ hwmaps (mem_Ici.2 (add_nonneg hs hT0)))
        (by simpa using hhw.le.trans (min_le_left _ _))
      simp only [zero_add] at hgw
      rw [(horb w hw T hT0).2, hgw]
      simp only [hι, hh, hQP]
    obtain ⟨-, hhz⟩ := hev.self_of_nhds
    have hhzρ : h z ∈ ball (0 : S) ρ := mem_ball_zero_iff.2 (hhz.trans_le (min_le_left _ _))
    have hgh : ContDiffAt ℝ m g (h z) :=
      hgm _ (by simpa [Submodule.norm_coe] using hhz.le.trans (min_le_right _ _))
    have hιhz : ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) m ι (h z) := hιC m (h z) hhzρ hgh
    have hback : hW.flow (-T) (ι (h z)) = ι z := by rw [hιh.self_of_nhds, hinv]
    -- The left inverse of `h`.
    have hk : ContDiffAt ℝ m (fun u ↦ Q (e (hW.flow (-T) (ι u)) - e p)) (h z) := by
      have hsrc : ι z ∈ (chartAt E p).source := by
        rw [← extChartAt_source 𝓘(ℝ, E)]
        exact e.map_target (hq z hz)
      have h1 : ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) m (fun u ↦ e (hW.flow (-T) (ι u))) (h z) :=
        ((contMDiffAt_extChartAt' (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) hsrc).of_le
          (by exact_mod_cast le_top)).comp_of_eq
          ((((hW.contMDiff_flow_apply (-T)).of_le (by exact_mod_cast le_top)).contMDiffAt).comp
            (h z) hιhz) hback
      exact Q.contDiff.contDiffAt.comp _ ((contMDiffAt_iff_contDiffAt.1 h1).sub contDiffAt_const)
    have hkh : ∀ᶠ w in 𝓝 z, Q (e (hW.flow (-T) (ι (h w))) - e p) = w :=
      (hιh.and hev).mono fun w ⟨hw, hw', _⟩ ↦ by rw [hw, hinv, hQι w hw']
    have hhC : ContDiffAt ℝ m h z :=
      ContDiffAt.of_local_left_inverse_of_finrank_eq hk hhd hkh hm0 rfl
    have hcomp : ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) m (fun w ↦ hW.flow (-T) (ι (h w))) z :=
      (((hW.contMDiff_flow_apply (-T)).of_le (by exact_mod_cast le_top)).contMDiffAt).comp z
        (hιhz.comp z hhC.contMDiffAt)
    exact hcomp.congr_of_eventuallyEq (hιh.mono fun w hw ↦ by beta_reduce; rw [hw, hinv])
  -- Smoothness and injectivity of the differential.
  have hιz (z : S) (hz : z ∈ ball (0 : S) ρ) :
      ContMDiffAt 𝓘(ℝ, S) 𝓘(ℝ, E) (⊤ : ℕ∞) ι z ∧ Injective (mfderiv 𝓘(ℝ, S) 𝓘(ℝ, E) ι z) := by
    have hgz : ContDiffAt ℝ 1 g z := by exact_mod_cast hg1 _ (hball z hz).2
    have hinj : Injective (fderiv ℝ (fun w : S ↦ e p + ((w : E) + g w)) z) := by
      rw [fderiv_const_add]
      exact P.injective_fderiv_add_comp_subtype (fun w hw ↦ hPz ⟨w, hw⟩) hPg
        (hgz.differentiableAt one_ne_zero)
    refine ⟨contMDiffAt_infty.2 fun m ↦ ?_,
      injective_mfderiv_extChartAt_symm_comp (hq z hz)
        ((hF 1 z hgz).differentiableAt one_ne_zero) hinj⟩
    exact (hsmooth (m + 1) m.succ_ne_zero z hz).of_le (by exact_mod_cast m.le_succ)
  -- The image lies in the stable set.
  have hst : ι '' ball 0 ρ ⊆ hW.flow.stableSet p := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hyi, hymaps, -⟩ := hy z (hball z hz)
    refine Flow.mem_stableSet.2 (Tendsto.congr' (f₁ := fun t ↦ e.symm (e p + y z t)) ?_ ?_)
    · filter_upwards [eventually_ge_atTop 0] with t ht using (horb z hz t ht).2.symm
    · have h1 : Tendsto (fun t ↦ e p + y z t) atTop (𝓝 (e p)) := by
        simpa using (htend _ hyi hymaps).const_add (e p)
      have h := (continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p).tendsto.comp h1
      simpa [he, Function.comp_def] using h
  -- The image covers the stable set near `p`, at values of `f` close to `f p`.
  have hcov : ∃ U ∈ 𝓝 p, ∃ ε > 0,
      hW.flow.stableSet p ∩ U ∩ {x | f p - ε < f x} ⊆ ι '' ball 0 ρ := by
    obtain ⟨ε, hε, hc⟩ := hconf r ⟨hr, hrr₀⟩
    set δ := min (r / 2) (ρ / (‖P‖ + 1))
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    refine ⟨chartBall 𝓘(ℝ, E) p δ, chartBall_mem_nhds _ p hδ, ε, hε, ?_⟩
    rintro x ⟨⟨hx, hxc⟩, hfx⟩
    obtain ⟨hxs, hxb⟩ := (mem_chartBall_iff _).1 hxc
    rw [mem_ball, dist_eq_norm] at hxb
    have hcx := hc x hx hxs (hxb.le.trans (min_le_left _ _)) hfx
    set Y : ℝ → E := fun t ↦ e (hW.flow t x) - e p
    have hYi : IsIntegralCurveOn Y
        (fun _ w ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X (e p + w))
        (Ici 0) := by
      have h := TauCeti.isIntegralCurveOn_extChartAt_globalFlow_sub hv hW.isCompleteVectorField
        (s := Ici 0) (p := p) (x := x) fun t ht ↦ by rw [← hW.flow_def]; exact (hcx t ht).1
      rwa [← hW.flow_def] at h
    have hY0 : Y 0 = e x - e p := by simp [Y]
    have hPY : ‖P (Y 0)‖ < ρ := by
      have h1 : ‖P‖ * (ρ / (‖P‖ + 1)) < ρ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg P]
      calc ‖P (Y 0)‖ ≤ ‖P‖ * ‖Y 0‖ := P.le_opNorm _
        _ ≤ ‖P‖ * (ρ / (‖P‖ + 1)) := by
          rw [hY0]
          exact mul_le_mul_of_nonneg_left (hxb.le.trans (min_le_right _ _)) (norm_nonneg _)
        _ < ρ := h1
    have hw := hgraph Y hYi (fun t ht ↦ by simpa [Y] using (hcx t ht).2) hPY.le
    refine ⟨Q (Y 0), by simpa [hQP] using hPY, ?_⟩
    simp only [hι, hQP]
    rw [← hw, hY0, add_sub_cancel, e.left_inv hxs]
  -- The derivative of `w ↦ e (φ_t (ι w))` is bounded in `t ≥ 0`.
  have hbd (z : S) (hz : z ∈ ball (0 : S) ρ) : ∃ C : ℝ, ∀ t, 0 ≤ t →
      hW.flow t (ι z) ∈ e.source ∧ DifferentiableAt ℝ (fun w ↦ e (hW.flow t (ι w))) z ∧
        ‖fderiv ℝ (fun w ↦ e (hW.flow t (ι w))) z‖ ≤ C := by
    obtain ⟨-, -, -, hyd, C, hC⟩ := hy z (hball z hz)
    refine ⟨C, fun t ht ↦ ?_⟩
    have heq : (fun w ↦ e (hW.flow t (ι w))) =ᶠ[𝓝 z] fun w ↦ e p + y w t := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      rw [(horb w hw t ht).2, e.right_inv (horb w hw t ht).1]
    have hD : HasFDerivAt (fun w : S ↦ e p + y w t)
        ((fderiv ℝ (fun v ↦ y v t) z).comp S.subtypeL) z :=
      ((hyd t ht).hasFDerivAt.comp (f := S.subtypeL) z S.subtypeL.hasFDerivAt).const_add _
    refine ⟨(horb z hz t ht).2 ▸ e.map_target (horb z hz t ht).1,
      (hD.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    rw [heq.fderiv_eq, hD.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (Submodule.norm_subtypeL_le S)).trans (hC t ht))
  exact ⟨{
    ι := ι
    ρ := ρ
    ρ_pos := hρ
    ι_zero := by simpa [hι, hg0] using e.left_inv (mem_extChartAt_source p)
    contMDiffAt_ι := fun z hz ↦ (hιz z hz).1
    injective_mfderiv_ι := fun z hz ↦ (hιz z hz).2
    image_ball_subset_stableSet := hst
    exists_stableSet_inter_subset_image_ball := hcov
    exists_forall_flow_mem_source_and_norm_fderiv_le := hbd
    P := P
    isIdempotentElem_P := hP
    commute_P := hAP
    range_P := hPS
    ker_P := hPU
    P_extChartAt_ι_sub := fun z hz ↦ by rw [← hQP, hQι z hz] }⟩

namespace LocalStableDisc

variable {hW} {p : M} {A : E →L[ℝ] E} (D : hW.LocalStableDisc p A)

/-- The corestriction `Q : E →L[ℝ] S` of the projection `P` of a local stable disc to its range,
the stable subspace `S` of `A`. -/
noncomputable def Q : E →L[ℝ] A.stableSubspace :=
  D.P.codRestrict A.stableSubspace fun x ↦ D.range_P ▸ LinearMap.mem_range_self _ x

theorem Q_def :
    D.Q = D.P.codRestrict A.stableSubspace fun x ↦ D.range_P ▸ LinearMap.mem_range_self _ x :=
  (rfl)

@[simp]
theorem coe_Q_apply (v : E) : (D.Q v : E) = D.P v := by
  rw [Q_def, ContinuousLinearMap.coe_codRestrict_apply]

/-- The map `x ↦ Q (e x - e p)`, for `e` the extended chart at `p`, is a left inverse of a local
stable disc on the ball of radius `ρ`. -/
theorem Q_extChartAt_ι_sub {z : A.stableSubspace} (hz : z ∈ ball 0 D.ρ) :
    D.Q (extChartAt 𝓘(ℝ, E) p (D.ι z) - extChartAt 𝓘(ℝ, E) p p) = z :=
  Subtype.ext <| by rw [coe_Q_apply, D.P_extChartAt_ι_sub z hz]

/-- The left inverse `x ↦ Q (e x - e p)` of a local stable disc, for `e` the extended chart at
`p`, is smooth on the source of `e`. -/
theorem contMDiffOn_Q_extChartAt_sub :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, A.stableSubspace) (⊤ : ℕ∞)
      (fun x ↦ D.Q (extChartAt 𝓘(ℝ, E) p x - extChartAt 𝓘(ℝ, E) p p))
      (extChartAt 𝓘(ℝ, E) p).source := by
  have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : ℕ∞)
      (fun x ↦ extChartAt 𝓘(ℝ, E) p x - extChartAt 𝓘(ℝ, E) p p) (extChartAt 𝓘(ℝ, E) p).source := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt.sub contMDiffOn_const
  exact D.Q.contDiff.contMDiff.comp_contMDiffOn h

/-- **A first-order bound at the centre.** Read in the extended chart `e` at `p`, a local stable
disc `ι` of `p` satisfies `‖e (ι z) - e p‖ ≤ C * ‖z‖` near `0`, for some constant `C`. -/
theorem exists_norm_extChartAt_sub_le :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : A.stableSubspace) δ,
      ‖extChartAt 𝓘(ℝ, E) p (D.ι z) - extChartAt 𝓘(ℝ, E) p p‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC⟩ := D.exists_forall_flow_mem_source_and_norm_fderiv_le 0 (mem_ball_self D.ρ_pos)
  have hd : DifferentiableAt ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) p (D.ι w)) 0 := by
    simpa using (hC 0 le_rfl).2.1
  obtain ⟨C, hC⟩ := hd.hasFDerivAt.isBigO_sub.bound
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.1 hC
  exact ⟨C, δ, hδ, fun z hz ↦ by simpa using h z hz⟩

/-- **Forward invariance of a local stable disc near `p`.** Let `ι` be a local stable disc of a
nondegenerate critical point `p`, with radius `ρ` and left inverse `π x = Q (e x - e p)`, for `e`
the extended chart at `p`, and `φ` the flow. For every `ρ₁ > 0` there is `ρ₂ ∈ (0, min ρ ρ₁]`
such that for `z` in the ball of radius `ρ₂` and `t ≥ 0`, the point `π (φ_t (ι z))` lies in the
ball of radius `ρ₁` and `ι (π (φ_t (ι z))) = φ_t (ι z)`. -/
theorem exists_forall_Q_flow_mem_ball_and_ι_eq
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) :
    ∃ ρ₂ ∈ Ioc 0 (min D.ρ ρ₁), ∀ z ∈ ball (0 : A.stableSubspace) ρ₂, ∀ t, 0 ≤ t →
      D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p) ∈ ball 0 ρ₁ ∧
        D.ι (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p)) =
          hW.flow t (D.ι z) := by
  obtain ⟨U, hU, ε, hε, hcov⟩ := D.exists_stableSet_inter_subset_image_ball
  set e := extChartAt 𝓘(ℝ, E) p
  -- A neighbourhood `V` of `p` lies in `U` and is mapped by `π` into the ball of radius `ρ₁`;
  -- orbits that start near `p`, with `f` close to `f p`, stay in `V`.
  have hπp : D.Q (e p - e p) = 0 := by simp
  have hV : U ∩ (fun x ↦ D.Q (e x - e p)) ⁻¹' ball 0 ρ₁ ∈ 𝓝 p :=
    inter_mem hU ((D.contMDiffOn_Q_extChartAt_sub.contMDiffAt ((isOpen_extChartAt_source p).mem_nhds
      (mem_extChartAt_source p))).continuousAt.preimage_mem_nhds
      (by rw [hπp]; exact ball_mem_nhds _ hρ₁))
  obtain ⟨r₀, hr₀, -, hconf⟩ := hW.exists_forall_flow_mem_source_and_norm_extChartAt_sub_le hp
  obtain ⟨r₁, hr₁, -, hr₁V⟩ := exists_chartBall_subset (I := 𝓘(ℝ, E)) hV
  obtain ⟨ε', hε', hc⟩ := hconf (min r₀ (r₁ / 2)) ⟨lt_min hr₀ (by positivity), min_le_left _ _⟩
  have hW₀ : (chartBall 𝓘(ℝ, E) p (min r₀ (r₁ / 2) / 2) : Set M) ∩
      {x | f p - min ε ε' < f x} ∈ 𝓝 p :=
    inter_mem (chartBall_mem_nhds _ p (by positivity))
      ((isOpen_lt continuous_const hW.isGeneralizedMorse.contMDiff.continuous).mem_nhds
        (by simp [hε, hε']))
  obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1
    ((D.contMDiffAt_ι 0 (mem_ball_self D.ρ_pos)).continuousAt.preimage_mem_nhds
      (by rwa [D.ι_zero]))
  refine ⟨min δ (min D.ρ ρ₁), ⟨lt_min hδ (lt_min D.ρ_pos hρ₁), min_le_right _ _⟩,
    fun z hz t ht ↦ ?_⟩
  obtain ⟨hzc, hzf⟩ := hδW (ball_subset_ball (min_le_left _ _) hz)
  have hzf : f p - min ε ε' < f (D.ι z) := hzf
  obtain ⟨hzs, hzb⟩ := (mem_chartBall_iff _).1 hzc
  rw [mem_ball, dist_eq_norm] at hzb
  have hzst : D.ι z ∈ hW.flow.stableSet p :=
    D.image_ball_subset_stableSet
      ⟨z, ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz, rfl⟩
  obtain ⟨hts, htb⟩ := hc (D.ι z) hzst hzs hzb.le
    ((sub_le_sub_left (min_le_right _ _) _).trans_lt hzf) t ht
  have hfle : f (D.ι z) ≤ f (hW.flow t (D.ι z)) := by
    simpa using hW.monotone_comp_flow (D.ι z) ht
  have hxV : hW.flow t (D.ι z) ∈ U ∩ (fun x ↦ D.Q (e x - e p)) ⁻¹' ball 0 ρ₁ :=
    hr₁V ((mem_chartBall_iff _).2 ⟨hts, by
      rw [mem_ball, dist_eq_norm]
      linarith [min_le_right r₀ (r₁ / 2)]⟩)
  obtain ⟨w, hw, hwx⟩ := hcov ⟨⟨(Flow.apply_mem_stableSet_iff _ _).2 hzst, hxV.1⟩,
    ((sub_le_sub_left (min_le_left _ _) _).trans_lt hzf).trans_le hfle⟩
  refine ⟨hxV.2, ?_⟩
  rw [← hwx, D.Q_extChartAt_ι_sub hw]

/-- **`-H` decreases along a local stable disc.** Let `D` be a local stable disc, with map `ι`,
radius `ρ` and left inverse `π x = Q (e x - e p)`, of a nondegenerate critical point `p` of the
function of a Weinstein structure `(ω, X, f)` with flow `φ`, over the stable subspace of the
linearization `A` of `X` at `p`. Let `e` be the extended chart at `p` and
`H = fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p)` the second derivative of `f` read in `e`. There is a
radius `ρ' ∈ (0, ρ]` such that for `z` in the ball of radius `ρ'` and `t ≥ 0`, the point
`ζ t = π (φ_t (ι z))` lies in the ball of radius `ρ` and `ι (ζ t) = φ_t (ι z)`; and if `z ≠ 0`,
then `t ↦ -H (ζ t) (ζ t)` has a negative derivative at every `t ≥ 0`, so it is strictly antitone
on `[0, ∞)`. -/
theorem exists_forall_flow_strictAntiOn
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) :
    ∃ ρ' ∈ Ioc 0 D.ρ, ∀ z ∈ ball (0 : A.stableSubspace) ρ',
      (∀ t, 0 ≤ t →
        D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p) ∈ ball 0 D.ρ ∧
        D.ι (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p)) =
          hW.flow t (D.ι z)) ∧
      (z ≠ 0 → (∀ t, 0 ≤ t → ∃ d < 0, HasDerivAt (fun s ↦
        -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
          (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow s (D.ι z)) - extChartAt 𝓘(ℝ, E) p p))
          (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow s (D.ι z)) - extChartAt 𝓘(ℝ, E) p p))) d t) ∧
        StrictAntiOn (fun t ↦
          -fderiv ℝ (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) p).symm)) (extChartAt 𝓘(ℝ, E) p p)
            (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p))
            (D.Q (extChartAt 𝓘(ℝ, E) p (hW.flow t (D.ι z)) - extChartAt 𝓘(ℝ, E) p p)))
          (Ici 0)) := by
  obtain ⟨C, δ₁, hδ₁, hC⟩ := D.exists_norm_extChartAt_sub_le
  set e := extChartAt 𝓘(ℝ, E) p
  set H := fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p)
  have hXp := hW.mdifferentiableAt_field p
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 (mem_criticalPoints.1 hp.mem_criticalPoints)
  obtain ⟨c, hc, hcB⟩ := hW.isGradientLike.exists_pos_mul_norm_sq_le_fderiv_fderiv hp hXp hA
  have hB := ((isManifoldNondegenerateCriticalPoint_iff _).1 hp).contDiffAt.isSymmSndFDerivAt
    (by simp)
  -- The coordinate field `Y`, recentred at `p`, vanishes at `0` with derivative `A` there.
  set Y : E → E := fun w ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X (e p + w) with hYdef
  have hY0 : Y 0 = 0 := by
    simp only [hYdef]
    rw [add_zero]
    exact (VectorField.mpullback_extChartAt_symm_self X p).trans hp0
  have hY : HasFDerivAt Y A 0 := by
    have h : HasFDerivAt (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X) A (e p + 0) := by
      rw [add_zero, hA]
      exact hXp.hasFDerivAt_mpullback_extChartAt_symm
    exact (h.comp 0 ((hasFDerivAt_id 0).const_add (e p))).congr_fderiv A.comp_id
  obtain ⟨δ, hδ, hδB⟩ :=
    ContinuousLinearMap.exists_forall_half_mul_norm_sq_le_apply hc hcB D.commute_P hY0 hY C
  -- On the disc over a small ball, `H ζ (P (Y w)) ≥ c / 2 * ‖ζ‖ ^ 2` at `w = e (ι ζ) - e p`.
  set ρ₁ := min D.ρ (min δ₁ (δ / (|C| + 1)))
  have hρ₁ : 0 < ρ₁ := lt_min D.ρ_pos (lt_min hδ₁ (by positivity))
  have hkey (ζ : A.stableSubspace) (hζ : ζ ∈ ball 0 ρ₁) :
      D.P (e (D.ι ζ) - e p) = ζ ∧ c / 2 * ‖ζ‖ ^ 2 ≤ H ζ (D.P (Y (e (D.ι ζ) - e p))) := by
    rw [mem_ball_zero_iff] at hζ
    have hζρ : ζ ∈ ball 0 D.ρ := mem_ball_zero_iff.2 (hζ.trans_le (min_le_left _ _))
    have hPw : D.P (e (D.ι ζ) - e p) = ζ := by rw [← D.coe_Q_apply, D.Q_extChartAt_ι_sub hζρ]
    have hw := hC ζ (mem_ball_zero_iff.2 (hζ.trans_le ((min_le_right _ _).trans
      (min_le_left _ _))))
    have hζδ : ‖ζ‖ < δ / (|C| + 1) := hζ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hwδ : ‖e (D.ι ζ) - e p‖ < δ :=
      calc ‖e (D.ι ζ) - e p‖ ≤ C * ‖ζ‖ := hw
        _ ≤ (|C| + 1) * ‖ζ‖ := by gcongr; linarith [le_abs_self C]
        _ < (|C| + 1) * (δ / (|C| + 1)) := by gcongr
        _ = δ := by field_simp
    have h := hδB _ hwδ (by rw [hPw]; exact hw)
    rw [hPw] at h
    exact ⟨hPw, h⟩
  obtain ⟨ρ', ⟨hρ', hρ'le⟩, hρ'inv⟩ := D.exists_forall_Q_flow_mem_ball_and_ι_eq hp hρ₁
  have hρ'ρ : ρ' ≤ D.ρ := hρ'le.trans (min_le_left _ _)
  refine ⟨ρ', ⟨hρ', hρ'ρ⟩, fun z hz ↦ ?_⟩
  have hzρ : z ∈ ball 0 D.ρ := ball_subset_ball hρ'ρ hz
  set ζ : ℝ → A.stableSubspace := fun s ↦ D.Q (e (hW.flow s (D.ι z)) - e p) with hζdef
  set w : ℝ → E := fun s ↦ e (hW.flow s (D.ι z)) - e p with hwdef
  have hinv' (t : ℝ) (ht : 0 ≤ t) : ζ t ∈ ball 0 ρ₁ ∧ D.ι (ζ t) = hW.flow t (D.ι z) :=
    hρ'inv z hz t ht
  refine ⟨fun t ht ↦ ⟨ball_subset_ball (min_le_left _ _) (hinv' t ht).1, (hinv' t ht).2⟩,
    fun hz0 ↦ ?_⟩
  obtain ⟨C', hC'⟩ := D.exists_forall_flow_mem_source_and_norm_fderiv_le z hzρ
  -- The derivative of `-H (ζ s) (ζ s)` at `t ≥ 0`, through the chart solution `w`.
  have hderiv (t : ℝ) (ht : 0 ≤ t) : ∃ d < 0, HasDerivAt (fun s ↦ -H (ζ s) (ζ s)) d t := by
    have hO : IsOpen {s | hW.flow s (D.ι z) ∈ e.source} :=
      (isOpen_extChartAt_source p).preimage (hW.isMIntegralCurve_flow (D.ι z)).continuous
    have hwi : IsIntegralCurveOn w (fun _ ↦ Y) {s | hW.flow s (D.ι z) ∈ e.source} := by
      have h := TauCeti.isIntegralCurveOn_extChartAt_globalFlow_sub
        (hW.contMDiff_field.of_le (by simp)) hW.isCompleteVectorField
        (s := {s | hW.flow s (D.ι z) ∈ e.source}) (p := p) (x := D.ι z) fun s hs ↦ by
          rw [← hW.flow_def]; exact hs
      rwa [← hW.flow_def] at h
    have hwt : HasDerivAt w (Y (w t)) t :=
      (hwi t (hC' t ht).1).hasDerivAt (hO.mem_nhds (hC' t ht).1)
    have hfun : (fun s ↦ -H (ζ s) (ζ s)) = fun s ↦ -H (D.P (w s)) (D.P (w s)) := by
      funext s
      simp only [hζdef, hwdef, D.coe_Q_apply]
    have hd := ContinuousLinearMap.hasDerivAt_neg_apply_self_comp hB D.P hwt
    rw [← hfun] at hd
    refine ⟨_, ?_, hd⟩
    -- `w t` is the chart point of `ι (ζ t)`, and `ζ t ≠ 0` since the orbit of `ι z` avoids `p`.
    have hwζ : w t = e (D.ι (ζ t)) - e p := by simp only [hwdef, (hinv' t ht).2]
    obtain ⟨hPw, hle⟩ := hkey (ζ t) (hinv' t ht).1
    have hζ0 : ζ t ≠ 0 := by
      intro h0
      have hxp : hW.flow t (D.ι z) = p := by rw [← (hinv' t ht).2, h0, D.ι_zero]
      have hzp : D.ι z = p := by
        rw [← Flow.map_zero_apply hW.flow (D.ι z), ← neg_add_cancel t, Flow.map_add, hxp,
          hW.flow_apply_of_mvfderiv_eq_zero (mem_criticalPoints.1 hp.mem_criticalPoints)]
      apply hz0
      rw [← D.Q_extChartAt_ι_sub hzρ, hzp, sub_self, map_zero]
    rw [hwζ, hPw]
    have := mul_pos (half_pos hc) (pow_pos (norm_pos_iff.2 hζ0) 2)
    linarith
  refine ⟨hderiv, strictAntiOn_of_deriv_neg (convex_Ici 0) (fun t ht ↦ ?_) fun t ht ↦ ?_⟩
  · obtain ⟨d, -, hd⟩ := hderiv t ht
    exact hd.continuousAt.continuousWithinAt
  · rw [interior_Ici] at ht
    obtain ⟨d, hd0, hd⟩ := hderiv t (le_of_lt ht)
    rw [hd.deriv]
    exact hd0

end LocalStableDisc

section Bounded

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- **A forward derivative bound makes `ι_X ω` vanish.** Let `(ω, X, f)` be a Weinstein
structure with flow `φ`, `e` the extended chart at `p`, and `γ : N → M` differentiable at `y`,
with `γ y` in the stable set of `p`. If for each tangent vector `v` at `y` the derivative of
`z ↦ e (φ_t (γ z))` at `y` on `v` is bounded for all large `t`, then the pullback of the one-form
`ι_X ω` by `γ` vanishes at `y`. -/
theorem mpullback_interior_eq_zero_of_bounded {p : M} {γ : N → M} {y : N}
    (hγ : MDifferentiableAt I' 𝓘(ℝ, E) γ y) (hy : γ y ∈ hW.flow.stableSet p)
    (hb : ∀ v : TangentSpace I' y, ∃ C, ∀ᶠ t in atTop,
      ‖mvfderiv I' (fun z ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (γ z))) y v‖ ≤ C) :
    mpullback I' 𝓘(ℝ, E) γ (RoughForm.interior X ω.val) y = 0 := by
  have hα : IsSmoothForm 𝓘(ℝ, E) (⊤ : ℕ∞) (RoughForm.interior X ω.val) :=
    (ω.isSmoothForm.of_le (by simp)).interior hW.contMDiff_field
  refine hW.flow.mpullback_eq_zero_of_mpullback_eq_exp_smul
    (fun t ↦ (hW.contMDiff_flow_apply t).mdifferentiable (by simp)) (hα.of_le (by simp))
    (fun t ↦ ?_) hγ hy hb
  rw [flow_def]
  exact mpullback_globalFlow_eq_exp_smul_of_interior_eq _ _
    (hα.contMDiff.mdifferentiable (by simp)) hW.mextDeriv_interior rfl t

/-- **A forward derivative bound makes `ω` vanish.** Let `(ω, X, f)` be a Weinstein structure
with flow `φ`, `e` the extended chart at `p`, and `γ : N → M` differentiable at `y`, with `γ y`
in the stable set of `p`. If for each tangent vector `v` at `y` the derivative of
`z ↦ e (φ_t (γ z))` at `y` on `v` is bounded for all large `t`, then the pullback of `ω` by `γ`
vanishes at `y`. -/
theorem mpullback_eq_zero_of_bounded {p : M} {γ : N → M} {y : N}
    (hγ : MDifferentiableAt I' 𝓘(ℝ, E) γ y) (hy : γ y ∈ hW.flow.stableSet p)
    (hb : ∀ v : TangentSpace I' y, ∃ C, ∀ᶠ t in atTop,
      ‖mvfderiv I' (fun z ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (γ z))) y v‖ ≤ C) :
    mpullback I' 𝓘(ℝ, E) γ ω.val y = 0 := by
  refine hW.flow.mpullback_eq_zero_of_mpullback_eq_exp_smul
    (fun t ↦ (hW.contMDiff_flow_apply t).mdifferentiable (by simp))
    (ω.isSmoothForm.of_le (by simp)) (fun t ↦ ?_) hγ hy hb
  rw [flow_def]
  exact IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul _ _
    ω.mdifferentiable hW.isLiouvilleVectorField t

/-- **Maps into the stable set have a forward derivative bound.** Let `(ω, X, f)` be a Weinstein
structure with flow `φ`, `p` a nondegenerate critical point of `f`, `e` the extended chart at
`p`, and `γ : N → M` differentiable at `y`, with range in the stable set of `p`. Then for each
tangent vector `v` at `y`, the derivative of `z ↦ e (φ_t (γ z))` at `y` on `v` is bounded for all
large `t`. -/
theorem exists_eventually_norm_mvfderiv_le_of_range_subset_stableSet {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {γ : N → M} {y : N}
    (hγ : MDifferentiableAt I' 𝓘(ℝ, E) γ y) (hs : range γ ⊆ hW.flow.stableSet p)
    (v : TangentSpace I' y) :
    ∃ C, ∀ᶠ t in atTop,
      ‖mvfderiv I' (fun z ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (γ z))) y v‖ ≤ C := by
  set A : E →L[ℝ] E := sectionLinearization (F := E) 𝓘(ℝ, E) id X p with hA
  obtain ⟨D⟩ := hW.exists_localStableDisc hp hA
  obtain ⟨U, hU, ε, hε, hcov⟩ := D.exists_stableSet_inter_subset_image_ball
  set e := extChartAt 𝓘(ℝ, E) p
  obtain ⟨π, hπ, hπι⟩ : ∃ π : M → A.stableSubspace,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, A.stableSubspace) (⊤ : ℕ∞) π e.source ∧
        ∀ z ∈ ball (0 : A.stableSubspace) D.ρ, π (D.ι z) = z :=
    ⟨_, D.contMDiffOn_Q_extChartAt_sub, fun _ hz ↦ D.Q_extChartAt_ι_sub hz⟩
  have hfc : Continuous f := hW.isGeneralizedMorse.contMDiff.continuous
  -- The orbit of `γ y` enters, at some time `T`, the part of the stable set that the disc covers;
  -- by continuity, so does the orbit of `γ z` for `z` near `y`.
  have hV : IsOpen (interior U ∩ {x | f p - ε < f x}) :=
    isOpen_interior.inter (isOpen_lt continuous_const hfc)
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 (hs ⟨y, rfl⟩)).eventually
    (hV.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hU, by simpa using hε⟩)).exists
  have hγc : ContinuousAt (fun z ↦ hW.flow T (γ z)) y :=
    (hW.contMDiff_flow_apply T).continuous.continuousAt.comp hγ.continuousAt
  have hnear : ∀ᶠ z in 𝓝 y, hW.flow T (γ z) ∈ D.ι '' ball 0 D.ρ := by
    filter_upwards [hγc.preimage_mem_nhds (hV.mem_nhds hT)] with z hz
    exact hcov ⟨⟨(Flow.apply_mem_stableSet_iff _ _).2 (hs ⟨z, rfl⟩), interior_subset hz.1⟩, hz.2⟩
  have hιπ (z : N) (hz : hW.flow T (γ z) ∈ D.ι '' ball 0 D.ρ) :
      π (hW.flow T (γ z)) ∈ ball 0 D.ρ ∧ D.ι (π (hW.flow T (γ z))) = hW.flow T (γ z) := by
    obtain ⟨w, hw, hwz⟩ := hz
    rw [← hwz, hπι w hw]
    exact ⟨hw, rfl⟩
  -- Near `y`, `φ_T ∘ γ` is `ι ∘ h` with `h = π ∘ φ_T ∘ γ` differentiable at `y`.
  obtain ⟨hy0, hy1⟩ := hιπ y hnear.self_of_nhds
  obtain ⟨C, hC⟩ := D.exists_forall_flow_mem_source_and_norm_fderiv_le _ hy0
  have hsrc : hW.flow T (γ y) ∈ e.source := by
    simpa [hy1, e, extChartAt_source] using (hC 0 le_rfl).1
  have hh : MDifferentiableAt I' 𝓘(ℝ, A.stableSubspace) (fun z ↦ π (hW.flow T (γ z))) y :=
    ((hπ.contMDiffAt ((isOpen_extChartAt_source p).mem_nhds hsrc)).mdifferentiableAt
      (by simp)).comp y
      (((hW.contMDiff_flow_apply T).mdifferentiable (by simp)).mdifferentiableAt.comp y hγ)
  refine ⟨C * ‖mvfderiv I' (fun z ↦ π (hW.flow T (γ z))) y v‖, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  obtain ⟨-, hd, hn⟩ := hC (t - T) (sub_nonneg.2 ht)
  have heq : (fun z ↦ e (hW.flow t (γ z))) =ᶠ[𝓝 y]
      (fun w ↦ e (hW.flow (t - T) (D.ι w))) ∘ fun z ↦ π (hW.flow T (γ z)) := by
    filter_upwards [hnear] with z hz
    rw [Function.comp_apply, (hιπ z hz).2, ← Flow.map_add, sub_add_cancel]
  rw [heq.mvfderiv_eq,
    mvfderiv_comp_apply_of_differentiableAt (M := N) (g := fun z ↦ π (hW.flow T (γ z))) hd hh v]
  exact ((fderiv ℝ _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

/-- **Stable sets are `ι_X ω`-isotropic.** Let `(ω, X, f)` be a Weinstein structure, `p` a
nondegenerate critical point of `f`, and `γ : N → M` differentiable at `y`, with range in the
stable set of `p`. Then the one-form `ι_X ω` vanishes at `γ y` on the image of the differential
of `γ` at `y`.

See [CieliebakEliashberg2012], Proposition 11.9 (a). -/
theorem interior_apply_mfderiv_eq_zero_of_range_subset_stableSet {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {γ : N → M} {y : N}
    (hγ : MDifferentiableAt I' 𝓘(ℝ, E) γ y) (hs : range γ ⊆ hW.flow.stableSet p)
    (v : TangentSpace I' y) :
    RoughForm.interior X ω.val (γ y) ![mfderiv I' 𝓘(ℝ, E) γ y v] = 0 := by
  rw [← mpullback_apply_one, hW.mpullback_interior_eq_zero_of_bounded hγ (hs ⟨y, rfl⟩)
    (hW.exists_eventually_norm_mvfderiv_le_of_range_subset_stableSet hp hγ hs)]
  rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- **Stable sets are isotropic.** Let `(ω, X, f)` be a Weinstein structure, `p` a nondegenerate
critical point of `f`, and `γ : N → M` differentiable at `y`, with range in the stable set of
`p`. Then `ω` vanishes at `γ y` on every pair of vectors in the image of the differential of `γ`
at `y`.

See [CieliebakEliashberg2012], Proposition 11.9 (a). -/
theorem apply_mfderiv_mfderiv_eq_zero_of_range_subset_stableSet {p : M}
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p) {γ : N → M} {y : N}
    (hγ : MDifferentiableAt I' 𝓘(ℝ, E) γ y) (hs : range γ ⊆ hW.flow.stableSet p)
    (v w : TangentSpace I' y) :
    ω.val (γ y) ![mfderiv I' 𝓘(ℝ, E) γ y v, mfderiv I' 𝓘(ℝ, E) γ y w] = 0 := by
  rw [← mpullback_apply_pair, hW.mpullback_eq_zero_of_bounded hγ (hs ⟨y, rfl⟩)
    (hW.exists_eventually_norm_mvfderiv_le_of_range_subset_stableSet hp hγ hs)]
  rw [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

end Bounded

end IsWeinsteinStructure

end SymplecticGeometry

end
