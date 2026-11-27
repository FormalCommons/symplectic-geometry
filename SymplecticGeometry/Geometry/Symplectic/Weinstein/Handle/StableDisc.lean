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
import SymplecticGeometry.Analysis.Calculus.FDeriv.Graph
import TauCeti.Analysis.ODE.ExponentialDichotomy
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
field read in that chart, the stable set of `p` near `p` is the image of a disc in the stable
subspace of the linearization of `X` at `p`, along which the derivative of the flow, read in the
chart at `p`, stays bounded for all positive times.

This prepares the isotropy of the stable discs of the nondegenerate critical
points. The conformal scaling `φ_t^* ω = e^t ω` and `φ_t^* (ι_X ω) = e^t ι_X ω` of the flow is
Tau Ceti's `TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul` and
`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`. They are stated for `globalFlow`, and
apply to `SymplecticGeometry.IsWeinsteinStructure.flow` after a rewrite with
`SymplecticGeometry.IsWeinsteinStructure.flow_def`. With them,
`Flow.mpullback_eq_zero_of_mpullback_eq_exp_smul` shows that a map into the stable set along
which the derivative of the flow, read in the chart at `p`, stays bounded for all large times
pulls both forms back to zero.

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
* `SymplecticGeometry.IsWeinsteinStructure.exists_forall_flow_mem_source_and_norm_extChartAt_sub_le`
  states that at a nondegenerate critical point `p`, the orbits of the points of the stable set
  of `p` that start in a small ball of the chart at `p`, with `f` close to `f p`, stay in a
  slightly larger ball.
* `SymplecticGeometry.IsWeinsteinStructure.exists_localStableDisc`: the local stable disc of a
  nondegenerate critical point `p`, a `C^n` map from the stable subspace of the linearization
  with injective differential on a ball, whose image there lies in the stable set of `p` and
  contains every point of it near `p` at which `f` is close to `f p`, whose orbits in positive
  time stay in the chart at `p`, and along which the derivative of the flow, read in that chart,
  exists and is bounded in positive time.
* `SymplecticGeometry.IsWeinsteinStructure.mpullback_interior_eq_zero_of_bounded` and
  `SymplecticGeometry.IsWeinsteinStructure.mpullback_eq_zero_of_bounded`: a map `γ` with `γ y`
  in the stable set of `p` pulls `ι_X ω` and `ω` back to zero at `y`, if the derivative at `y`
  of `γ` followed by the flow, read in the chart at `p`, is bounded for all large times on each
  tangent vector.

## Implementation notes

The definitions and lemmas follow those of Tau Ceti's `TauCeti.IsAdaptedPseudoGradient.flow`,
which names the flow of an adapted pseudo-gradient in the same way. Tau Ceti's pseudo-gradients
decrease the function, while a Weinstein field increases it; the bound on the stable set is
therefore `TauCeti.Flow.le_of_mem_stableSet_of_antitone` applied to `-f`. The confinement near a
critical point is `TauCeti.IsGradientLike.exists_forall_mem_source_and_norm_extChartAt_sub_le`
(`SymplecticGeometry.Geometry.Manifold.Morse.EnergyBarrier`), applied to the orbits of the flow;
a nondegenerate critical point is isolated by Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints`.
The disc is built in the extended chart `e` at `p`. The dichotomy for the linearization `A`
(`TauCeti.IsGradientLike.exists_projection_exponential_bounds`, in
`SymplecticGeometry.Geometry.Symplectic.Weinstein.Handle.Linearization`) gives a projection `P`
onto the stable subspace, and `ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_fderiv`,
applied to the field read in `e` with a confinement radius within the chart target, gives the
graph map `g` and the confined forward solutions over `range P`. The disc is
`z ↦ e.symm (e p + z + g z)`. Its orbits are the solutions read back through `e`, by
`TauCeti.extChartAt_symm_add_eq_globalFlow`; the covering statement combines the confinement of
the stable set with the description of the confined solutions as the graph, and the differential
is injective since `P ∘ g = 0`, by
`ContinuousLinearMap.injective_fderiv_add_comp_subtype`.
The covering step, which first confines the orbits of the stable set near `p` and then identifies
them with the local stable graph, follows the plan of Tau Ceti's
`TauCeti.IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_stableSet`
(`TauCeti.Analysis.Calculus.Morse.GlobalChart`), for negative gradient flows on a vector space.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11; this file prepares Proposition 11.9 (a), the isotropy of the stable manifolds
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

/-- **The local stable disc of a nondegenerate critical point.** Let `p` be a nondegenerate
critical point of the function of a Weinstein structure, `A` the linearization of the Liouville
field at `p`, and `e` the extended chart at `p`. For every `n ≥ 1` there are a map `ι` from the
stable subspace of `A` to `M` with `ι 0 = p` and a radius `ρ > 0` such that:
* on the ball of radius `ρ`, `ι` is `C^n` and its differential is injective;
* `ι` maps that ball into the stable set of `p`;
* the image of that ball contains every point of the stable set of `p` that lies in some
  neighbourhood `U` of `p` and at which `f` exceeds `f p - ε`, for some `ε > 0`;
* at each point `z` of that ball and each `t ≥ 0`, where `φ` is the flow of the Liouville field,
  the point `φ_t (ι z)` lies in the source of `e`, the map `w ↦ e (φ_t (ι w))` is differentiable
  at `z`, and its derivative there is bounded independently of `t`. -/
theorem exists_localStableDisc {p : M} (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    {A : E →L[ℝ] E} (hA : A = sectionLinearization (F := E) 𝓘(ℝ, E) id X p) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ ι : A.stableSubspace → M, ∃ ρ > 0, ι 0 = p ∧
      (∀ z ∈ ball (0 : A.stableSubspace) ρ,
        ContMDiffAt 𝓘(ℝ, A.stableSubspace) 𝓘(ℝ, E) n ι z ∧
          Injective (mfderiv 𝓘(ℝ, A.stableSubspace) 𝓘(ℝ, E) ι z)) ∧
      ι '' ball 0 ρ ⊆ hW.flow.stableSet p ∧
      (∃ U ∈ 𝓝 p, ∃ ε > 0, hW.flow.stableSet p ∩ U ∩ {x | f p - ε < f x} ⊆ ι '' ball 0 ρ) ∧
      ∀ z ∈ ball (0 : A.stableSubspace) ρ, ∃ C : ℝ, ∀ t, 0 ≤ t →
        hW.flow t (ι z) ∈ (extChartAt 𝓘(ℝ, E) p).source ∧
          DifferentiableAt ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (ι w))) z ∧
          ‖fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) p (hW.flow t (ι w))) z‖ ≤ C := by
  have hXp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent
      (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) p :=
    (hW.contMDiff_field p).mdifferentiableAt (by simp)
  have hp0 : X p = 0 := hW.isGradientLike.eq_zero_iff.2 (mem_criticalPoints.1 hp.mem_criticalPoints)
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x ↦ (X x : TangentBundle 𝓘(ℝ, E) M)) :=
    hW.contMDiff_field.of_le (by simp)
  -- The dichotomy of the linearization, and the confinement radius `r₀`.
  obtain ⟨P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    hW.isGradientLike.exists_projection_exponential_bounds hp hXp hA
  have hPS : (P : E →ₗ[ℝ] E).range = A.stableSubspace :=
    ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds hα hP hAP hs hu
  obtain ⟨r₀, hr₀, hr₀t, hconf⟩ := hW.exists_forall_flow_mem_source_and_norm_extChartAt_sub_le hp
  -- The local stable graph of the coordinate field, with confinement radius at most `r₀`.
  obtain ⟨r, hr, hrr₀, ρ, hρ, g, -, -, hg0, -, hgn, hPg, -, hset, htend, y, hy⟩ :=
    ContinuousLinearMap.exists_localStableGraph_of_contDiffAt_fderiv (n := n) hs hu hα hP hAP hn
      ((hW.contMDiff_field p).of_le (by simp)).contDiffAt_mpullback_extChartAt_symm
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
  refine ⟨ι, ρ, hρ, by simpa [hι, hg0] using e.left_inv (mem_extChartAt_source p),
    fun z hz ↦ ?_, ?_, ?_, fun z hz ↦ ?_⟩
  · -- Smoothness and injectivity of the differential.
    obtain ⟨-, -, hy0, -⟩ := hy z (hball z hz)
    have hq : e p + ((z : E) + g z) ∈ e.target := by simpa [hy0] using (horb z hz 0 le_rfl).1
    have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have hgz : ContDiffAt ℝ n g z := hgn _ (hball z hz).2
    have hhd : ContDiffAt ℝ n (fun w : S ↦ e p + ((w : E) + g w)) z :=
      contDiffAt_const.add (S.subtypeL.contDiff.contDiffAt.add
        (hgz.comp (f := S.subtypeL) z S.subtypeL.contDiff.contDiffAt))
    have hinj : Injective (fderiv ℝ (fun w : S ↦ e p + ((w : E) + g w)) z) := by
      rw [fderiv_const_add]
      exact P.injective_fderiv_add_comp_subtype (fun w hw ↦ hPz ⟨w, hw⟩) hPg
        (hgz.differentiableAt hn0)
    have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n e.symm (e p + ((z : E) + g z)) :=
      ((contMDiffOn_extChartAt_symm (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) p).of_le
        (by exact_mod_cast le_top)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hq)
    exact ⟨hsymm.comp z hhd.contMDiffAt,
      injective_mfderiv_extChartAt_symm_comp hq (hhd.differentiableAt hn0) hinj⟩
  · -- The image lies in the stable set.
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hyi, hymaps, -⟩ := hy z (hball z hz)
    refine Flow.mem_stableSet.2 (Tendsto.congr' (f₁ := fun t ↦ e.symm (e p + y z t)) ?_ ?_)
    · filter_upwards [eventually_ge_atTop 0] with t ht using (horb z hz t ht).2.symm
    · have h1 : Tendsto (fun t ↦ e p + y z t) atTop (𝓝 (e p)) := by
        simpa using (htend _ hyi hymaps).const_add (e p)
      have h := (continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) p).tendsto.comp h1
      simpa [he, Function.comp_def] using h
  · -- The image covers the stable set near `p`, at values of `f` close to `f p`.
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
    have hmem : Y 0 ∈ {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y
        (fun _ w ↦ VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm X (e p + w)) (Ici 0) ∧
          y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} :=
      ⟨⟨Y, hYi, rfl, fun t ht ↦ by simpa [Y] using (hcx t ht).2⟩, hPY.le⟩
    rw [hset] at hmem
    obtain ⟨_, ⟨⟨w, rfl⟩, -⟩, hw⟩ := hmem
    simp only at hw
    have hPw : P (Y 0) = P w := by
      rw [← hw, map_add, hPg, add_zero, ← mul_apply_eq_comp, hP.eq]
    have hwS : P w ∈ S := hPS ▸ LinearMap.mem_range_self (P : E →ₗ[ℝ] E) w
    refine ⟨⟨P w, hwS⟩, by simpa [← hPw] using hPY, ?_⟩
    simp only [hι]
    rw [hw, hY0, add_sub_cancel, e.left_inv hxs]
  · -- The derivative of `w ↦ e (φ_t (ι w))` is bounded in `t ≥ 0`.
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

end Bounded

end IsWeinsteinStructure

end SymplecticGeometry

end
