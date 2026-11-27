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
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.Morse.EnergyBarrier

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
value of `f` close to `f p`, never moves far from `p`.

This is the first step towards the isotropy of the stable discs of the nondegenerate critical
points. The conformal scaling `φ_t^* ω = e^t ω` and `φ_t^* (ι_X ω) = e^t ι_X ω` of the flow is
Tau Ceti's `TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul` and
`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`. They are stated for `globalFlow`, and
apply to `SymplecticGeometry.IsWeinsteinStructure.flow` after a rewrite with
`SymplecticGeometry.IsWeinsteinStructure.flow_def`.

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

## Implementation notes

The definitions and lemmas follow those of Tau Ceti's `TauCeti.IsAdaptedPseudoGradient.flow`,
which names the flow of an adapted pseudo-gradient in the same way. Tau Ceti's pseudo-gradients
decrease the function, while a Weinstein field increases it; the bound on the stable set is
therefore `TauCeti.Flow.le_of_mem_stableSet_of_antitone` applied to `-f`. The confinement near a
critical point is `TauCeti.IsGradientLike.exists_forall_mem_source_and_norm_extChartAt_sub_le`
(`SymplecticGeometry.Geometry.Manifold.Morse.EnergyBarrier`), applied to the orbits of the flow;
a nondegenerate critical point is isolated by Tau Ceti's
`TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 11; this file prepares Proposition 11.9 (a), the isotropy of the stable manifolds
-/

public section

open Function Metric Set TauCeti
open scoped Manifold

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

end IsWeinsteinStructure

end SymplecticGeometry

end
