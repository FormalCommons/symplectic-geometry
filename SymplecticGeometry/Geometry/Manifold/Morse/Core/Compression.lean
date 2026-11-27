/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Dynamics.OmegaLimit
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
import SymplecticGeometry.Dynamics.Flow.OmegaLimit
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Compression of a sublevel along a descending flow

Let `Y` be a complete `C¹` vector field on a boundaryless manifold `M`, with flow
`Φ = TauCeti.globalFlow Y`, and `g` a differentiable function with `dg(Y) ≤ 0`. For a compact set
`S` that the flow maps into itself in forward time, such as a compact sublevel `{g ≤ b}`, late
time maps of the flow carry `S` into every open neighbourhood of the ω-limit set `ω atTop Φ S`
(Mathlib's `eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`). Each point
of that set has its whole orbit in `S`, and its backward orbit clusters at a point `z`
of `S` with `dg(Y) = 0` at `z`, at a level `g z` no lower than its own
(`TauCeti.exists_mapClusterPt_atBot_globalFlow_of_mem_omegaLimit`).

This is the ω-limit argument of the compression across a critical level: there `Y` is a cutoff
of a gradient-like field, and the zeros of `dg(Y)` are the zero set of the cutoff and the critical
points of the level.

## Main results

* `TauCeti.exists_mapClusterPt_atBot_globalFlow_of_mem_omegaLimit`: the backward orbit of a point
  of the ω-limit set of a compact forward invariant set clusters at a zero of `dg(Y)` in that set,
  along whose orbit `g` is constant, at a level no lower than that of the point.

The topological part is `Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit`
(`SymplecticGeometry/Dynamics/Flow/OmegaLimit.lean`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Part I, §3.
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Filter Set Topology
open scoped omegaLimit Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M]
  {Y : (x : M) → TangentSpace I x}

/-- **Backward orbits of the ω-limit set of a descending flow.** Let `Y` be a complete `C¹`
vector field with flow `Φ`, and `g` a differentiable function with `dg(Y) ≤ 0`. Let `S` be a
compact set with `Φ t` mapping `S` into itself for `t ≥ 0`. Then every point `y` of the ω-limit
set `ω atTop Φ S` has its whole orbit in `S`, and its backward orbit has a cluster point `z ∈ S`
at `-∞` with `g y ≤ g z`, along whose orbit `g` is constant, and at which `dg(Y) = 0`. -/
theorem exists_mapClusterPt_atBot_globalFlow_of_mem_omegaLimit
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField Y) {g : M → ℝ} (hg : MDifferentiable I 𝓘(ℝ) g)
    (hgY : ∀ x, mvfderiv I g x (Y x) ≤ 0) {S : Set M} (hS : IsCompact S)
    (hmaps : ∀ t, 0 ≤ t → MapsTo (globalFlow Y hY hc t) S S) {y : M}
    (hy : y ∈ ω atTop (globalFlow Y hY hc) S) :
    (∀ t, globalFlow Y hY hc t y ∈ S) ∧ ∃ z ∈ S,
      MapClusterPt z atBot (fun t ↦ globalFlow Y hY hc t y) ∧ g y ≤ g z ∧
      (∀ t, g (globalFlow Y hY hc t z) = g z) ∧ mvfderiv I g z (Y z) = 0 := by
  have hanti (x : M) : Antitone fun t ↦ g (globalFlow Y hY hc t x) :=
    (isMIntegralCurve_globalFlow hY hc x).antitone_comp (fun _ ↦ hg _) fun _ ↦ hgY _
  obtain ⟨horb, z, hzS, hz, hle, hconst⟩ :=
    Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit hS hmaps hg.continuous (hanti y) hy
  refine ⟨horb, z, hzS, hz, hle, hconst, ?_⟩
  -- `g` is constant along the orbit of `z`, an integral curve of `Y` through `z` at time `0`.
  have hd := Manifold.hasDerivAt_comp_curve (hg _) (isMIntegralCurve_globalFlow hY hc z 0)
  have hconst' : (g ∘ fun t ↦ globalFlow Y hY hc t z) = fun _ ↦ g z := funext hconst
  rw [hconst'] at hd
  have h := hd.unique (hasDerivAt_const 0 (g z))
  -- The coercion of a `Flow` is its `toFun` field, so its time-zero law is `map_zero'`.
  beta_reduce at h
  rwa [(globalFlow Y hY hc).map_zero' z] at h

end TauCeti
