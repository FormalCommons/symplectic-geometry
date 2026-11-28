/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Dynamics.OmegaLimit
public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Dynamics.Flow.OmegaLimit
public import SymplecticGeometry.Geometry.Manifold.Morse.Core.Basic
import SymplecticGeometry.Geometry.Manifold.Flow.Basic
import SymplecticGeometry.Geometry.Manifold.ModelTransport.Boundaryless
import SymplecticGeometry.Geometry.Manifold.Morse.Core.Cube
import SymplecticGeometry.Geometry.Manifold.Morse.Core.PseudoGradient
import SymplecticGeometry.Geometry.Manifold.SmoothIsotopy.Diffeotopy
import SymplecticGeometry.Geometry.Manifold.VectorField.Cutoff
import SymplecticGeometry.Topology.Maps.Proper
import SymplecticGeometry.Topology.Order.Sublevel
import TauCeti.Geometry.Manifold.Flow.Locality
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.Morse.ModelTransport
import TauCeti.Topology.OmegaLimit

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

Running the flow for a late time is a diffeotopy, Tau Ceti's `TauCeti.globalFlowDiffeotopy` (for a
compactly supported field, `TauCeti.compactlySupportedFlowDiffeotopy`), which fixes the zeros of
`Y` at all times. So a bound on the ω-limit set gives a diffeotopy fixing the zeros of `Y` whose
final map carries `S` into the given neighbourhood
(`TauCeti.exists_diffeotopy_mapsTo_of_omegaLimit_subset`). Its proof follows the end of that of
`TauCeti.exists_diffeotopy_mapsTo_of_sublevel_subset`
(`SymplecticGeometry/Geometry/Manifold/Morse/Core/Basic.lean`), with the ω-limit bound in place
of a crossing time.

This is the ω-limit argument of the compression across a critical level: there `Y` is a cutoff
of a gradient-like field, and the zeros of `dg(Y)` are the zero set of the cutoff and the critical
points of the level. The cube charts of the critical points are built for the flow of the
gradient-like field `X` itself, not for that of its cutoff `Y`; above the level where the cutoff
is one, the backward orbits of the two flows agree, so a point of the ω-limit set above that level
lies in the unstable set, for the flow of `X`, of a critical point.

Put together, for a cutoff `ρ` of `g` that vanishes near `{g ≤ a}` and is one a little above
`a`, the flow of `Y = (ρ ∘ g) • X` gives a diffeotopy fixed near `{g ≤ a}` that carries a compact
sublevel `{g ≤ b}` into any open set containing `{g ≤ a}` and the parts above `a` of the
unstable sets of the critical points of the level `v`
(`TauCeti.exists_diffeotopy_mapsTo_of_unstableSet_subset`). The cut-off field is
`TauCeti.exists_cutoff_vectorField` (`VectorField/Cutoff.lean`).

On a manifold modelled on `E` itself, for a proper Morse function `g` bounded below whose
critical points in `g⁻¹[a₀, b]` all lie on the level `v` and have index less than `dim E`, this
gives a band core `SymplecticGeometry.BandCore 𝓘(ℝ, E) g a₀ a b`. The field `X` is the
compactly supported pseudo-gradient of `IsCompact.exists_contMDiff_pseudoGradient_eq_zero_off`
(`Morse/Core/PseudoGradient.lean`) on the band `g⁻¹[a₀, b]`; the cubes are those of
`TauCeti.MorseChart.exists_cubeChart_unstableSet` (`Morse/Core/Cube.lean`) at the critical
points of the level `v`, disjoint because they lie in the unstable sets of distinct points
(Tau Ceti's `Flow.disjoint_unstableSet`); and each open set containing `{g ≤ a}` and the cubes
contains the parts above `a` of those unstable sets, so the diffeotopy above gives a compression
(`TauCeti.Diffeotopy.exists_smoothIsotopy_id_of_mapsTo_final`,
`SmoothIsotopy/Diffeotopy.lean`).

For a general boundaryless model `I`, the band core comes from that of `g` read on Tau Ceti's
copy `TauCeti.BoundarylessModel I M`, a manifold modelled on `E` with the same topology, where
`g` stays a proper Morse function with the same critical points and indices
(`TauCeti/Geometry/Manifold/Morse/ModelTransport.lean`). It is pulled back to `M` along the
identity diffeomorphism `TauCeti.BoundarylessModel.diffeomorph` by
`SymplecticGeometry.BandCore.ofDiffeomorph`, as Tau Ceti's
`TauCeti.exists_flow_apply_eq_sub_of_isCompact` brings its flow back from that copy.

## Main results

* `TauCeti.mapsTo_globalFlow_preimage_Iic`: the flow maps each sublevel `{g ≤ b}` into itself in
  forward time.
* `TauCeti.mvfderiv_eq_zero_of_mapClusterPt_atBot_globalFlow`: a cluster point `z` at `-∞` of the
  orbit of `y` has `g y ≤ g z`, `g` is constant along its orbit, and `dg(Y) = 0` there.
* `TauCeti.exists_mapClusterPt_atBot_globalFlow_of_mem_omegaLimit`: the backward orbit of a point
  of the ω-limit set of a compact forward invariant set clusters at a zero of `dg(Y)` in that set,
  along whose orbit `g` is constant, at a level no lower than that of the point.
* `TauCeti.omegaLimit_globalFlow_subset_union_unstableSet`: if `Y = X` above a level `a`, and the
  critical points of `g` in `g⁻¹(a, b]` lie on one level `v`, finitely many, the other points there
  having `dg(X) < 0`, then the ω-limit set under the flow of `Y` of a compact forward invariant set
  `S ⊆ {g ≤ b}` lies in `{g ≤ a}` together with the parts above `a` of the unstable sets of those
  critical points for the flow of `X`.
* `TauCeti.exists_diffeotopy_mapsTo_of_omegaLimit_subset`: a diffeotopy fixing the zeros of a
  complete field, whose final map carries a compact forward invariant set into a given open
  neighbourhood of its ω-limit set.
* `TauCeti.exists_diffeotopy_mapsTo_of_unstableSet_subset`: a diffeotopy fixed near `{g ≤ a}`
  carrying `{g ≤ b}` into an open set containing `{g ≤ a}` and the parts above `a` of the
  unstable sets of the critical points of one level.
* `TauCeti.IsMorse.exists_bandCore`: a proper Morse function, bounded below, whose critical
  points in `g⁻¹[a₀, b]` lie on one level `v` with `a < v < b` and have index less than
  `dim E`, has a band core for the levels `a₀`, `a`, `b`.

The topological part is `Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit`
(`SymplecticGeometry/Dynamics/Flow/OmegaLimit.lean`); the convergence of a backward orbit
whose cluster points are finitely many is Tau Ceti's
`TauCeti.exists_tendsto_atTop_of_setOf_mapClusterPt_subset`, and the agreement of the backward
orbits of `X` and `Y` where the two fields agree is Tau Ceti's `TauCeti.flowOf_eq_of_eqOn`.

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

/-- **Sublevels are forward invariant under a descending flow.** Let `Y` be a complete `C¹`
vector field and `g` a differentiable function with `dg(Y) ≤ 0`. Then for `t ≥ 0` the flow map
`Φ t` sends each sublevel `{g ≤ b}` into itself. -/
theorem mapsTo_globalFlow_preimage_Iic
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField Y) {g : M → ℝ} (hg : MDifferentiable I 𝓘(ℝ) g)
    (hgY : ∀ x, mvfderiv I g x (Y x) ≤ 0) (b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    MapsTo (globalFlow Y hY hc t) (g ⁻¹' Iic b) (g ⁻¹' Iic b) := fun x hx ↦ by
  have h : g (globalFlow Y hY hc t x) ≤ g (globalFlow Y hY hc 0 x) :=
    antitone_comp_globalFlow hY hc hg hgY x ht
  rw [Flow.map_zero_apply] at h
  exact h.trans hx

/-- **Backward cluster points of a descending flow.** Let `Y` be a complete `C¹` vector field
with flow `Φ`, and `g` a differentiable function with `dg(Y) ≤ 0`. If `z` is a cluster point at
`-∞` of the orbit `t ↦ Φ t y`, then `g y ≤ g z`, `g` is constant along the orbit of `z`, and
`dg(Y) = 0` at `z`. -/
theorem mvfderiv_eq_zero_of_mapClusterPt_atBot_globalFlow
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField Y) {g : M → ℝ} (hg : MDifferentiable I 𝓘(ℝ) g)
    (hgY : ∀ x, mvfderiv I g x (Y x) ≤ 0) {y z : M}
    (hz : MapClusterPt z atBot (fun t ↦ globalFlow Y hY hc t y)) :
    g y ≤ g z ∧ (∀ t, g (globalFlow Y hY hc t z) = g z) ∧ mvfderiv I g z (Y z) = 0 := by
  have hanti : Antitone fun t ↦ g (globalFlow Y hY hc t y) :=
    antitone_comp_globalFlow hY hc hg hgY y
  have hconst := Flow.apply_flow_eq_of_mapClusterPt_atBot_of_antitone hanti hg.continuous hz
  refine ⟨?_, hconst, ?_⟩
  · simpa only [Flow.map_zero_apply] using
      (Flow.isLUB_of_mapClusterPt_atBot_of_antitone hanti hg.continuous.continuousAt hz).1
        ⟨0, rfl⟩
  · have h := ((isMIntegralCurve_globalFlow hY hc z).isMIntegralCurveAt 0
      ).mfderiv_apply_eq_zero_of_eventuallyEq_const (hg _) (.of_forall hconst)
    rwa [Flow.map_zero_apply] at h

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
  have hanti : Antitone fun t ↦ g (globalFlow Y hY hc t y) :=
    antitone_comp_globalFlow hY hc hg hgY y
  obtain ⟨horb, z, hzS, hz, -⟩ :=
    Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit hS hmaps hg.continuous hanti hy
  exact ⟨horb, z, hzS, hz, mvfderiv_eq_zero_of_mapClusterPt_atBot_globalFlow hY hc hg hgY hz⟩

/-- **The ω-limit set of a compact set under a cutoff flow.** Let `X` and `Y` be complete `C¹`
vector fields and `g` a differentiable function with `dg(X) ≤ 0` and `dg(Y) ≤ 0`, such that
`Y = X` at the points above a level `a`. Let `S ⊆ {g ≤ b}` be a compact set that the flow of `Y`
maps into itself in forward time, such as a compact sublevel `{g ≤ b}`. Suppose that at the
points `x` with `a < g x ≤ b` which are not critical for `g` we have `dg(X) < 0`, and that the
critical points there all lie on a level `v`, whose critical points are finitely many. Then every
point of the ω-limit set of `S` under the flow of `Y` either lies at level at most `a`, or lies
above `a` in the unstable set, for the flow of `X`, of a critical point of level `v`. -/
theorem omegaLimit_globalFlow_subset_union_unstableSet {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hXc : IsCompleteVectorField X)
    (hY : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hYc : IsCompleteVectorField Y) {g : M → ℝ} (hg : MDifferentiable I 𝓘(ℝ) g)
    (hgX : ∀ x, mvfderiv I g x (X x) ≤ 0) (hgY : ∀ x, mvfderiv I g x (Y x) ≤ 0)
    {a v b : ℝ} (hYX : ∀ x, a < g x → Y x = X x)
    (hneg : ∀ x, a < g x → g x ≤ b → x ∉ criticalPoints I g → mvfderiv I g x (X x) < 0)
    (hcrit : ∀ x ∈ criticalPoints I g, a < g x → g x ≤ b → g x = v)
    (hfin : (criticalPoints I g ∩ g ⁻¹' {v}).Finite) {S : Set M} (hS : IsCompact S)
    (hmaps : ∀ t, 0 ≤ t → MapsTo (globalFlow Y hY hYc t) S S) (hSb : S ⊆ g ⁻¹' Iic b) :
    ω atTop (globalFlow Y hY hYc) S ⊆
      g ⁻¹' Iic a ∪ ⋃ p ∈ criticalPoints I g ∩ g ⁻¹' {v},
        Flow.unstableSet (globalFlow X hX hXc) p ∩ g ⁻¹' Ioi a := by
  set Φ := globalFlow Y hY hYc
  set Ψ := globalFlow X hX hXc
  have hantiY (x : M) : Antitone fun t ↦ g (Φ t x) :=
    antitone_comp_globalFlow hY hYc hg hgY x
  intro y hy
  have horb :=
    (exists_mapClusterPt_atBot_globalFlow_of_mem_omegaLimit hY hYc hg hgY hS hmaps hy).1
  rcases le_or_gt (g y) a with hya | hya
  · exact Or.inl hya
  refine Or.inr ?_
  -- The backward orbit of `y` under `Φ` stays above `a`, where `Y = X`, so it is also the
  -- backward orbit of `y` under `Ψ`.
  have heq (t : ℝ) (ht : t ≤ 0) : Ψ t y = Φ t y := by
    have h := flowOf_eq_of_eqOn (U := {x | a < g x}) hY hX
      (isOpen_lt continuous_const hg.continuous) (fun x hx ↦ (hYX x hx).symm)
      (hYc.mem_flowDomain t y) ?_
    · simpa only [flowOf_eq_globalFlow hY hYc, flowOf_eq_globalFlow hX hXc] using h.2
    intro s hs
    rw [uIcc_of_ge ht] at hs
    simp only [flowOf_eq_globalFlow hY hYc, mem_ofPred_eq]
    exact hya.trans_le (by simpa only [Flow.map_zero_apply] using hantiY y hs.2)
  -- The backward orbit of `y` under `Ψ` lies in `S`, and clusters only at critical points
  -- of level `v`, so it converges to one of them.
  have hu : ContinuousOn (fun t ↦ Ψ (-t) y) (Ici 0) :=
    ((Ψ.continuous_eval_const y).comp continuous_neg).continuousOn
  have huS : MapsTo (fun t ↦ Ψ (-t) y) (Ici 0) S := fun t (ht : 0 ≤ t) ↦ by
    simpa only [heq (-t) (neg_nonpos.2 ht)] using horb (-t)
  have hsub : {z | MapClusterPt z atTop fun t ↦ Ψ (-t) y} ⊆ criticalPoints I g ∩ g ⁻¹' {v} := by
    intro z hz
    have hzb : g z ≤ b := hSb (hS.isClosed.mem_of_mapClusterPt hz
      ((eventually_ge_atTop 0).mono fun t ht ↦ huS ht))
    have hz' : MapClusterPt z atBot fun t ↦ Ψ t y := by
      rw [← map_neg_atTop, ← mapClusterPt_comp]
      simpa only [Function.comp_def, mem_ofPred_eq] using hz
    obtain ⟨hyz, -, hX0⟩ := mvfderiv_eq_zero_of_mapClusterPt_atBot_globalFlow hX hXc hg hgX hz'
    have hzc : z ∈ criticalPoints I g := by
      by_contra h
      exact (hneg z (hya.trans_le hyz) hzb h).ne hX0
    exact ⟨hzc, hcrit z hzc (hya.trans_le hyz) hzb⟩
  obtain ⟨p, hpC, hp⟩ := exists_tendsto_atTop_of_setOf_mapClusterPt_subset hS hu huS hfin hsub
  refine mem_iUnion₂.2 ⟨p, hpC, Flow.mem_unstableSet.2 ?_, hya⟩
  simpa only [Function.comp_def, neg_neg] using hp.comp tendsto_neg_atBot_atTop

section Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M]
  {n : ℕ∞} [IsManifold I n M] [IsManifold I 1 M] {Y : (x : M) → TangentSpace I x}

/-- **Compressing a forward invariant set towards its ω-limit set.** Let `Y` be a complete `Cⁿ`
vector field, `1 ≤ n`, with flow `Φ`, let `S` be a compact set with `Φ t` mapping `S` into itself
for `t ≥ 0`, and let `U` be an open set containing the ω-limit set `ω atTop Φ S`. Then there is a
`Cⁿ` diffeotopy that fixes every zero of `Y` at all times and whose final diffeomorphism maps `S`
into `U`. -/
theorem exists_diffeotopy_mapsTo_of_omegaLimit_subset (hn : 1 ≤ n)
    (hY : ContMDiff I I.tangent n (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hc : IsCompleteVectorField Y) {S : Set M} (hS : IsCompact S)
    (hmaps : ∀ t, 0 ≤ t → MapsTo (globalFlow Y (hY.of_le (mod_cast hn)) hc t) S S)
    {U : Set M} (hU : IsOpen U)
    (hωU : ω atTop (globalFlow Y (hY.of_le (mod_cast hn)) hc) S ⊆ U) :
    ∃ Φ : Diffeotopy I n M, (∀ t, ∀ x, Y x = 0 → Φ (t, x) = x) ∧ MapsTo Φ.final S U := by
  -- Late time maps of the flow carry `S` into `U`; take one of them.
  obtain ⟨T, hT⟩ := (eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
    atTop _ S hS ((eventually_ge_atTop 0).mono hmaps) hU hωU).exists
  refine ⟨globalFlowDiffeotopy hn hY hc T,
    fun t x hx ↦ globalFlowDiffeotopy_apply_of_eq_zero hn hY hc T hx t, fun x hx ↦ ?_⟩
  rw [Diffeotopy.final_apply, globalFlowDiffeotopy_apply, Set.Icc.coe_one, mul_one,
    ← globalFlow_apply (hY.of_le (mod_cast hn)) hc]
  exact hT hx

end Diffeotopy

section Cutoff

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M]
  [IsManifold I ∞ M] {X : (x : M) → TangentSpace I x} {g : M → ℝ}

/-- **Pushing a sublevel down past one critical level, fixing a neighbourhood of the sublevel
below.** Let `X` be a smooth vector field vanishing outside a compact set, with flow `Ψ`, and `g`
a smooth function with `dg(X) ≤ 0`, whose sublevel `{g ≤ b}` is compact. Let `a < b`, and suppose
that `dg(X) < 0` at the regular points `x` with `a < g x ≤ b`, and that the critical points there
lie on one level `v`, whose critical points are finitely many. Let `U` be an open set containing
`{g ≤ a}` and, for each critical point `p` of level `v`, the part above `a` of the unstable set of
`p` for `Ψ`. Then there is a smooth diffeotopy that fixes every point of some neighbourhood of
`{g ≤ a}` at all times and whose final diffeomorphism carries `{g ≤ b}` into `U`. -/
theorem exists_diffeotopy_mapsTo_of_unstableSet_subset
    (hX : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hXc : IsCompleteVectorField X)
    (hXs : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)))
    {C : Set M} (hC : IsCompact C) (hXC : ∀ x ∉ C, X x = 0)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hgX : ∀ x, mvfderiv I g x (X x) ≤ 0)
    {a v b : ℝ} (hab : a < b) (hS : IsCompact (g ⁻¹' Iic b))
    (hneg : ∀ x, a < g x → g x ≤ b → x ∉ criticalPoints I g → mvfderiv I g x (X x) < 0)
    (hcrit : ∀ x ∈ criticalPoints I g, a < g x → g x ≤ b → g x = v)
    (hfin : (criticalPoints I g ∩ g ⁻¹' {v}).Finite) {U : Set M} (hU : IsOpen U)
    (hsub : {x | g x ≤ a} ⊆ U)
    (hunst : ∀ p ∈ criticalPoints I g ∩ g ⁻¹' {v},
      Flow.unstableSet (globalFlow X hX hXc) p ∩ {x | a < g x} ⊆ U) :
    ∃ Φ : Diffeotopy I ∞ M, (∃ V ∈ 𝓝ˢ {x | g x ≤ a}, ∀ t, ∀ x ∈ V, Φ (t, x) = x) ∧
      MapsTo Φ.final {x | g x ≤ b} U := by
  have hgd : MDifferentiable I 𝓘(ℝ) g := hg.mdifferentiable (by simp)
  -- A level `a + ε` with `{g ≤ a + ε} ⊆ U`, and the cut-off field `Y`, zero below
  -- `c = a + ε / 3` and equal to `X` above `d = a + 2 ε / 3`.
  obtain ⟨ε, hε, -, hεU⟩ := exists_pos_sublevel_subset_of_isCompact_preimage_Icc
    hg.continuous hab (hS.of_isClosed_subset (isClosed_Icc.preimage hg.continuous)
      fun x hx ↦ hx.2) (hU.mem_nhdsSet.2 hsub)
  set c := a + ε / 3 with hc
  set d := a + 2 * ε / 3 with hd
  obtain ⟨Y, hYs, hY0, hYX, hYr⟩ := exists_cutoff_vectorField hg hXs (by linarith : c < d)
  have hY1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) :=
    hYs.of_le (by simp)
  have hYc := isCompleteVectorField_of_isCompact_of_eq_zero_off hY1 hC fun x hx ↦ by
    obtain ⟨r, -, hr⟩ := hYr x
    rw [hr, hXC x hx, smul_zero]
  have hgY (x : M) : mvfderiv I g x (Y x) ≤ 0 := by
    obtain ⟨r, hr, hYx⟩ := hYr x
    rw [hYx, map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hr.1 (hgX x)
  -- The sublevel `{g ≤ b}` is forward invariant, and its ω-limit set lies in `U`.
  have hmaps (t : ℝ) (ht : 0 ≤ t) := mapsTo_globalFlow_preimage_Iic hY1 hYc hgd hgY b ht
  have hω := omegaLimit_globalFlow_subset_union_unstableSet hX hXc hY1 hYc hgd hgX hgY
    (fun x hx ↦ hYX x hx.le) (fun x hx ↦ hneg x (by linarith))
    (fun x hx hdx ↦ hcrit x hx (by linarith)) hfin hS hmaps subset_rfl
  have hωU : ω atTop (globalFlow Y hY1 hYc) (g ⁻¹' Iic b) ⊆ U := by
    intro y hy
    rcases hω hy with hyd | hyc
    · exact hεU (show g y ≤ a + ε by linarith [show g y ≤ d from hyd])
    · obtain ⟨p, hp, hyu, hyd⟩ := mem_iUnion₂.1 hyc
      exact hunst p hp ⟨hyu, (show d < g y from hyd).trans' (by linarith)⟩
  -- The diffeotopy fixes the zeros of `Y`, among them the points below `c`.
  obtain ⟨Φ, hΦ0, hΦS⟩ :=
    exists_diffeotopy_mapsTo_of_omegaLimit_subset (by simp) hYs hYc hS hmaps hU hωU
  exact ⟨Φ, ⟨{x | g x < c}, (isOpen_lt hg.continuous continuous_const).mem_nhdsSet.2
    fun x hx ↦ (show g x ≤ a from hx).trans_lt (by linarith),
    fun t x hx ↦ hΦ0 t x (hY0 x (show g x < c from hx).le)⟩, hΦS⟩

end Cutoff

section BandCore

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : M → ℝ}

/-- **Band cores across one critical level, on a manifold modelled on `E`.** Let `g` be a proper
Morse function, bounded below, on a manifold modelled on `E` with the model `𝓘(ℝ, E)`, and let
`a₀ < a < v < b` be levels such that every critical point of `g` in `g⁻¹[a₀, b]` lies on the
level `v` and has Morse index less than `dim E`. Then `g` has a band core for the levels `a₀`,
`a`, `b`. -/
private theorem IsMorse.exists_bandCore_modelSpace (hg : IsMorse 𝓘(ℝ, E) g)
    (hp : IsProperMap g) (hbdd : BddBelow (range g))
    {a₀ a v b : ℝ} (ha₀ : a₀ < a) (ha : a < v) (hb : v < b)
    (hcrit : ∀ x ∈ criticalPoints 𝓘(ℝ, E) g, a₀ ≤ g x → g x ≤ b →
      g x = v ∧ manifoldMorseIndex 𝓘(ℝ, E) g x < Module.finrank ℝ E) :
    Nonempty (SymplecticGeometry.BandCore 𝓘(ℝ, E) g a₀ a b) := by
  have hgs := hg.contMDiff
  have hcompact (c d : ℝ) : IsCompact (g ⁻¹' Icc c d) := hp.isCompact_preimage isCompact_Icc
  -- The field `X`: a compactly supported pseudo-gradient on the band `g⁻¹[a₀, b]`.
  obtain ⟨X, hXs, ⟨C, hC, hXC⟩, hgX, hneg, hchart⟩ :=
    (hcompact a₀ b).exists_contMDiff_pseudoGradient_eq_zero_off hgs
      fun x _ hx ↦ hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
  have hX1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hXs.of_le (by simp)
  have hXc := isCompleteVectorField_of_isCompact_of_eq_zero_off hX1 hC hXC
  -- At the regular points of the band, `g` strictly decreases along `X`.
  have hneg' (y : M) (h₀ : a₀ ≤ g y) (hb' : g y ≤ b) (hy : y ∉ criticalPoints 𝓘(ℝ, E) g) :
      mvfderiv 𝓘(ℝ, E) g y (X y) < 0 :=
    hneg y ⟨h₀, hb'⟩ fun h ↦ hy (mem_criticalPoints_iff_mfderiv_eq_zero.2 h)
  -- The critical points of the level `v`, finitely many.
  set P := criticalPoints 𝓘(ℝ, E) g ∩ g ⁻¹' {v}
  have hP : P.Finite := (hg.finite_criticalPoints_inter (hcompact v v)).subset
    (inter_subset_inter_right _ fun x (hx : g x = v) ↦ ⟨hx.ge, hx.le⟩)
  have hPv (p : P) : g p = v := p.property.2
  -- The cube at each of them.
  have hcube (p : P) : ∃ χ : (Fin (manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) ×
        (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) → M,
      Manifold.IsSmoothEmbedding 𝓘(ℝ, (Fin (manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ) ×
        (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) g p) → ℝ)) 𝓘(ℝ, E) ∞ χ ∧
      IsOpen (range χ) ∧
      MapsTo χ (Metric.closedBall 0 1 ×ˢ {0})
        (Flow.unstableSet (globalFlow X hX1 hXc) p ∩ {x | a₀ < g x}) ∧
      MapsTo χ (Metric.sphere 0 1 ×ˢ {0}) {x | g x < a} ∧
      Flow.unstableSet (globalFlow X hX1 hXc) p ∩ {x | a ≤ g x} ⊆
        χ '' (Metric.closedBall 0 1 ×ˢ {0}) := by
    obtain ⟨φ, hφ⟩ := hchart p ⟨by linarith [hPv p], by linarith [hPv p]⟩
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property.1)
    obtain ⟨χ, h₁, h₂, -, h₃, h₄, h₅⟩ := MorseChart.exists_cubeChart_unstableSet hX1 hXc hXs φ hφ
      hgs hgX ha₀ (by rw [hPv p]; exact ha) (fun b' _ ↦ hcompact a₀ b')
      fun y hy hyp ↦ hneg' y hy.le (by linarith [hPv p]) fun hc ↦ by
        linarith [(hcrit y hc hy.le (by linarith [hPv p])).1, hPv p]
    exact ⟨χ, h₁, h₂, h₃, h₄, h₅⟩
  -- The cubes are indexed by `Fin n`, since the index type of a band core lives in `Type`.
  let := hP.fintype
  set e := Fintype.equivFin P
  choose χ hχe hχo hχc hχs hχu using fun i ↦ hcube (e.symm i)
  refine ⟨{ ι := Fin (Fintype.card P)
            dim := fun i ↦ manifoldMorseIndex 𝓘(ℝ, E) g (e.symm i)
            dim_lt := fun i ↦ (hcrit _ (e.symm i).property.1 (by linarith [hPv (e.symm i)])
              (by linarith [hPv (e.symm i)])).2
            chart := χ
            isSmoothEmbedding_chart := hχe
            isOpen_range_chart := hχo
            mapsTo_cube := fun i ↦ (hχc i).mono_right inter_subset_right
            mapsTo_sphere := hχs
            pairwise_disjoint := fun i j hij ↦
              (Flow.disjoint_unstableSet (Subtype.coe_injective.ne (e.symm.injective.ne hij))).mono
                ((hχc i).mono_right inter_subset_left).image_subset
                ((hχc j).mono_right inter_subset_left).image_subset
            exists_compression := fun U hU hsub ↦ ?_ }⟩
  -- The compression: the diffeotopy of `exists_diffeotopy_mapsTo_of_unstableSet_subset`, whose
  -- hypothesis on the unstable sets holds since their parts above `a` lie in the cubes.
  obtain ⟨Φ, hΦV, hΦ⟩ := exists_diffeotopy_mapsTo_of_unstableSet_subset hX1 hXc hXs hC
    hXC hgs hgX (ha.trans hb) (hp.isCompact_preimage_Iic hbdd b)
    (fun x hx hxb ↦ hneg' x (by linarith) hxb)
    (fun x hx hax hxb ↦ (hcrit x hx (by linarith) hxb).1) hP hU (subset_union_left.trans hsub)
    fun p hpP y hy ↦ by
      have hyu : y ∈ Flow.unstableSet (globalFlow X hX1 hXc) (e.symm (e ⟨p, hpP⟩)) := by
        rw [e.symm_apply_apply]
        exact hy.1
      exact hsub (Or.inr (mem_iUnion.2 ⟨e ⟨p, hpP⟩, hχu _ ⟨hyu, (show a < g y from hy.2).le⟩⟩))
  exact Φ.exists_smoothIsotopy_id_of_mapsTo_final hΦV hΦ

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : M → ℝ}

/-- **Band cores across one critical level.** Let `g` be a proper Morse function, bounded below,
on a boundaryless manifold, and let `a₀ < a < v < b` be levels such that every critical point of
`g` in `g⁻¹[a₀, b]` lies on the level `v` and has Morse index less than `dim E`. Then `g` has a
band core for the levels `a₀`, `a`, `b`. -/
theorem IsMorse.exists_bandCore (hg : IsMorse I g) (hp : IsProperMap g)
    (hbdd : BddBelow (range g))
    {a₀ a v b : ℝ} (ha₀ : a₀ < a) (ha : a < v) (hb : v < b)
    (hcrit : ∀ x ∈ criticalPoints I g, a₀ ≤ g x → g x ≤ b →
      g x = v ∧ manifoldMorseIndex I g x < Module.finrank ℝ E) :
    Nonempty (SymplecticGeometry.BandCore I g a₀ a b) := by
  -- Work on the copy of `M` modelled on `E` itself, with the function `g' = g ∘ e.symm`.
  set e := BoundarylessModel.homeomorph I M
  set g' : BoundarylessModel I M → ℝ := g ∘ e.symm with hg'
  obtain ⟨c⟩ := IsMorse.exists_bandCore_modelSpace ((BoundarylessModel.isMorse_iff I g).2 hg)
    (hp.comp e.symm.isProperMap) (hbdd.mono (range_comp_subset_range _ _)) ha₀ ha hb
    fun x hx h₀ hb' ↦ by
      rw [BoundarylessModel.manifoldMorseIndex_eq]
      rw [BoundarylessModel.criticalPoints_eq] at hx
      exact hcrit _ hx h₀ hb'
  -- Pull the band core back along the diffeomorphism `M ≃ BoundarylessModel I M`.
  have hcomp : g' ∘ BoundarylessModel.diffeomorph I ∞ = g := by
    rw [BoundarylessModel.coe_diffeomorph, hg', Function.comp_assoc, e.symm_comp_self,
      Function.comp_id]
  exact ⟨hcomp ▸ c.ofDiffeomorph (BoundarylessModel.diffeomorph I ∞)⟩

end BandCore

end TauCeti
