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
import TauCeti.Geometry.Manifold.Flow.Locality
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
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
    (isMIntegralCurve_globalFlow hY hc x).antitone_comp (fun _ ↦ hg _) (fun _ ↦ hgY _) ht
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
    (isMIntegralCurve_globalFlow hY hc y).antitone_comp (fun _ ↦ hg _) fun _ ↦ hgY _
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
    (isMIntegralCurve_globalFlow hY hc y).antitone_comp (fun _ ↦ hg _) fun _ ↦ hgY _
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
    (isMIntegralCurve_globalFlow hY hYc x).antitone_comp (fun _ ↦ hg _) fun _ ↦ hgY _
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
    (Ψ.continuous continuous_neg continuous_const).continuousOn
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

end TauCeti
