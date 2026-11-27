/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Separation.Hausdorff
import TauCeti.Dynamics.Flow.OmegaLimit

/-!
# Backward orbits of points of an ω-limit set

Let `φ` be a flow of `ℝ` on a Hausdorff space, `S` a compact set that `φ t` maps into itself for
`t ≥ 0`, and `g` a continuous function antitone along orbits. A point `y` of the ω-limit set
`ω atTop φ S` has its whole orbit in `S`, so its backward orbit has a cluster point `z ∈ S` at
`-∞`. The function `g` is constant along the orbit of `z`, and `g y ≤ g z`
(`Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit`).

This is the topological half of the compression of a sublevel `{g ≤ b}` along a descending flow:
for the flow of a field `Y` with `dg(Y) ≤ 0`, constancy of `g` along the orbit of `z` forces
`dg(Y) = 0` at `z`, so every point of the ω-limit set lies on a backward orbit that comes from the
zeros of `dg(Y)` at a level no lower than its own.

## Main results

* `Flow.isLUB_of_mapClusterPt_atBot_of_antitone`: at a cluster point at `-∞` of an orbit, a
  continuous function antitone along the orbit takes the supremum of its values along it.
* `Flow.apply_flow_eq_of_mapClusterPt_atBot_of_antitone`: such a function is constant along the
  orbit of the cluster point.
* `Flow.exists_mapClusterPt_atBot_of_mem_omegaLimit`: the backward orbit of a point of the
  ω-limit set of a compact forward invariant set clusters at a point of that set, along whose
  orbit the function is constant at a value no lower than at the point.

The first two are the backward-time counterparts of Tau Ceti's
`Flow.isGLB_of_mapClusterPt_of_antitone` and `Flow.apply_flow_eq_of_mapClusterPt_of_antitone`
(`TauCeti/Dynamics/Flow/Lyapunov.lean`), with the same proofs, and `Flow.mapClusterPt_atBot_flow`
is that of `Flow.mapClusterPt_atTop_flow` (`TauCeti/Topology/OmegaLimit.lean`).

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Filter Set Topology
open scoped omegaLimit

namespace Flow

variable {α : Type*} [TopologicalSpace α] {φ : Flow ℝ α} {g : α → ℝ} {x y : α}

/-- **The α-limit set of an orbit of a flow is invariant.** If `z` is a cluster point at `-∞` of
the orbit `t ↦ φ t y` of a flow of `ℝ`, so is `φ s z` for every time `s`. -/
theorem mapClusterPt_atBot_flow {z : α} (hz : MapClusterPt z atBot fun t ↦ φ t y) (s : ℝ) :
    MapClusterPt (φ s z) atBot fun t ↦ φ t y := by
  have hω := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := φ) y z).2 hz
  exact (mem_omegaLimit_singleton_iff_mapClusterPt (f := atBot) (ϕ := φ) y _).1
    (isInvariant_omegaLimit atBot φ {y} (fun t ↦ tendsto_atBot_add_const_left _ t tendsto_id) s hω)

/-- **A Lyapunov function attains its supremum along an orbit at the backward cluster points.**
If `g` is antitone along the orbit of `y` and continuous at a cluster point `x` of the backward
orbit, then `g x` is the least upper bound of the values of `g` along the orbit. -/
theorem isLUB_of_mapClusterPt_atBot_of_antitone (hanti : Antitone fun t ↦ g (φ t y))
    (hg : ContinuousAt g x) (hx : MapClusterPt x atBot fun t ↦ φ t y) :
    IsLUB (range fun t ↦ g (φ t y)) (g x) := by
  have hcl : MapClusterPt (g x) atBot fun t ↦ g (φ t y) := hx.continuousAt_comp hg
  refine ⟨?_, fun b hb ↦ ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact isClosed_Ici.mem_of_mapClusterPt hcl ((eventually_le_atBot t).mono fun s hs ↦ hanti hs)
  · exact isClosed_Iic.mem_of_mapClusterPt hcl (.of_forall fun s ↦ hb ⟨s, rfl⟩)

/-- **A Lyapunov function is constant along the orbit of a backward cluster point.** If `g` is
continuous and antitone along the orbit of `y`, it is constant along the orbit of every cluster
point `x` of the backward orbit of `y`. -/
theorem apply_flow_eq_of_mapClusterPt_atBot_of_antitone (hanti : Antitone fun t ↦ g (φ t y))
    (hg : Continuous g) (hx : MapClusterPt x atBot fun t ↦ φ t y) (t : ℝ) : g (φ t x) = g x :=
  (isLUB_of_mapClusterPt_atBot_of_antitone hanti hg.continuousAt
    (mapClusterPt_atBot_flow hx t)).unique
    (isLUB_of_mapClusterPt_atBot_of_antitone hanti hg.continuousAt hx)

/-- **Backward orbits of points of an ω-limit set.** Let `S` be a compact subset of a Hausdorff
space, mapped into itself by `φ t` for `t ≥ 0`, and `g` a continuous function antitone along the
orbit of a point `y` of the ω-limit set `ω atTop φ S`. Then the whole orbit of `y` lies in `S`,
and its backward orbit has a cluster point `z ∈ S` at `-∞` with `g y ≤ g z`, along whose orbit
`g` is constant. -/
theorem exists_mapClusterPt_atBot_of_mem_omegaLimit [T2Space α] {S : Set α} (hS : IsCompact S)
    (hmaps : ∀ t, 0 ≤ t → MapsTo (φ t) S S) (hg : Continuous g)
    (hanti : Antitone fun t ↦ g (φ t y)) (hy : y ∈ ω atTop φ S) :
    (∀ t, φ t y ∈ S) ∧ ∃ z ∈ S, MapClusterPt z atBot (fun t ↦ φ t y) ∧ g y ≤ g z ∧
      ∀ t, g (φ t z) = g z := by
  have horb : ∀ t, φ t y ∈ S :=
    omegaLimit_subset_setOf_forall_apply_mem (fun t ↦ tendsto_atTop_add_const_left _ t tendsto_id)
      hS.isClosed ((eventually_ge_atTop 0).mono hmaps) hy
  obtain ⟨z, hzS, hz⟩ := hS.exists_mapClusterPt_of_frequently (l := atBot)
    (.of_forall fun t ↦ horb t)
  have hlub := isLUB_of_mapClusterPt_atBot_of_antitone hanti hg.continuousAt hz
  refine ⟨horb, z, hzS, hz, ?_, apply_flow_eq_of_mapClusterPt_atBot_of_antitone hanti hg hz⟩
  simpa only [map_zero_apply] using hlub.1 ⟨0, rfl⟩

end Flow
