/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Horizontal

/-!
# Horizontality is a local property

Tau Ceti's `TauCeti.IsHorizontalMap J D f` asks that the tangent images of `f` lie in the
distribution `D`. Since a tangent map at a point depends only on the germ of `f` there, a map that
near every point agrees with some horizontal map is horizontal
(`TauCeti.IsHorizontalMap.of_forall_eventuallyEq`). In particular a map that follows one
horizontal map on a set `s` and another off it is horizontal when the two agree near the frontier
of `s` (`TauCeti.IsHorizontalMap.piecewise`, whose proof follows that of Mathlib's
`ContMDiff.piecewise`). This is how curves glued from horizontal pieces are seen to be horizontal.
The file also notes that a constant map is horizontal (`TauCeti.isHorizontalMap_const`), since
its tangent maps vanish.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {f : N → M}

/-- A constant map is horizontal for every distribution. -/
theorem isHorizontalMap_const (x : M) : IsHorizontalMap J D (fun _ : N ↦ x) :=
  isHorizontalMap_iff.2 fun y v ↦ by
    rw [mfderiv_const]
    exact (D x).zero_mem

/-- A map that agrees near each point with some horizontal map is horizontal. -/
theorem IsHorizontalMap.of_forall_eventuallyEq
    (h : ∀ y, ∃ g : N → M, IsHorizontalMap J D g ∧ f =ᶠ[𝓝 y] g) : IsHorizontalMap J D f := by
  refine isHorizontalMap_iff.2 fun y v ↦ ?_
  obtain ⟨g, hg, hfg⟩ := h y
  rw [hfg.mfderiv_eq, hfg.eq_of_nhds]
  exact hg.mfderiv_mem y v

/-- The map that follows a horizontal map `f` on a set `s` and a horizontal map `g` off it is
horizontal, if `f` and `g` agree near each point of the frontier of `s`. -/
theorem IsHorizontalMap.piecewise {g : N → M} {s : Set N} [DecidablePred (· ∈ s)]
    (hf : IsHorizontalMap J D f) (hg : IsHorizontalMap J D g)
    (hfg : ∀ y ∈ frontier s, f =ᶠ[𝓝 y] g) : IsHorizontalMap J D (s.piecewise f g) := by
  refine of_forall_eventuallyEq fun y ↦ ?_
  by_cases hy : y ∈ interior s
  · refine ⟨f, hf, ?_⟩
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    exact Set.piecewise_eq_of_mem _ _ _ (interior_subset hz)
  by_cases hy' : y ∈ closure s
  · refine ⟨f, hf, ?_⟩
    filter_upwards [hfg y ⟨hy', hy⟩] with z hz
    by_cases hzs : z ∈ s <;> simp [Set.piecewise, hzs, hz]
  · refine ⟨g, hg, ?_⟩
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy'] with z hz
    exact Set.piecewise_eq_of_notMem _ _ _ fun hzs ↦ hz (subset_closure hzs)

end TauCeti

end
