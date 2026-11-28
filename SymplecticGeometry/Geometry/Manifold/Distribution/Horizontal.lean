/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Horizontal
import TauCeti.Geometry.Manifold.MFDeriv.Translation

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

For a map `f` on a normed space, the derivative `df_z w` is the velocity at `0` of the line
`r ↦ f (z + r • w)`. So it lies in `D (f z)` as soon as that line is horizontal
(`TauCeti.IsHorizontalMap.mfderiv_apply_mem_of_line`); no differentiability of `f` is needed,
since its derivative is zero where `f` is not differentiable. A translate `w ↦ f (w + c)` of a
horizontal map on a real normed space is horizontal (`TauCeti.IsHorizontalMap.comp_add_right`),
since its derivatives are those of `f` (Tau Ceti's `TauCeti.mfderiv_comp_add_right`).
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

section Line

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- If the line `r ↦ f (z + r • w)` of a map `f` on a normed space is horizontal for `D`, then
the derivative of `f` at `z` in the direction `w` lies in `D (f z)`. -/
theorem IsHorizontalMap.mfderiv_apply_mem_of_line {f : V → M} {z w : V}
    (hf : IsHorizontalMap 𝓘(𝕜, 𝕜) D fun r : 𝕜 ↦ f (z + r • w)) :
    mfderiv 𝓘(𝕜, V) I f z w ∈ D (f z) := by
  by_cases hd : MDifferentiableAt 𝓘(𝕜, V) I f z
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    exact (D _).zero_mem
  have hc : HasMFDerivAt 𝓘(𝕜, 𝕜) 𝓘(𝕜, V) (fun r : 𝕜 ↦ z + r • w) 0
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) :=
    (((hasFDerivAt_id (0 : 𝕜)).smul_const w).const_add z).hasMFDerivAt
  have h0 : z + (0 : 𝕜) • w = z := by simp
  have hw : mfderiv 𝓘(𝕜, 𝕜) 𝓘(𝕜, V) (fun r : 𝕜 ↦ z + r • w) 0 (1 : 𝕜) = w := by
    rw [hc.mfderiv]
    -- Read the tangent spaces of the model spaces as the model spaces.
    change ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w) (1 : 𝕜) = w
    simp
  have key := mfderiv_comp_apply_of_eq (0 : 𝕜) hd hc.mdifferentiableAt h0 (1 : 𝕜)
  rw [hw] at key
  have h := hf.mfderiv_mem 0 (1 : 𝕜)
  rw [h0] at h
  rw [← key]
  exact h

end Line

section Translate

variable {M : Type*} [TopologicalSpace M] {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [ChartedSpace H M]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A translate `w ↦ f (w + c)` of a horizontal map `f` on a real normed space is horizontal. -/
theorem IsHorizontalMap.comp_add_right {f : V → M} (hf : IsHorizontalMap 𝓘(ℝ, V) D f) (c : V) :
    IsHorizontalMap 𝓘(ℝ, V) D fun w ↦ f (w + c) :=
  isHorizontalMap_iff.2 fun y v ↦ by
    rw [mfderiv_comp_add_right]
    exact hf.mfderiv_mem (y + c) v

end Translate

end TauCeti

end
