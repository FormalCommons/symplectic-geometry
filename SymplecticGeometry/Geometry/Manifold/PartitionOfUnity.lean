/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Topology.Algebra.Support

/-!
# Smooth cutoff functions near a closed set, and smooth majorants

## Main results

* `IsClosed.exists_contMDiffMap_tsupport_subset_eventually_eq_one`: a closed set `A` inside an
  open set `U` of a Hausdorff σ-compact manifold modelled on a finite-dimensional space has a
  smooth cutoff equal to `1` on a neighbourhood of `A` with topological support in `U`. It is
  Mathlib's smooth Urysohn lemma `exists_contMDiffMap_zero_one_nhds_of_isClosed`, applied to `Uᶜ`
  and `A`; Mathlib's `exists_contMDiffMap_one_nhds_of_subset_interior` bounds only the support,
  and Tau Ceti's `IsClosed.exists_contMDiff_tsupport_subset_eq_one_iff` gives the value `1` only
  on `A`.
* `exists_contMDiffMap_forall_lt`: a real function on a Hausdorff σ-compact manifold modelled on
  a finite-dimensional space that is bounded above near each point lies strictly below a smooth
  function. It applies Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local_const` to the
  convex sets `Ioi (f x)`, as Tau Ceti's `CompactExhaustion.exists_contMDiffMap_isProperMap`
  applies it to its own convex sets.
-/

public section

open Set Topology
open scoped Manifold ContDiff

section Cutoff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

variable (I) in
/-- **A smooth cutoff near a closed set.** If `A` is a closed subset of an open set `U` of a
Hausdorff σ-compact manifold modelled on a finite-dimensional real space, there is a smooth
function `θ : M → [0, 1]` with topological support in `U` that equals `1` on a neighbourhood
of `A`. -/
theorem IsClosed.exists_contMDiffMap_tsupport_subset_eventually_eq_one {A U : Set M}
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ θ : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, tsupport θ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ A, θ x = 1) ∧
      ∀ x, θ x ∈ Icc 0 1 := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤)
    hU.isClosed_compl hA (disjoint_compl_left_iff_subset.2 hAU)
  obtain ⟨O, hO, hUO, hθO⟩ := eventually_nhdsSet_iff_exists.1 hθ0
  exact ⟨θ, (TauCeti.tsupport_subset_of_forall_notMem_eq_zero (fun x hx ↦ hθO x (not_not.1 hx))
    hO.isClosed_compl).trans (compl_subset_comm.1 hUO), hθ1, hθ⟩

variable (I) in
/-- **A smooth majorant.** A real function on a Hausdorff σ-compact manifold modelled on a
finite-dimensional real space that is bounded above on a neighbourhood of each point lies
strictly below a smooth function. -/
theorem exists_contMDiffMap_forall_lt {f : M → ℝ} (hf : ∀ x, ∃ U ∈ 𝓝 x, BddAbove (f '' U)) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, ∀ x, f x < g x :=
  exists_contMDiffMap_forall_mem_convex_of_local_const I (n := ⊤) (t := fun x ↦ Ioi (f x))
    (fun _ ↦ convex_Ioi _) fun x ↦ by
      obtain ⟨U, hU, c, hc⟩ := hf x
      exact ⟨c + 1, Filter.mem_of_superset hU fun y hy ↦
        (hc (mem_image_of_mem f hy)).trans_lt (lt_add_one c)⟩

end Cutoff
