/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
import Mathlib.Topology.Algebra.Module.PerfectSpace
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Configuration
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Topology.Perfect

/-!
# Moving a closed discrete set off a compact set

In a preconnected boundaryless manifold `N` of real dimension at least two, let `Z` be a closed
discrete subset and `K` a compact subset whose complement is nonempty. Then some diffeotopy of `N`
has a final map that sends no point of `K` into `Z`
(`TauCeti.exists_diffeotopy_apply_one_notMem`). Equivalently, the inverse of the final map carries
the finitely many points of `Z ∩ K` out of `K`, and fixes every point of `Z \ K`.

The proof picks as many distinct targets in the complement of `Z ∪ K` as `Z ∩ K` has points; they
exist since `Z` has empty interior in the perfect space `N`. The complement of `Z \ K` is open and
still preconnected, and Tau Ceti's `exists_diffeotopy_final_comp_eq_of_isPreconnected` gives a
diffeotopy supported there that sends the targets onto the points of `Z ∩ K`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma, of
  which the result is a consequence.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace E N] [T2Space N] {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n N]
  {m : ℕ∞}

/-- A closed discrete subset `Z` of a preconnected boundaryless manifold of dimension at least two
can be moved off a compact set `K` with nonempty complement: the final map of some `C^m`
diffeotopy sends no point of `K` into `Z`. The regularity is `C^m` provided `1 ≤ m` and
`m + 1 ≤ n`. -/
theorem exists_diffeotopy_apply_one_notMem [PreconnectedSpace N]
    (hdim : 1 < Module.rank ℝ E) (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) {Z K : Set N}
    (hZ : IsClosed Z) (hZd : IsDiscrete Z) (hK : IsCompact K) (hKc : Kᶜ.Nonempty) :
    ∃ Ψ : Diffeotopy 𝓘(ℝ, E) m N, ∀ y ∈ K, Ψ (1, y) ∉ Z := by
  classical
  have : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans hdim)
  have : PerfectSpace E := perfectSpace_of_module ℝ E
  have : PerfectSpace N := ChartedSpace.perfectSpace (H := E)
  -- The points of `Z` in `K`, enumerated.
  have hA : (Z ∩ K).Finite := (hK.inter_left hZ).finite (hZd.mono inter_subset_left)
  have := hA.to_subtype
  let e := Finite.equivFin (Z ∩ K : Set N)
  -- `Z` has empty interior, so infinitely many points lie outside `Z ∪ K`: the targets.
  have hZi : Dense Zᶜ := by
    simpa [dense_iff_closure_eq, eq_univ_iff_forall, compl_eq_univ_sdiff] using
      isOpen_univ.subset_closure_sdiff_of_isDiscrete (S := Z) (by simpa using hZd)
  have hT : IsOpen (Kᶜ ∩ Zᶜ) := hK.isClosed.isOpen_compl.inter hZ.isOpen_compl
  obtain ⟨y₀, hy₀⟩ := hZi.inter_open_nonempty Kᶜ hK.isClosed.isOpen_compl hKc
  let w := (infinite_of_mem_nhds y₀ (hT.mem_nhds hy₀)).natEmbedding
  -- The points of `Z` outside `K` stay where they are; the rest of `N` is preconnected.
  have hZK : IsClosed (Z \ K) ∧ IsDiscrete (Z \ K) := isClosed_and_discrete_iff.2 fun x ↦
    (isClosed_and_discrete_iff.1 ⟨hZ, hZd⟩ x).mono_right (Filter.principal_mono.2 sdiff_subset)
  obtain ⟨Ψ, L, -, hLU, hΨL, hΨ⟩ := exists_diffeotopy_final_comp_eq_of_isPreconnected
    hdim hm hmn (isOpen_univ.sdiff hZK.1)
    (isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hdim isOpen_univ
      isPreconnected_univ hZK.1 hZK.2)
    (f := fun i : Fin (Nat.card (Z ∩ K : Set N)) ↦ (w i : N)) (g := fun i ↦ (e.symm i : N))
    (Subtype.val_injective.comp (w.injective.comp Fin.val_injective))
    (Subtype.val_injective.comp e.symm.injective)
    (fun i ↦ ⟨trivial, fun h ↦ (w i).prop.2 h.1⟩)
    (fun i ↦ ⟨trivial, fun h ↦ h.2 (e.symm i).prop.2⟩)
  refine ⟨Ψ, fun y hy hyZ ↦ ?_⟩
  by_cases hyK : Ψ (1, y) ∈ K
  · -- A point of `Z ∩ K` is the image of a target, which lies outside `K`.
    have h := congrFun hΨ (e ⟨_, hyZ, hyK⟩)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at h
    have := Ψ.final.injective (h.trans (Diffeotopy.final_apply Ψ y).symm)
    exact (w _).prop.1 (this ▸ hy)
  · -- A point of `Z` outside `K` is fixed, so it is its own preimage.
    have hfix : Ψ (1, Ψ (1, y)) = Ψ (1, y) := hΨL 1 fun h ↦ (hLU h).2 ⟨hyZ, hyK⟩
    have := Ψ.final.injective ((Ψ.final_apply _).trans (hfix.trans (Ψ.final_apply y).symm))
    rw [this] at hyK
    exact hyK hy

end TauCeti

end
