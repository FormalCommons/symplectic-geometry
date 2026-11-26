/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Order.Interval.Set.OrdConnected
public import TauCeti.Geometry.Manifold.Connected
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Topology.Order.IntermediateValue
import SymplecticGeometry.Geometry.Manifold.LocallyFlat.LineComplement
import SymplecticGeometry.Topology.Connected.Clopen

/-!
# Removing arcs and a discrete set from a connected open set of a manifold

Let `M` be a boundaryless manifold whose model space `E` has real dimension greater than one.
This file shows that removing from a preconnected open set `U ⊆ M` a closed discrete set `s`
and finitely many pairwise disjoint arcs, each relatively closed in `U \ s` and with a free end,
leaves a preconnected set. An arc here is the image `f '' J` of an order-connected `J ⊆ ℝ`
under a smooth embedding `f : ℝ → M`, and its free end is `f b` for a greatest or least
element `b` of `J`.

The points of `s` are removed first, by Tau Ceti's
`TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`, read in the model
space `E` through the charts composed with `I`. The arcs are then removed one at a time by
`IsPreconnected.sdiff_of_forall_exists_mem_nhds`: near an arc point, a small neighbourhood
minus the arc consists of at most two preconnected pieces, each with the arc in its closure,
and near the free end it is preconnected
(`Manifold.IsSmoothEmbedding.exists_isPreconnected_diff_image` and
`Manifold.IsSmoothEmbedding.exists_isPreconnected_diff_image_of_mem_bounds`). Relative
closedness keeps the set left open after each step.

## Main results

* `isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_boundaryless`: Tau Ceti's discrete-set lemma
  for a manifold modelled on a boundaryless model with corners.
* `Manifold.IsSmoothEmbedding.isPreconnected_sdiff_image`: removing one arc with a free end from
  a preconnected set that contains it and is open leaves a preconnected set.
* `isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank`: the statement above, for a closed
  discrete set and finitely many arcs.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 5, for slice charts of embedded submanifolds.
-/

public section

open Function Set Topology Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

include I in
/-- **Removing a closed discrete set from a preconnected open set of a manifold** modelled on a
boundaryless model with corners `I : ModelWithCorners ℝ E H`, with `E` of real dimension greater
than one, leaves it preconnected. -/
theorem isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_boundaryless (hE : 1 < Module.rank ℝ E)
    {U s : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) (hs : IsClosed s)
    (hd : IsDiscrete s) : IsPreconnected (U \ s) :=
  -- Composing the charts with the homeomorphism `I : H ≃ₜ E` makes `M` a charted space over `E`.
  letI : ChartedSpace E H := I.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  letI : ChartedSpace E M := ChartedSpace.comp E H M
  TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hE hU hUc hs hd

variable {I} {n : WithTop ℕ∞}

namespace Manifold.IsSmoothEmbedding

/-- **Removing an arc with a free end keeps an open set preconnected.** Let `f : ℝ → M` be a
`C^n` embedding into a boundaryless manifold whose model space has rank greater than one, `J` an
order-connected subset of `ℝ` and `b ∈ J` an upper or a lower bound of `J`. If `U` is open and
preconnected and contains `f '' J`, then `U \ f '' J` is preconnected. -/
theorem isPreconnected_sdiff_image {f : ℝ → M} (h : IsSmoothEmbedding 𝓘(ℝ) I n f)
    (hE : 1 < Module.rank ℝ E) {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U)
    {J : Set ℝ} (hJ : J.OrdConnected) {b : ℝ} (hb : b ∈ J)
    (hbJ : b ∈ upperBounds J ∨ b ∈ lowerBounds J) (hJU : f '' J ⊆ U) :
    IsPreconnected (U \ f '' J) := by
  refine hUc.sdiff_of_forall_exists_mem_nhds
    (hJ.isPreconnected.image _ h.isEmbedding.continuous.continuousOn) hJU (mem_image_of_mem f hb)
    (h.exists_isPreconnected_diff_image_of_mem_bounds hE hbJ
      (hU.mem_nhds (hJU (mem_image_of_mem f hb)))) ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨V, hV, hVU, P, Q, hP, hQ, hPQ, hcl⟩ :=
    h.exists_isPreconnected_diff_image hE J t (hU.mem_nhds (hJU (mem_image_of_mem f ht)))
  exact ⟨V, hV, hVU, P, Q, hPQ, hP, hQ, hcl⟩

end Manifold.IsSmoothEmbedding

/-- **Removing finitely many arcs with free ends and a closed discrete set keeps an open set
preconnected.** Let `M` be a boundaryless manifold whose model space has rank greater than one,
`U ⊆ M` open and preconnected, and `s` closed and discrete. For `i` in a finite type, let
`f i : ℝ → M` be a `C^n` embedding and `J i ⊆ ℝ` order-connected with a greatest or a least
element. Suppose that the arcs `f i '' J i` lie in `U \ s`, are pairwise disjoint, and are
closed in `U \ s`. Then `U \ (s ∪ ⋃ i, f i '' J i)` is preconnected. -/
theorem isPreconnected_sdiff_union_iUnion_image_of_one_lt_rank {ι : Type*} [Finite ι]
    (hE : 1 < Module.rank ℝ E) {U s : Set M} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hs : IsClosed s) (hd : IsDiscrete s) {f : ι → ℝ → M}
    (hf : ∀ i, IsSmoothEmbedding 𝓘(ℝ) I n (f i)) {J : ι → Set ℝ} (hJ : ∀ i, (J i).OrdConnected)
    (hb : ∀ i, ∃ b, IsGreatest (J i) b ∨ IsLeast (J i) b) (hJU : ∀ i, f i '' J i ⊆ U \ s)
    (hdisj : Pairwise (Disjoint on fun i ↦ f i '' J i))
    (hcl : ∀ i, closure (f i '' J i) ∩ (U \ s) ⊆ f i '' J i) :
    IsPreconnected (U \ (s ∪ ⋃ i, f i '' J i)) := by
  classical
  have := Fintype.ofFinite ι
  -- Remove the arcs indexed by a finset one at a time; the set left stays open.
  suffices key : ∀ T : Finset ι, IsOpen (U \ (s ∪ ⋃ i ∈ T, f i '' J i)) ∧
      IsPreconnected (U \ (s ∪ ⋃ i ∈ T, f i '' J i)) by
    simpa using (key Finset.univ).2
  intro T
  induction T using Finset.induction_on with
  | empty =>
    simpa using ⟨hU.sdiff hs, isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_boundaryless I hE
      hU hUc hs hd⟩
  | @insert j T hjT ih =>
    obtain ⟨hVo, hVc⟩ := ih
    have heq : U \ (s ∪ ⋃ i ∈ insert j T, f i '' J i) =
        (U \ (s ∪ ⋃ i ∈ T, f i '' J i)) \ f j '' J j := by
      ext x
      simp only [Finset.set_biUnion_insert, mem_sdiff, mem_union]
      tauto
    have hjV : f j '' J j ⊆ U \ (s ∪ ⋃ i ∈ T, f i '' J i) := fun x hx ↦
      ⟨(hJU j hx).1, fun h ↦ h.elim (hJU j hx).2 fun h ↦ by
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 h
        exact disjoint_left.1 (hdisj (i := i) (j := j) fun hij ↦ hjT (hij ▸ hi)) hxi hx⟩
    -- The arc is closed in the set left, so removing it leaves an open set.
    have hcl' : (U \ (s ∪ ⋃ i ∈ T, f i '' J i)) \ f j '' J j =
        (U \ (s ∪ ⋃ i ∈ T, f i '' J i)) \ closure (f j '' J j) := by
      refine Subset.antisymm (fun x hx ↦ ⟨hx.1, fun hxc ↦ hx.2 (hcl j ⟨hxc, ?_⟩)⟩)
        (sdiff_subset_sdiff_right subset_closure)
      exact ⟨hx.1.1, fun hxs ↦ hx.1.2 (Or.inl hxs)⟩
    obtain ⟨b, hbJ, hbb⟩ : ∃ b ∈ J j, b ∈ upperBounds (J j) ∨ b ∈ lowerBounds (J j) := by
      obtain ⟨b, hb | hb⟩ := hb j
      exacts [⟨b, hb.1, .inl hb.2⟩, ⟨b, hb.1, .inr hb.2⟩]
    rw [heq]
    exact ⟨hcl' ▸ hVo.sdiff isClosed_closure,
      (hf j).isPreconnected_sdiff_image hE hVo hVc (hJ j) hbJ hbb hjV⟩

end
