/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Topology.DiscreteSubset
import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Discrete sets and curves are null in a manifold

On a manifold whose model space `E` is finite-dimensional, Tau Ceti's `TauCeti.IsNullSet` says
that a set has measure zero in every chart. This file shows that a discrete set is null when `E`
is nontrivial, and deduces that the points of a manifold of dimension greater than one that lie
neither on a discrete set nor on countably many differentiable curves form a dense set.

## Main results

* `IsDiscrete.isNullSet`: a discrete set is null.
* `SymplecticGeometry.dense_compl_union_iUnion_range`: if `1 < finrank ℝ E`, the complement of
  the union of a discrete set and the ranges of countably many differentiable curves `ℝ → M` is
  dense.
* `SymplecticGeometry.dense_compl_iUnion_range_addCircle`: if `1 < finrank ℝ E`, the complement
  of the union of the ranges of countably many differentiable loops `AddCircle p → M` is dense.

The curves are null by Tau Ceti's `MDifferentiable.isNullSet_range_of_finrank_lt_finrank`, and
the complement of a null set is dense by `TauCeti.IsNullSet.dense_compl`.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §3, for sets of measure zero in a manifold.
-/

public section

open Set Topology Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- On a manifold whose model space is finite-dimensional and nontrivial, a discrete set is
null. -/
theorem IsDiscrete.isNullSet [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {s : Set M}
    (hs : IsDiscrete s) : TauCeti.IsNullSet I s := by
  refine TauCeti.isNullSet_iff_forall_exists_nhds.2 fun x hx ↦ ?_
  obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hs x hx
  refine ⟨u, hu.mem_nhds ?_, ?_⟩
  · exact (hus.symm.subset (mem_singleton x)).1
  · rw [inter_comm, hus]
    exact (countable_singleton x).isNullSet

namespace SymplecticGeometry

/-- On a manifold whose model space has finite dimension greater than one, the points that lie
neither on a discrete set `s` nor on the range of any of countably many differentiable curves
`f i : ℝ → M` form a dense set. -/
theorem dense_compl_union_iUnion_range [IsManifold I 1 M] (hE : 1 < Module.finrank ℝ E)
    {ι : Type*} [Countable ι] {s : Set M} (hs : IsDiscrete s) {f : ι → ℝ → M}
    (hf : ∀ i, MDifferentiable 𝓘(ℝ) I (f i)) :
    Dense (s ∪ ⋃ i, range (f i))ᶜ := by
  borelize E
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hE)
  refine TauCeti.IsNullSet.dense_compl (I := I) (hs.isNullSet.union (.iUnion fun i ↦ ?_))
  exact (hf i).isNullSet_range_of_finrank_lt_finrank (by simpa using hE)

/-- On a manifold whose model space has finite dimension greater than one, the points that lie
on none of countably many differentiable loops `g i : AddCircle p → M` form a dense set. -/
theorem dense_compl_iUnion_range_addCircle [IsManifold I 1 M] (hE : 1 < Module.finrank ℝ E)
    {p : ℝ} [Fact (0 < p)] {ι : Type*} [Countable ι] {g : ι → AddCircle p → M}
    (hg : ∀ i, MDifferentiable 𝓘(ℝ) I (g i)) :
    Dense (⋃ i, range (g i))ᶜ := by
  have hcoe : MDifferentiable 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) :=
    (AddCircle.contMDiff_coe p 1).mdifferentiable one_ne_zero
  simpa [(QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples p)).range_comp] using
    dense_compl_union_iUnion_range (s := ∅) hE (isDiscrete_iff_discreteTopology.2 inferInstance)
      (f := fun i ↦ g i ∘ (↑)) fun i ↦ (hg i).comp hcoe

end SymplecticGeometry

end
