/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.Regular

/-!
# Disjoint locally finite neighbourhoods in paracompact spaces

In a paracompact regular space, a locally finite family `R` of pairwise disjoint closed sets, each
disjoint from a closed set `Q`, has open neighbourhoods `O i ⊇ R i` that are pairwise disjoint,
miss `Q`, and form a locally finite family
(`LocallyFinite.exists_isOpen_superset_pairwise_disjoint`).

A locally finite family of pairwise disjoint closed sets is discrete: every point has a
neighbourhood that meets at most one of them, and, together with `Q`, at most one of the sets
`Q, R i`. The proof is the classical argument that paracompact spaces are collectionwise normal.
Choose for each point `x` a closed neighbourhood `C x` with this property; a locally finite open
refinement `V` of the interiors (Mathlib's `precise_refinement`) has locally finite closures
`K x ⊆ C x`. Then `O i` is the complement of the union of those `K x` that miss `R i`.

## Main results

* `LocallyFinite.exists_isOpen_superset_pairwise_disjoint`: pairwise disjoint, locally finite
  open neighbourhoods of a locally finite family of pairwise disjoint closed sets, avoiding a
  closed set disjoint from all of them.

## References

* R. Engelking, *General Topology*, Section 5.1 (paracompact spaces are collectionwise normal)
-/

public section

open Set Function Topology

variable {ι X : Type*} [TopologicalSpace X]

/-- In a paracompact regular space, let `R` be a locally finite family of pairwise disjoint closed
sets, each disjoint from a closed set `Q`. Then there are open sets `O i ⊇ R i`, pairwise
disjoint and disjoint from `Q`, that form a locally finite family. -/
theorem LocallyFinite.exists_isOpen_superset_pairwise_disjoint [ParacompactSpace X]
    [RegularSpace X] {R : ι → Set X} {Q : Set X} (hR : ∀ i, IsClosed (R i))
    (hlf : LocallyFinite R) (hdisj : Pairwise (Disjoint on R)) (hQ : IsClosed Q)
    (hRQ : ∀ i, Disjoint (R i) Q) :
    ∃ O : ι → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, R i ⊆ O i) ∧ Pairwise (Disjoint on O) ∧
      (∀ i, Disjoint (O i) Q) ∧ LocallyFinite O := by
  classical
  -- Sets that meet at most one of the sets `Q, R i`.
  let good (C : Set X) : Prop :=
    (∀ i j, (C ∩ R i).Nonempty → (C ∩ R j).Nonempty → i = j) ∧
      ∀ i, (C ∩ R i).Nonempty → Disjoint C Q
  have hgood_mono {C D : Set X} (hCD : C ⊆ D) (hD : good D) : good C :=
    ⟨fun i j hi hj ↦ hD.1 i j (hi.mono (inter_subset_inter_left _ hCD))
      (hj.mono (inter_subset_inter_left _ hCD)),
      fun i hi ↦ (hD.2 i (hi.mono (inter_subset_inter_left _ hCD))).mono_left hCD⟩
  -- Every point has a neighbourhood meeting at most one of the sets `Q, R i`.
  have hnhds (x : X) : ∃ W ∈ 𝓝 x, good W := by
    let S : ι → Set X := fun i ↦ if x ∈ R i then ∅ else R i
    have hS : IsClosed (⋃ i, S i) :=
      (hlf.subset fun i ↦ by dsimp only [S]; split_ifs <;> simp).isClosed_iUnion
        fun i ↦ by dsimp only [S]; split_ifs; exacts [isClosed_empty, hR i]
    have hxS : x ∉ ⋃ i, S i := by simp +contextual [S]
    have hW : (⋃ i, S i)ᶜ ∈ 𝓝 x := hS.isOpen_compl.mem_nhds hxS
    -- A point of `W` in `R i` with `x ∉ R i` is impossible.
    have hmem {W : Set X} (hWS : W ⊆ (⋃ i, S i)ᶜ) {i : ι} (hi : (W ∩ R i).Nonempty) : x ∈ R i := by
      by_contra hx
      obtain ⟨y, hyW, hyR⟩ := hi
      exact hWS hyW (mem_iUnion.2 ⟨i, by simpa [S, hx] using hyR⟩)
    by_cases hxQ : x ∈ Q
    · refine ⟨(⋃ i, S i)ᶜ, hW, fun i _ hi ↦ ?_, fun i hi ↦ ?_⟩ <;>
        exact ((hRQ i).notMem_of_mem_left (hmem subset_rfl hi) hxQ).elim
    · refine ⟨(⋃ i, S i)ᶜ ∩ Qᶜ, Filter.inter_mem hW (hQ.isOpen_compl.mem_nhds hxQ),
        fun i j hi hj ↦ ?_, fun _ _ ↦ disjoint_compl_left.mono_left inter_subset_right⟩
      by_contra hij
      exact (hdisj hij).notMem_of_mem_left (hmem inter_subset_left hi)
        (hmem inter_subset_left hj)
  choose W hWx hWgood using hnhds
  -- Closed neighbourhoods inside them, and a locally finite open refinement of their interiors.
  choose C hCx hCc hCW using fun x ↦ exists_mem_nhds_isClosed_subset (hWx x)
  obtain ⟨V, -, hVcov, hVlf, hVC⟩ := precise_refinement (fun x ↦ interior (C x))
    (fun _ ↦ isOpen_interior)
    (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, mem_interior_iff_mem_nhds.2 (hCx x)⟩)
  set K : X → Set X := fun x ↦ closure (V x)
  have hKlf : LocallyFinite K := hVlf.closure
  have hKgood (x : X) : good (K x) :=
    hgood_mono ((closure_mono ((hVC x).trans interior_subset)).trans
      (hCc x).closure_subset |>.trans (hCW x)) (hWgood x)
  have hcov (y : X) : ∃ x, y ∈ V x := mem_iUnion.1 (hVcov.symm ▸ mem_univ y)
  -- `O i` is the complement of the union of the `K x` that miss `R i`.
  let O : ι → Set X := fun i ↦ (⋃ x, if Disjoint (K x) (R i) then K x else ∅)ᶜ
  -- A point of `O i` lies in some `V x`, and then `K x` meets `R i`.
  have hO {i : ι} {y : X} (hy : y ∈ O i) : ∃ x, y ∈ V x ∧ (K x ∩ R i).Nonempty := by
    obtain ⟨x, hx⟩ := hcov y
    refine ⟨x, hx, not_disjoint_iff_nonempty_inter.1 fun hd ↦ hy (mem_iUnion.2 ⟨x, ?_⟩)⟩
    simpa [hd] using subset_closure hx
  refine ⟨O, fun i ↦ ?_, fun i y hy ↦ ?_, fun i j hij ↦ ?_, fun i ↦ ?_, fun z ↦ ?_⟩
  · refine (LocallyFinite.isClosed_iUnion (hKlf.subset fun x ↦ ?_) fun x ↦ ?_).isOpen_compl
    · split_ifs <;> simp
    · split_ifs; exacts [isClosed_closure, isClosed_empty]
  · simp only [O, mem_compl_iff, mem_iUnion, not_exists]
    intro x hx
    split_ifs at hx with hd
    exacts [hd.notMem_of_mem_right hy hx, hx]
  · refine disjoint_left.2 fun y hyi hyj ↦ hij ?_
    obtain ⟨x, hx, hxi⟩ := hO hyi
    -- `y ∈ K x` and `y ∈ O j`, so `K x` also meets `R j`.
    exact (hKgood x).1 i j hxi (not_disjoint_iff_nonempty_inter.1 fun hd ↦
      hyj (mem_iUnion.2 ⟨x, by simpa [hd] using subset_closure hx⟩))
  · refine disjoint_left.2 fun y hy hyQ ↦ ?_
    obtain ⟨x, hx, hxi⟩ := hO hy
    exact ((hKgood x).2 i hxi).notMem_of_mem_left (subset_closure hx) hyQ
  · obtain ⟨N, hN, hNf⟩ := hKlf z
    -- Each `K x` meets at most one `R i`, and only finitely many `K x` meet `N`.
    refine ⟨N, hN, (hNf.biUnion (t := fun x ↦ {i | (K x ∩ R i).Nonempty}) fun x _ ↦
      Set.Subsingleton.finite fun i hi j hj ↦ (hKgood x).1 i j hi hj).subset
        fun i ⟨y, hyO, hyN⟩ ↦ ?_⟩
    obtain ⟨x, hx, hxi⟩ := hO hyO
    exact mem_iUnion₂.2 ⟨x, ⟨y, subset_closure hx, hyN⟩, hxi⟩
