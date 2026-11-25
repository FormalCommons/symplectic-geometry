/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import SymplecticGeometry.Topology.CoveringDimension.Basic
import TauCeti.Topology.PartitionOfUnity.Basic

/-!
# Partitions of unity of bounded order on σ-compact spaces

Let `X` be a Hausdorff, locally compact, σ-compact space in which every compact set satisfies
`CoveringDimLE K n`. Then every open cover of `X` has a refinement with a subordinate partition
of unity in which at every point at most `3 * (n + 1)` functions do not vanish.

The proof goes through the shells of a compact exhaustion `S` with `S 0 = ∅`. The shell
`S (j + 1) \ interior (S j)` is compact and lies in the open set
`interior (S (j + 2)) \ S (j - 1)`. Over each shell,
`CoveringDimLE.exists_finset_card_le` refines the cover by finitely many open subsets of that
open set, with every point of `X` in at most `n + 1` of them. A point `x` lies only in the open
sets of the indices `j` with `S.find x - 2 ≤ j ≤ S.find x`, so the union of these families is a
locally finite cover in which every point lies in at most `3 * (n + 1)` members, and a
partition of unity subordinate to it has the same bound.

## Main declarations

* `SymplecticGeometry.exists_isSubordinate_card_finsupport_le`: the partition of unity of
  bounded order.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50 (covering dimension)
-/

public section

open Set

namespace SymplecticGeometry

universe u

variable {X : Type u} [TopologicalSpace X]

open Classical in
/-- For a compact exhaustion `K` and `S = K.shiftr`, an open cover `U` of `X` has a finite
refinement over the shell `S (j + 1) \ interior (S j)`: finitely many open subsets of
`interior (S (j + 2)) \ S (j - 1)`, each inside some `U i`, covering the shell, such that every
point of `X` lies in at most `n + 1` of them. -/
private theorem exists_finset_shell [T2Space X] [NormalSpace X] {n : ℕ}
    (hX : ∀ K : Set X, IsCompact K → CoveringDimLE K n) {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) (K : CompactExhaustion X) (j : ℕ) :
    ∃ 𝒲 : Finset (Set X),
      (∀ W ∈ 𝒲, IsOpen W ∧ W ⊆ interior (K.shiftr (j + 2)) \ K.shiftr (j - 1) ∧
        ∃ i, W ⊆ U i) ∧
      K.shiftr (j + 1) \ interior (K.shiftr j) ⊆ ⋃₀ (𝒲 : Set (Set X)) ∧
      ∀ x, {W ∈ 𝒲 | x ∈ W}.card ≤ n + 1 := by
  set S := K.shiftr
  have hA : IsCompact (S (j + 1) \ interior (S j)) := (S.isCompact _).diff isOpen_interior
  -- The shell lies in the open set `interior (S (j + 2)) \ S (j - 1)`.
  have hAO : S (j + 1) \ interior (S j) ⊆ interior (S (j + 2)) \ S (j - 1) := by
    rintro x ⟨hx, hxj⟩
    refine ⟨S.subset_interior_succ _ hx, fun hx' => ?_⟩
    rcases j with _ | j
    · have := S.mem_iff_find_le.1 hx'
      simp [S] at this
    · exact hxj (S.subset_interior_succ _ hx')
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hU (by simp [hcov])
  obtain ⟨𝒲, h𝒲, hA𝒲, hcard⟩ := (hX _ hA).exists_finset_card_le hA.isClosed
    (𝒰 := t.image U) (by simpa using fun i _ => hU i)
    (fun x hx => by simpa using mem_iUnion₂.1 (ht hx))
    (isOpen_interior.sdiff (S.isCompact _).isClosed) hAO
  refine ⟨𝒲, fun W hW => ?_, hA𝒲, hcard⟩
  obtain ⟨hWo, hWO, _, hU', hWU⟩ := h𝒲 W hW
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hU'
  exact ⟨hWo, hWO, i, hWU⟩

/-- In a Hausdorff, locally compact, σ-compact space in which every compact set satisfies the
covering-dimension bound for `n`, every open cover `U` has a refinement `U ∘ c` with a subordinate
partition of unity `ρ` such that at every point at most `3 * (n + 1)` of the functions of `ρ` do
not vanish. -/
theorem exists_isSubordinate_card_finsupport_le [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] {n : ℕ} (hX : ∀ K : Set X, IsCompact K → CoveringDimLE K n)
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) :
    ∃ (κ : Type u) (c : κ → ι) (ρ : PartitionOfUnity κ X univ),
      ρ.IsSubordinate (U ∘ c) ∧ ∀ x, (ρ.finsupport x).card ≤ 3 * (n + 1) := by
  classical
  let S := (CompactExhaustion.choice X).shiftr
  -- Over each shell, a finite refinement inside its open neighbourhood, of order `n + 1`.
  choose 𝒲 h𝒲 hA𝒲 hcard using exists_finset_shell hX U hU hcov (CompactExhaustion.choice X)
  let κ := {p : ℕ × Set X // p.2 ∈ 𝒲 p.1}
  let V : κ → Set X := fun k => k.val.2
  choose c hc using fun k : κ => (h𝒲 _ _ k.property).2.2
  -- A member of the `j`-th family contains only points `x` with `j ≤ S.find x ≤ j + 2`.
  have hloc : ∀ k x, x ∈ V k → S.find x ≤ k.val.1 + 2 ∧ k.val.1 ≤ S.find x := fun k x hx => by
    obtain ⟨hx2, hx1⟩ := (h𝒲 _ _ k.property).2.1 hx
    have h1 := mt S.mem_iff_find_le.2 hx1
    exact ⟨S.mem_iff_find_le.1 (interior_subset hx2), by omega⟩
  have hVcov : ⋃ k, V k = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hf : 1 ≤ S.find x := by simp [S]
    have hx : x ∈ S (S.find x - 1 + 1) \ interior (S (S.find x - 1)) :=
      ⟨by rw [Nat.sub_add_cancel hf]; exact S.mem_find x,
        fun hx => by have := S.mem_iff_find_le.1 (interior_subset hx); omega⟩
    obtain ⟨W, hW, hxW⟩ := hA𝒲 _ hx
    exact mem_iUnion.2 ⟨⟨(_, W), hW⟩, hxW⟩
  have hVlf : LocallyFinite V := by
    intro x
    refine ⟨interior (S (S.find x + 1)),
      isOpen_interior.mem_nhds (S.subset_interior_succ _ (S.mem_find x)), ?_⟩
    refine ((Finset.range (S.find x + 2)).biUnion fun j => (𝒲 j).image (j, ·)).finite_toSet.preimage
      Subtype.val_injective.injOn |>.subset ?_
    rintro k ⟨y, hyk, hy⟩
    have := (hloc k y hyk).2
    have := S.mem_iff_find_le.1 (interior_subset hy)
    simp only [Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, mem_preimage, mem_iUnion,
      mem_Iio, mem_image, Finset.mem_coe]
    exact ⟨k.val.1, by omega, k.val.2, k.property, rfl⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ V
    (fun k => (h𝒲 _ _ k.property).1) hVlf hVcov.ge
  refine ⟨κ, c, ρ, fun k => (hρ k).trans (hc k), fun x => ?_⟩
  set f := S.find x
  calc (ρ.finsupport x).card = ((ρ.finsupport x).map (Function.Embedding.subtype _)).card :=
        (Finset.card_map _).symm
    _ ≤ ((Finset.Icc (f - 2) f).biUnion fun j => {W ∈ 𝒲 j | x ∈ W}.image (j, ·)).card := by
        refine Finset.card_le_card fun p hp => ?_
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hp
        have hxk := hρ.mem_of_mem_finsupport hk
        have := hloc k x hxk
        simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_filter]
        exact ⟨k.val.1, by omega, k.val.2, ⟨k.property, hxk⟩, rfl⟩
    _ ≤ ∑ j ∈ Finset.Icc (f - 2) f, ({W ∈ 𝒲 j | x ∈ W}.image (j, ·)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.Icc (f - 2) f, (n + 1) :=
        Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (hcard j x)
    _ ≤ 3 * (n + 1) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)

end SymplecticGeometry

end
