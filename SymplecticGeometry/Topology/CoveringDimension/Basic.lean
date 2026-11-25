/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ShrinkingLemma

/-!
# A relative bound on the covering dimension

For a set `K` of a topological space `X` and `n : ℕ`, `CoveringDimLE K n` says that every
finite family of open sets of `X` whose union contains `K` has a finite refinement by open sets
of `X`, still covering `K`, in which every point of `K` lies in at most `n + 1` members. For
`K = univ` this is the Lebesgue covering dimension of `X` bounded by `n`, in the form for finite
covers. The relative form is checked inside the ambient space, so that it passes to closed
subsets and along inducing maps without changing spaces.

## Main declarations

* `SymplecticGeometry.CoveringDimLE`: the bound, with `coveringDimLE_def`.
* `SymplecticGeometry.CoveringDimLE.mono`, `SymplecticGeometry.coveringDimLE_empty`,
  `SymplecticGeometry.CoveringDimLE.subset`: monotonicity in `n`, the empty set, and closed
  subsets.
* `SymplecticGeometry.CoveringDimLE.of_isInducing`: the bound for `f '' K` gives the bound
  for `K` along an inducing map `f`.
* `SymplecticGeometry.coveringDimLE_image_val_iff`: for `K` in an open subspace `S`, the bound
  for `K` in `S` and for its image in `X` agree.
* `SymplecticGeometry.CoveringDimLE.exists_finset_card_le`: in a normal space, for `K`
  closed, a refinement inside a given open neighbourhood of `K` in which every point of `X`
  lies in at most `n + 1` members.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50 (covering dimension)
-/

public section

open Set

namespace SymplecticGeometry

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Classical in
/-- `CoveringDimLE K n`: every finite set `𝒰` of open sets of `X` covering `K` has a
refinement `𝒱`, a finite set of open sets of `X` covering `K`, each inside a member of `𝒰`,
such that every point of `K` lies in at most `n + 1` members of `𝒱`. -/
def CoveringDimLE (K : Set X) (n : ℕ) : Prop :=
  ∀ 𝒰 : Finset (Set X), (∀ U ∈ 𝒰, IsOpen U) → K ⊆ ⋃₀ (𝒰 : Set (Set X)) →
    ∃ 𝒱 : Finset (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ K ⊆ ⋃₀ (𝒱 : Set (Set X)) ∧
      (∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U) ∧ ∀ x ∈ K, {V ∈ 𝒱 | x ∈ V}.card ≤ n + 1

open Classical in
theorem coveringDimLE_def (K : Set X) (n : ℕ) :
    CoveringDimLE K n ↔
      ∀ 𝒰 : Finset (Set X), (∀ U ∈ 𝒰, IsOpen U) → K ⊆ ⋃₀ (𝒰 : Set (Set X)) →
        ∃ 𝒱 : Finset (Set X), (∀ V ∈ 𝒱, IsOpen V) ∧ K ⊆ ⋃₀ (𝒱 : Set (Set X)) ∧
          (∀ V ∈ 𝒱, ∃ U ∈ 𝒰, V ⊆ U) ∧ ∀ x ∈ K, {V ∈ 𝒱 | x ∈ V}.card ≤ n + 1 :=
  Iff.rfl

namespace CoveringDimLE

variable {K L : Set X} {n m : ℕ}

/-- The bound for `n` gives the bound for every `m ≥ n`. -/
theorem mono (h : CoveringDimLE K n) (hnm : n ≤ m) : CoveringDimLE K m := by
  intro 𝒰 hU hK
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := h 𝒰 hU hK
  exact ⟨𝒱, hV, hKV, hVU, fun x hx => (hcard x hx).trans (by omega)⟩

/-- The bound passes to a closed subset. -/
theorem subset (h : CoveringDimLE K n) (hLK : L ⊆ K) (hL : IsClosed L) :
    CoveringDimLE L n := by
  classical
  intro 𝒰 hU hLU
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := h (insert Lᶜ 𝒰)
    (by simpa [Finset.forall_mem_insert] using ⟨hL, hU⟩)
    (fun x _ => by
      by_cases hx : x ∈ L
      · obtain ⟨U, hU𝒰, hxU⟩ := hLU hx
        exact ⟨U, by simp [hU𝒰], hxU⟩
      · exact ⟨Lᶜ, by simp, hx⟩)
  refine ⟨{V ∈ 𝒱 | ∃ U ∈ 𝒰, V ⊆ U}, fun V hV' => hV V (Finset.mem_filter.1 hV').1,
    fun x hx => ?_, fun V hV' => (Finset.mem_filter.1 hV').2, fun x hx => ?_⟩
  · obtain ⟨V, hV𝒱, hxV⟩ := hKV (hLK hx)
    obtain ⟨U, hU', hVU'⟩ := hVU V hV𝒱
    rcases Finset.mem_insert.1 hU' with rfl | hU𝒰
    · exact absurd hx (hVU' hxV)
    · exact ⟨V, Finset.mem_filter.2 ⟨hV𝒱, U, hU𝒰, hVU'⟩, hxV⟩
  · refine le_trans (Finset.card_le_card fun V hV' => ?_) (hcard x (hLK hx))
    simp only [Finset.mem_filter] at hV' ⊢
    exact ⟨hV'.1.1, hV'.2⟩

/-- The bound passes back along an inducing map: if `f '' K` satisfies it in `Y`, then `K`
satisfies it in `X`. -/
theorem of_isInducing {f : X → Y} (hf : Topology.IsInducing f) {K : Set X}
    (h : CoveringDimLE (f '' K) n) : CoveringDimLE K n := by
  classical
  intro 𝒰 hU hK
  have hpre : ∀ U ∈ 𝒰, ∃ U' : Set Y, IsOpen U' ∧ f ⁻¹' U' = U :=
    fun U hU𝒰 => hf.isOpen_iff.1 (hU U hU𝒰)
  choose! g hgo hgf using hpre
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := h (𝒰.image g)
    (by simpa using fun U hU𝒰 => hgo U hU𝒰)
    (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨U, hU𝒰, hxU⟩ := hK hx
      refine ⟨g U, by simpa using ⟨U, hU𝒰, rfl⟩, ?_⟩
      rw [← hgf U hU𝒰] at hxU
      exact hxU)
  refine ⟨𝒱.image (f ⁻¹' ·), ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · simpa using fun V hV𝒱 => (hV V hV𝒱).preimage hf.continuous
  · obtain ⟨V, hV𝒱, hxV⟩ := hKV (mem_image_of_mem f hx)
    exact ⟨f ⁻¹' V, by simpa using ⟨V, hV𝒱, rfl⟩, hxV⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro V hV𝒱
    obtain ⟨_, hU', hVU'⟩ := hVU V hV𝒱
    obtain ⟨U, hU𝒰, rfl⟩ := Finset.mem_image.1 hU'
    exact ⟨U, hU𝒰, (preimage_mono hVU').trans (hgf U hU𝒰).le⟩
  · rw [Finset.filter_image]
    exact Finset.card_image_le.trans (hcard (f x) (mem_image_of_mem f hx))

end CoveringDimLE

/-- The empty set satisfies the bound for every `n`. -/
theorem coveringDimLE_empty (n : ℕ) : CoveringDimLE (∅ : Set X) n :=
  fun _ _ _ => ⟨∅, by simp, by simp, by simp, by simp⟩

/-- For a set `K` of an open subspace `S` of `X`, the bound for `K` in `S` is the bound for
its image in `X`. -/
theorem coveringDimLE_image_val_iff {S : Set X} (hS : IsOpen S) {K : Set S} {n : ℕ} :
    CoveringDimLE ((↑) '' K : Set X) n ↔ CoveringDimLE K n := by
  classical
  refine ⟨CoveringDimLE.of_isInducing Topology.IsInducing.subtypeVal, fun h 𝒰 hU hK => ?_⟩
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := h (𝒰.image ((↑) ⁻¹' ·))
    (by simpa using fun U hU𝒰 => (hU U hU𝒰).preimage continuous_subtypeVal)
    (fun x hx => by
      obtain ⟨U, hU𝒰, hxU⟩ := hK (mem_image_of_mem _ hx)
      exact ⟨_, Finset.mem_image_of_mem _ hU𝒰, hxU⟩)
  refine ⟨𝒱.image ((↑) '' ·), ?_, ?_, ?_, ?_⟩
  · simpa using fun V hV𝒱 => hS.isOpenMap_subtypeVal V (hV V hV𝒱)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, hV𝒱, hxV⟩ := hKV hx
    exact ⟨_, Finset.mem_image_of_mem _ hV𝒱, mem_image_of_mem _ hxV⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro V hV𝒱
    obtain ⟨_, hU', hVU'⟩ := hVU V hV𝒱
    obtain ⟨U, hU𝒰, rfl⟩ := Finset.mem_image.1 hU'
    exact ⟨U, hU𝒰, (image_mono hVU').trans (image_preimage_subset _ _)⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Finset.filter_image]
    refine Finset.card_image_le.trans (le_trans (Finset.card_le_card fun V hV' => ?_)
      (hcard x hx))
    simp only [Finset.mem_filter, Subtype.val_injective.mem_set_image] at hV' ⊢
    exact hV'

open Classical in
/-- In a normal space, a closed set `K` with `CoveringDimLE K n`, a finite cover `𝒰` of `K` by
open sets and an open `O ⊇ K` give a finite set of open subsets of `O`, each inside a member of
`𝒰`, covering `K`, such that every point of `X` lies in at most `n + 1` of them. -/
theorem CoveringDimLE.exists_finset_card_le [NormalSpace X] {K : Set X} {n : ℕ}
    (h : CoveringDimLE K n) (hK : IsClosed K) {𝒰 : Finset (Set X)} (hU : ∀ U ∈ 𝒰, IsOpen U)
    (hKU : K ⊆ ⋃₀ (𝒰 : Set (Set X))) {O : Set X} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ 𝒲 : Finset (Set X), (∀ W ∈ 𝒲, IsOpen W ∧ W ⊆ O ∧ ∃ U ∈ 𝒰, W ⊆ U) ∧
      K ⊆ ⋃₀ (𝒲 : Set (Set X)) ∧ ∀ x, {W ∈ 𝒲 | x ∈ W}.card ≤ n + 1 := by
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := h (𝒰.image (· ∩ O))
    (by simpa using fun U hU𝒰 => (hU U hU𝒰).inter hO)
    (fun x hx => by
      obtain ⟨U, hU𝒰, hxU⟩ := hKU hx
      exact ⟨U ∩ O, Finset.mem_image_of_mem _ hU𝒰, hxU, hKO hx⟩)
  obtain ⟨v, hKv, hvo, hvV⟩ := exists_subset_iUnion_closure_subset
    (u := fun V : 𝒱 => (V : Set X)) hK (fun V => hV V V.property) (fun _ _ => toFinite _)
    (fun x hx => by
      obtain ⟨V, hV𝒱, hxV⟩ := hKV hx
      exact mem_iUnion.2 ⟨⟨V, hV𝒱⟩, hxV⟩)
  -- `B` is the closed set of points in the closures of `n + 2` of the `v i`.
  set B : Set X := ⋃ T ∈ (Finset.univ : Finset 𝒱).powersetCard (n + 2), ⋂ i ∈ T, closure (v i)
  have hB : IsClosed B :=
    isClosed_biUnion_finset fun T _ => isClosed_biInter fun i _ => isClosed_closure
  have hmemB : ∀ x, n + 1 < ({i | x ∈ closure (v i)} : Finset 𝒱).card → x ∈ B := fun x hx => by
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hx)
    exact mem_iUnion₂.2 ⟨T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hTc⟩,
      mem_iInter₂.2 fun i hi => (Finset.mem_filter.1 (hT hi)).2⟩
  have hKB : ∀ x ∈ K, x ∉ B := fun x hx hxB => by
    obtain ⟨T, hT, hxT⟩ := mem_iUnion₂.1 hxB
    have hTc := (Finset.mem_powersetCard.1 hT).2
    have : (T.map (Function.Embedding.subtype _)).card ≤ n + 1 :=
      (Finset.card_le_card fun V hV' => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hV'
        exact Finset.mem_filter.2 ⟨i.property, hvV i (mem_iInter₂.1 hxT i hi)⟩).trans (hcard x hx)
    simp [hTc] at this
  refine ⟨Finset.univ.image fun i => v i \ B, ?_, fun x hx => ?_, fun x => ?_⟩
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro i
    obtain ⟨_, hU', hiU⟩ := hVU i i.property
    obtain ⟨U, hU𝒰, rfl⟩ := Finset.mem_image.1 hU'
    have hvi : v i \ B ⊆ U ∩ O := sdiff_subset.trans (subset_closure.trans ((hvV i).trans hiU))
    exact ⟨(hvo i).sdiff hB, hvi.trans inter_subset_right, U, hU𝒰,
      hvi.trans inter_subset_left⟩
  · obtain ⟨i, hxi⟩ := mem_iUnion.1 (hKv hx)
    exact ⟨v i \ B, Finset.mem_image_of_mem _ (Finset.mem_univ i), hxi, hKB x hx⟩
  · have hsub : {W ∈ Finset.univ.image (fun i => v i \ B) | x ∈ W} ⊆
        ({i | x ∈ v i \ B} : Finset 𝒱).image fun i => v i \ B := fun W hW => by
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hW ⊢
      obtain ⟨⟨i, rfl⟩, hxi⟩ := hW
      exact ⟨i, hxi, rfl⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (not_lt.1 fun hlt => ?_))
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (Nat.zero_lt_of_lt hlt)
    refine (Finset.mem_filter.1 hi).2.2 (hmemB x (hlt.trans_le (Finset.card_le_card ?_)))
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ j, subset_closure (Finset.mem_filter.1 hj).2.1⟩

end SymplecticGeometry

end
