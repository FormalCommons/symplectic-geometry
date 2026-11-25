/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.CoveringDimension.Basic

/-!
# The covering dimension of a finite union of closed sets

If closed sets `K₁` and `K₂` of a topological space each satisfy `CoveringDimLE · n`, then so
does `K₁ ∪ K₂`, and likewise for any finite family of closed sets. No separation axiom is
needed.

The proof follows Munkres. A closed set `K` with the bound turns any finite open cover `𝒰`
into one with order at most `n + 1` at the points of `K`, without raising the order anywhere
else and without shrinking its union: refine `𝒰` near `K`, attach each piece of the
refinement to a member of `𝒰` that contains it, and replace each `U ∈ 𝒰` by `U \ K` together
with the pieces attached to it. Doing this for `K₁` and then for `K₂` gives the union.

## Main declarations

* `SymplecticGeometry.CoveringDimLE.exists_refinement`: the step above for one closed set.
* `SymplecticGeometry.CoveringDimLE.union`: two closed sets.
* `SymplecticGeometry.CoveringDimLE.biUnion`: a finite family of closed sets.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, Theorem 50.2
-/

public section

open Set

namespace SymplecticGeometry

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

namespace CoveringDimLE

open Classical in
/-- For a closed set `K` with `CoveringDimLE K n`, every finite set `𝒰` of open sets whose
union contains `K` has a refinement `𝒟`, a finite set of open sets each inside a member of
`𝒰`, whose union contains that of `𝒰`, such that a point of `K` lies in at most `n + 1`
members of `𝒟` and no point lies in more members of `𝒟` than of `𝒰`. -/
theorem exists_refinement {K : Set X} (h : CoveringDimLE K n) (hK : IsClosed K)
    {𝒰 : Finset (Set X)} (hU : ∀ U ∈ 𝒰, IsOpen U) (hKU : K ⊆ ⋃₀ (𝒰 : Set (Set X))) :
    ∃ 𝒟 : Finset (Set X), (∀ D ∈ 𝒟, IsOpen D) ∧
      ⋃₀ (𝒰 : Set (Set X)) ⊆ ⋃₀ (𝒟 : Set (Set X)) ∧ (∀ D ∈ 𝒟, ∃ U ∈ 𝒰, D ⊆ U) ∧
      (∀ x ∈ K, {D ∈ 𝒟 | x ∈ D}.card ≤ n + 1) ∧
      ∀ x, {D ∈ 𝒟 | x ∈ D}.card ≤ {U ∈ 𝒰 | x ∈ U}.card := by
  obtain ⟨𝒱, hV, hKV, hVU, hcard⟩ := (coveringDimLE_def K n).1 h 𝒰 hU hKU
  choose! f hf𝒰 hVf using hVU
  -- `D U` is `U \ K` together with the members of `𝒱` attached to `U` by `f`.
  set D : Set X → Set X := fun U => (U \ K) ∪ ⋃ V ∈ {V ∈ 𝒱 | f V = U}, V
  have hDU : ∀ U ∈ 𝒰, D U ⊆ U := fun U _ => union_subset sdiff_subset <| iUnion₂_subset
    fun V hV' => by
      obtain ⟨hV𝒱, rfl⟩ := Finset.mem_filter.1 hV'
      exact hVf V hV𝒱
  have hfilter : ∀ x, {D' ∈ 𝒰.image D | x ∈ D'}.card ≤ {U ∈ 𝒰 | x ∈ D U}.card := fun x => by
    -- `filter_image` produces another decidability instance for the filter, which `convert`
    -- identifies with this one.
    rw [Finset.filter_image]
    convert Finset.card_image_le (s := {U ∈ 𝒰 | x ∈ D U}) (f := D)
  refine ⟨𝒰.image D, ?_, fun x hx => ?_, ?_, fun x hx => ?_, fun x => ?_⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun U hU𝒰 => ((hU U hU𝒰).sdiff hK).union
      (isOpen_biUnion fun V hV' => hV V (Finset.mem_filter.1 hV').1)
  · by_cases hxK : x ∈ K
    · obtain ⟨V, hV𝒱, hxV⟩ := hKV hxK
      exact ⟨D (f V), Finset.mem_image_of_mem _ (hf𝒰 V hV𝒱),
        Or.inr (mem_biUnion (Finset.mem_filter.2 ⟨hV𝒱, rfl⟩) hxV)⟩
    · obtain ⟨U, hU𝒰, hxU⟩ := hx
      exact ⟨D U, Finset.mem_image_of_mem _ hU𝒰, Or.inl ⟨hxU, hxK⟩⟩
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun U hU𝒰 => ⟨U, hU𝒰, hDU U hU𝒰⟩
  · -- At a point of `K`, each `D U` containing `x` contains it through some `V ∋ x` with
    -- `f V = U`, so these `U` are images under `f` of members of `𝒱` containing `x`.
    refine ((hfilter x).trans (Finset.card_le_card (t := {V ∈ 𝒱 | x ∈ V}.image f)
      fun U hU' => ?_)).trans (Finset.card_image_le.trans (hcard x hx))
    obtain ⟨-, hxD⟩ := Finset.mem_filter.1 hU'
    rcases hxD with ⟨-, hxK⟩ | hxD
    · exact absurd hx hxK
    · obtain ⟨V, hV', hxV⟩ := mem_iUnion₂.1 hxD
      obtain ⟨hV𝒱, rfl⟩ := Finset.mem_filter.1 hV'
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hV𝒱, hxV⟩)
  · exact (hfilter x).trans (Finset.card_le_card fun U hU' => Finset.mem_filter.2
      ⟨(Finset.mem_filter.1 hU').1, hDU U (Finset.mem_filter.1 hU').1 (Finset.mem_filter.1 hU').2⟩)

/-- If closed sets `K₁` and `K₂` both satisfy `CoveringDimLE · n`, then so does `K₁ ∪ K₂`. -/
theorem union {K₁ K₂ : Set X} (h₁ : CoveringDimLE K₁ n) (h₂ : CoveringDimLE K₂ n)
    (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) : CoveringDimLE (K₁ ∪ K₂) n := by
  refine (coveringDimLE_def _ n).2 fun 𝒰 hU hKU => ?_
  obtain ⟨𝒟₁, hD₁, hUD₁, hD₁U, hcard₁, -⟩ :=
    h₁.exists_refinement hK₁ hU (subset_union_left.trans hKU)
  obtain ⟨𝒟₂, hD₂, hUD₂, hD₂U, hcard₂, hcard₂'⟩ :=
    h₂.exists_refinement hK₂ hD₁ ((subset_union_right.trans hKU).trans hUD₁)
  refine ⟨𝒟₂, hD₂, hKU.trans (hUD₁.trans hUD₂), fun D hD => ?_, fun x hx => ?_⟩
  · obtain ⟨D₁, hD₁𝒟, hDD₁⟩ := hD₂U D hD
    obtain ⟨U, hU𝒰, hD₁U'⟩ := hD₁U D₁ hD₁𝒟
    exact ⟨U, hU𝒰, hDD₁.trans hD₁U'⟩
  · by_cases hx₂ : x ∈ K₂
    · exact hcard₂ x hx₂
    · exact (hcard₂' x).trans (hcard₁ x (hx.resolve_right hx₂))

/-- If each closed set `K i`, for `i` in a finite set `s`, satisfies `CoveringDimLE · n`, then
so does their union. -/
theorem biUnion {ι : Type*} {s : Finset ι} {K : ι → Set X} (hK : ∀ i ∈ s, IsClosed (K i))
    (h : ∀ i ∈ s, CoveringDimLE (K i) n) : CoveringDimLE (⋃ i ∈ s, K i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ ih =>
    rw [Finset.set_biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hK h
    exact h.1.union (ih hK.2 h.2) hK.1 (isClosed_biUnion_finset hK.2)

end CoveringDimLE

end SymplecticGeometry

end
