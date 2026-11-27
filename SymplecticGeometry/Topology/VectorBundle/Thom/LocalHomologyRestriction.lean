/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# Restricting a class of the Thom pair to a point of the zero section

For a bundle `E → B` and a point `b` of the base, every nonzero vector differs from the point
`0_b` of the zero section, so the identity of the total space is a map of pairs from the Thom
pair `(E, E₀)` to `(E, E ∖ 0_b)`. The induced map
`TauCeti.thomPairLocalHomologyRestriction : Hₖ(E, E₀) ⟶ Hₖ(E, E ∖ 0_b)` takes a class of the Thom
pair to its local class at `0_b`, an element of the local homology of the total space at `0_b`.

Tau Ceti's `TauCeti.localHomologyRestriction` restricts local homology along an inclusion of
sets, but the Thom pair is not written as the local homology along the zero section (its second
space is `zeroSectionCompl`, not the complement of a set), so this map is defined separately.

## Main definitions

* `TauCeti.thomPairLocalHomologyRestriction`: the map from the homology of the Thom pair to the
  local homology of the total space at `0_b`, unfolded by
  `TauCeti.thomPairLocalHomologyRestriction_def`.

## Main results

* `Bundle.zeroSectionCompl_union_compl_preimage_singleton`: `E ∖ 0 ∪ E ∖ E_b` is the complement
  of `0_b`.
* `TauCeti.singularHomologyMap_ofSubsetMap_thomPairLocalHomologyRestriction`: reading a class of
  the Thom pair relative to `E ∖ 0 ∪ E ∖ E_b` factors through its local class at `0_b`, since
  that set is the complement of `0_b`
  (`Bundle.zeroSectionCompl_union_compl_preimage_singleton`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local homology and the restriction of a class to a point).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set TauCeti

universe w v u

namespace Bundle

variable {B : Type*} {P : Type*} {E : B → Type*} [∀ b, Zero (E b)]

/-- The points of the total space that are nonzero vectors or lie off the fibre over `b` are
the points other than the zero vector `0_b`. -/
theorem zeroSectionCompl_union_compl_preimage_singleton (b : B) :
    zeroSectionCompl P E ∪ (π P E ⁻¹' {b})ᶜ = {zeroSection P E b}ᶜ := by
  ext ⟨b', v⟩
  simp only [mem_union, mem_zeroSectionCompl, mem_compl_iff, mem_preimage, mem_singleton_iff,
    zeroSection, TotalSpace.mk.injEq, not_and]
  constructor
  · rintro (hv | hb) rfl
    exacts [fun h ↦ hv (eq_of_heq h), (hb rfl).elim]
  · intro h
    by_cases hb : b' = b
    · subst hb
      exact Or.inl fun hv ↦ h rfl (heq_of_eq hv)
    · exact Or.inr hb

end Bundle

namespace TauCeti

/-- The nonzero vectors of a bundle lie in the complement of the point `0_b` of the zero
section. -/
theorem zeroSectionCompl_subset_compl_singleton_zeroSection {B : Type*} (F : Type*)
    (E : B → Type*) [∀ b, Zero (E b)] (b : B) :
    zeroSectionCompl F E ⊆ {zeroSection F E b}ᶜ := by
  rw [zeroSectionCompl_eq_compl_range]
  exact compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self b))

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {B : Type w} (F : Type*) (E : B → Type w) [∀ b, Zero (E b)] [TopologicalSpace (TotalSpace F E)]

/-- The restriction `Hₖ(E, E₀) ⟶ Hₖ(E, E ∖ 0_b)` from the homology of the Thom pair of a bundle
to the local homology of its total space at the point `0_b` of the zero section, induced by the
identity of the total space. -/
def thomPairLocalHomologyRestriction (b : B) (k : ℕ) :
    (thomPair F E).singularHomology R k ⟶ localHomology R {zeroSection F E b} k :=
  TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of (TotalSpace F E)))
    (zeroSectionCompl_subset_compl_singleton_zeroSection F E b)) R k

/-- The restriction to `0_b` is the map on relative homology induced by the identity of the total
space. -/
theorem thomPairLocalHomologyRestriction_def (b : B) (k : ℕ) :
    thomPairLocalHomologyRestriction R F E b k =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of (TotalSpace F E)))
        (zeroSectionCompl_subset_compl_singleton_zeroSection F E b)) R k :=
  (rfl)

section

variable {B : Type} [TopologicalSpace B] {F : Type} [TopologicalSpace F] {E : B → Type}
  [∀ b, Zero (E b)] [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

/-- Reading a class of the Thom pair `Hₖ(E, E ∖ 0)` relative to `E ∖ 0 ∪ E ∖ E_b` is reading its
local class at `0_b` (`thomPairLocalHomologyRestriction`) relative to that set, since that set is
the complement of `0_b`. -/
theorem singularHomologyMap_ofSubsetMap_thomPairLocalHomologyRestriction (R : ModuleCat.{0} ℤ)
    (b : B) (k : ℕ) (γ : ((thomPair F E).singularHomology R k : ModuleCat.{0} ℤ)) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
        (zeroSectionCompl_union_compl_preimage_singleton (P := F) b).superset hv) R k
        ((thomPairLocalHomologyRestriction R F E b k).hom γ) =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of (TotalSpace F E)))
        (B := zeroSectionCompl F E)
        (B' := zeroSectionCompl F E ∪ TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩ ⁻¹'
          ({b}ᶜ : Set (TopCat.of B))) fun _ hx ↦ Or.inl hx) R k γ := by
  rw [thomPairLocalHomologyRestriction_def, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_comp]
  exact congrArg (fun g ↦ TopPair.singularHomologyMap g R k γ)
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.comp_id _))

end

end TauCeti

end
