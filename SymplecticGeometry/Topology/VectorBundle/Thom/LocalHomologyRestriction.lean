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

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local homology and the restriction of a class to a point).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set

universe w v u

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

end TauCeti

end
