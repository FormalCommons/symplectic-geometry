/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cup.RelativeKronecker
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Capping a cross product of two pairs with a class of the first factor

Let `A ⊆ X` and `B ⊆ Y` be open, and write `A × Y` and `X × B` for their preimages under the
projections of `X × Y`. For `o ∈ Hₚ(X, A; R)` and `x ∈ H_q(Y, B; S)`, the homology cross product
of the pairs `o × x = TopCat.singularHomologyCrossRelPair … (o ⊗ₜ x)` lies in
`Hₚ₊q(X × Y, A × Y ∪ X × B; R ⊗ S)`. Cap it, with the cap product of the excisive couple
`(A × Y, X × B)` (`TopCat.singularRelativeCap`), with the pull-back of a class `u ∈ Hᵖ(X, A)`
along the first projection, and push the result forward along the second projection
`(X × Y, X × B) ⟶ (Y, B)`. This gives back `x`, scaled by the Kronecker pairing of `u` and `o`:

`pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`

(`TopCat.singularRelativeCap_singularHomologyCrossRelPair`). It extends Tau Ceti's
`TopCat.singularCap_singularHomologyCrossRel` (`Cohomology/Cap/CrossRel.lean`), where the second
factor is a space, to a second pair, and holds for every class `u`, with no condition on `Hᵖ(X)`.

The proof follows that of `TopCat.singularCap_singularHomologyCrossRel`: both sides have the same
Kronecker pairing with every class `c ∈ H^q(Y, B; S, I)` with injective coefficients `I`, and
these pairings separate the classes of `H_q(Y, B; S)` (`TopPair.singularKronecker_bijective`).
The pairings are computed without the connecting morphism, from the naturality of the Kronecker
pairing (`TopPair.singularKronecker_naturality`), the Kronecker pairing of the excisive cap
product (`TopCat.singularRelativeCap_comp_singularKronecker`), which turns it into the relative
cup product of the pull-backs of `u` and `c`, that is the relative cross product `u × c`
(`TauCeti.singularRelativeCross_apply`), and the Kronecker pairing of relative cross products
(`TopCat.singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross`).

## Main results

* `TopCat.singularHomologyCrossRelPair_comp_singularRelativeCap_comp_singularKronecker`: the
  Kronecker pairing `⟨c, pr₂_*((o × x) ⌢ pr₁^* u)⟩ = ⟨u, o⟩ ⟨c, x⟩`,
  with coefficients in any module.
* `TopCat.singularRelativeCap_singularHomologyCrossRelPair`:
  `pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, Sections 6 and 7 (the slant and cap products of
  cross products, and the Thom isomorphism).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2 (the relative cross product) and Section 3.3 (cap products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w

namespace TopCat

variable {k : Type w} [CommRing k] {X Y : TopCat.{w}} {A : Set X} {B : Set Y}
  {R S I : ModuleCat.{w} k} (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}

/-- **The Kronecker pairing of a cap product with a cross product of pairs**,
`⟨c, pr₂_*((o × x) ⌢ pr₁^* u)⟩ = ⟨u, o⟩ ⟨c, x⟩`: for open `A ⊆ X` and `B ⊆ Y`, a class
`u ∈ Hᵖ(X, A; R, k)` and a class `c ∈ H^q(Y, B; S, I)`, capping the homology cross product
`Hₚ(X, A; R) ⊗ H_q(Y, B; S) ⟶ Hₚ₊q(X × Y, A × Y ∪ X × B; R ⊗ S)` of the pairs with the pull-back
of `u` along the first projection, pushing forward along the second projection to `H_q(Y, B; S)`
and evaluating `c` is the tensor product of the evaluations of `u` and `c`, followed by the left
unitor of `I`. -/
@[elementwise]
theorem singularHomologyCrossRelPair_comp_singularRelativeCap_comp_singularKronecker
    (u : (TopPair.ofSubset A).singularCohomology R k (𝟙_ (ModuleCat.{w} k)) p)
    (c : (TopPair.ofSubset B).singularCohomology S k I q) :
    singularHomologyCrossRelPair X Y A B R S p q (p + q) rfl ≫
        singularRelativeCap k (𝟙 (R ⊗ S)) (λ_ S).hom (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
          (isOpen_subtypeVal_preimage_preimage_fst_union hA)
          (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q (p + q) rfl
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p u) ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _))
          S q ≫
        (TopPair.ofSubset B).singularKronecker k q c =
      ((TopPair.ofSubset A).singularKronecker k p u ⊗ₘ
        (TopPair.ofSubset B).singularKronecker k q c) ≫ (λ_ I).hom := by
  rw [← TopPair.singularKronecker_naturality, singularRelativeCap_comp_singularKronecker,
    ← TauCeti.singularRelativeCross_apply k X Y hA hB]
  exact singularHomologyCrossRelPair_comp_singularKronecker_singularRelativeCross X Y _ hA hB p q
    (p + q) rfl u c

/-- **Capping a cross product of two pairs with a class of the first factor**,
`pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`: for open `A ⊆ X` and `B ⊆ Y`, a class
`u ∈ Hᵖ(X, A; R, k)`, a class `o ∈ Hₚ(X, A; R)` and a class `x ∈ H_q(Y, B; S)`, capping the
homology cross product `o × x ∈ Hₚ₊q(X × Y, A × Y ∪ X × B; R ⊗ S)` of the pairs with the pull-back
of `u` along the first projection, with the cap product of the excisive couple
`(A × Y, X × B)`, and pushing forward along the second projection
`(X × Y, X × B) ⟶ (Y, B)` gives `x` scaled by the Kronecker pairing `⟨u, o⟩`. -/
theorem singularRelativeCap_singularHomologyCrossRelPair
    (u : (TopPair.ofSubset A).singularCohomology R k (𝟙_ (ModuleCat.{w} k)) p)
    (o : ((TopPair.ofSubset A).singularHomology R p : ModuleCat.{w} k))
    (x : ((TopPair.ofSubset B).singularHomology S q : ModuleCat.{w} k)) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) S q
        (singularRelativeCap k (𝟙 (R ⊗ S)) (λ_ S).hom (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
          (isOpen_subtypeVal_preimage_preimage_fst_union hA)
          (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q (p + q) rfl
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p u)
          (singularHomologyCrossRelPair X Y A B R S p q (p + q) rfl (o ⊗ₜ x))) =
      ((TopPair.ofSubset A).singularKronecker k p u o : k) • x := by
  -- Classes of `H_q(Y, B; S)` are separated by their Kronecker pairings with classes with
  -- injective coefficients: the inclusion into an injective module is such a pairing.
  let ι := Injective.ι ((TopPair.ofSubset B).singularHomology S q)
  apply (ModuleCat.mono_iff_injective ι).1 inferInstance
  obtain ⟨c, hc⟩ := (TopPair.singularKronecker_bijective (TopPair.ofSubset B) k (R := S) q).2 ι
  rw [← hc, map_smul]
  simpa only [ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply] using
    singularHomologyCrossRelPair_comp_singularRelativeCap_comp_singularKronecker_apply
      hA hB u c (o ⊗ₜ x)

end TopCat
