/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cup.RelativeKronecker
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import SymplecticGeometry.Algebra.Category.ModuleCat.ULiftTensor
import SymplecticGeometry.AlgebraicTopology.Cohomology.PairChangeOfCoefficients
import TauCeti.AlgebraicTopology.Cohomology.IntegralCup

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
* `TopCat.singularRelativeCap_singularHomologyCrossRelPair_ulift`: the same formula with the
  integral coefficients `ULift ℤ` of Tau Ceti's local orientations and Thom classes.

The integral form takes a class `u` with chain coefficients and values `ULift ℤ`, the cross
product with its coefficients `ULift ℤ ⊗ ULift ℤ` multiplied to `ULift ℤ`
(`ModuleCat.uliftTensorSelfIso`), and the cap product along the right unitor of `ULift ℤ`, as
Tau Ceti caps with fundamental classes. It is reduced to the general formula by the coefficient
naturality of the excisive cap product (`TopCat.singularRelativeCap_coefficient_naturality`),
along the inverse of `ModuleCat.uliftTensorSelfIso` and `TauCeti.integralCoeffIso`. Its
cohomology carries the `ℤ`-linear structure of a preadditive category
(`CategoryTheory.MonoidalPreadditive.monoidalLinearInt`), as Tau Ceti's integral classes do; since
`ModuleCat ℤ` has only one `ℤ`-linear structure (`CategoryTheory.Linear.subsingletonInt`), the
general formula applies to it.

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

section ULift

/-! ### Integral coefficients `ULift ℤ` -/

variable {X Y : TopCat.{0}} {A : Set X} {B : Set Y} (hA : IsOpen A) (hB : IsOpen B) {p q : ℕ}

/-- `TopCat.singularRelativeCap_singularHomologyCrossRelPair` over `ℤ`, for any `ℤ`-linear structure
on `ModuleCat ℤ`: the structures are all equal (`CategoryTheory.Linear.subsingletonInt`), so the
statement for one of them is the statement for `ModuleCat`'s own. -/
private theorem singularRelativeCap_singularHomologyCrossRelPair_of_linearInt
    (L : Linear ℤ (ModuleCat.{0} ℤ)) [MonoidalLinear ℤ (ModuleCat.{0} ℤ)]
    (u : (TopPair.ofSubset A).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) p)
    (o : ((TopPair.ofSubset A).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) p :
      ModuleCat.{0} ℤ))
    (x : ((TopPair.ofSubset B).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) q :
      ModuleCat.{0} ℤ)) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q
        (singularRelativeCap ℤ (𝟙 _) (λ_ _).hom (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
          (isOpen_subtypeVal_preimage_preimage_fst_union hA)
          (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q (p + q) rfl
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p u)
          (singularHomologyCrossRelPair X Y A B (ModuleCat.of ℤ (ULift.{0} ℤ))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) p q (p + q) rfl (o ⊗ₜ x))) =
      ((TopPair.ofSubset A).singularKronecker ℤ p u o : ℤ) • x := by
  obtain rfl : L = ModuleCat.instLinear := Subsingleton.elim _ _
  exact singularRelativeCap_singularHomologyCrossRelPair hA hB u o x

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/-- **Capping a cross product of two pairs with a class of the first factor, with integral
coefficients `ULift ℤ`**, `pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`: for open `A ⊆ X` and
`B ⊆ Y`, a class `u ∈ Hᵖ(X, A; ℤ)` with chain coefficients and values `ULift ℤ`, a class
`o ∈ Hₚ(X, A; ℤ)` and a class `x ∈ H_q(Y, B; ℤ)`, take the homology cross product
`o × x ∈ Hₚ₊q(X × Y, A × Y ∪ X × B; ℤ ⊗ ℤ)` of the pairs with its coefficients multiplied to `ℤ`
by `ModuleCat.uliftTensorSelfIso ℤ`, cap it with the pull-back of `u` along the first projection,
with the cap product of the excisive couple `(A × Y, X × B)` along the right unitor of `ULift ℤ`,
and push forward along the second projection `(X × Y, X × B) ⟶ (Y, B)`. The result is `x`
scaled by the Kronecker pairing `⟨u, o⟩ ∈ ULift ℤ`. The cohomology carries the `ℤ`-linear
structure of a preadditive category, as Tau Ceti's integral classes do. -/
theorem singularRelativeCap_singularHomologyCrossRelPair_ulift
    (u : (TopPair.ofSubset A).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) p)
    (o : ((TopPair.ofSubset A).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) p :
      ModuleCat.{0} ℤ))
    (x : ((TopPair.ofSubset B).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) q :
      ModuleCat.{0} ℤ)) :
    TopPair.singularHomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q
        (singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
          (isOpen_subtypeVal_preimage_preimage_fst_union hA)
          (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q (p + q) rfl
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p u)
          (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
            (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) (p + q)
            (singularHomologyCrossRelPair X Y A B (ModuleCat.of ℤ (ULift.{0} ℤ))
              (ModuleCat.of ℤ (ULift.{0} ℤ)) p q (p + q) rfl (o ⊗ₜ x)))) =
      ((TopPair.ofSubset A).singularKronecker ℤ p u o).down • x := by
  -- The change of coefficients: `T' = ULift ℤ ⟶ ULift ℤ ⊗ ULift ℤ` is the inverse of the
  -- multiplication, `S' = ℤ ⟶ ULift ℤ` and the values `ℤ ⟶ ULift ℤ` are
  -- `TauCeti.integralCoeffIso.inv`.
  have hu : (ModuleCat.uliftTensorSelfIso ℤ).inv ≫ 𝟙 _ =
      (ρ_ (ModuleCat.of ℤ (ULift.{0} ℤ))).inv ≫ (𝟙 _ ⊗ₘ TauCeti.integralCoeffIso.inv) := by
    rw [Category.comp_id, id_tensorHom, ← cancel_mono (ModuleCat.uliftTensorSelfIso ℤ).hom,
      Iso.inv_hom_id, Category.assoc]
    rw [TauCeti.integralCoeffIso_inv_eq_ofHom, ← Category.assoc]
    exact (ModuleCat.rightUnitor_inv_whiskerLeft_uliftTensorSelfIso_hom ℤ).symm
  have hμ : (TauCeti.integralCoeffIso.inv ▷ 𝟙_ (ModuleCat.{0} ℤ)) ≫ (ρ_ _).hom =
      (𝟙_ (ModuleCat.{0} ℤ) ◁ TauCeti.integralCoeffIso.inv) ≫ (λ_ _).hom ≫ 𝟙 _ := by
    rw [Category.comp_id, rightUnitor_naturality, leftUnitor_naturality]
    exact congrArg (· ≫ TauCeti.integralCoeffIso.inv) (unitors_equal (C := ModuleCat.{0} ℤ)).symm
  have hcap := singularRelativeCap_coefficient_naturality ℤ (𝟙 _) (ρ_ _).inv (λ_ _).hom
    (ρ_ _).hom (𝟙 _) TauCeti.integralCoeffIso.inv (ModuleCat.uliftTensorSelfIso ℤ).inv
    TauCeti.integralCoeffIso.inv (𝟙 _) hu hμ _ _
    (isOpen_subtypeVal_preimage_preimage_fst_union hA)
    (isOpen_subtypeVal_preimage_preimage_snd_union hB) p q (p + q) rfl
    (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p
      ((TopPair.ofSubset A).singularCohomologyValueMap _ ℤ TauCeti.integralCoeffIso.hom p u))
  -- Changing the values of `pr₁^* u` to `ℤ` and back gives `pr₁^* u`.
  have hα : HomologicalComplex.homologyMap
      ((TauCeti.ChainComplex.linearYonedaFunctor ℤ (𝟙_ (ModuleCat.{0} ℤ))).map
        (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map (𝟙 _)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A)))).op ≫
        ((TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplex _).linearYonedaObjMap ℤ
          TauCeti.integralCoeffIso.inv) p
      (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p
        ((TopPair.ofSubset A).singularCohomologyValueMap _ ℤ TauCeti.integralCoeffIso.hom p u)) =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p
        u := by
    have h1 : HomologicalComplex.homologyMap
        ((TauCeti.ChainComplex.linearYonedaFunctor ℤ (𝟙_ (ModuleCat.{0} ℤ))).map
          (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
            (𝟙 (ModuleCat.of ℤ (ULift.{0} ℤ)))).app
              (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A)))).op ≫
          ((TopPair.ofSubset (fst X Y ⁻¹' A)).singularChainComplex _).linearYonedaObjMap ℤ
            TauCeti.integralCoeffIso.inv) p =
        (TopPair.ofSubset (fst X Y ⁻¹' A)).singularCohomologyValueMap
          (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ TauCeti.integralCoeffIso.inv p := by
      simp
    have h2 : TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A)).singularCohomologyValueMap
          (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ TauCeti.integralCoeffIso.hom p ≫
        (TopPair.ofSubset (fst X Y ⁻¹' A)).singularCohomologyValueMap
          (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ TauCeti.integralCoeffIso.inv p =
        TopPair.singularCohomologyMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p := by
      rw [← TopPair.singularCohomologyValueMap_comp, Iso.hom_inv_id,
        TopPair.singularCohomologyValueMap_id, Category.comp_id]
    rw [← Category.assoc, TopPair.singularCohomologyValueMap_naturality] at h2
    rw [h1]
    conv_rhs => rw [← h2]
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    -- The two sides differ only in instance arguments, which `rw` does not unfold.
    with_reducible_and_instances rfl
  -- The multiplication of the homology coefficients and its inverse cancel.
  have hc : ∀ z, HomologicalComplex.homologyMap
      (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).inv).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) (p + q)
      (HomologicalComplex.homologyMap
        (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B))))
        (p + q) z) = z := fun z ↦ by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, ← NatTrans.comp_app,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      HomologicalComplex.homologyMap_id, ModuleCat.id_apply]
  have he : HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
      (𝟙 (ModuleCat.of ℤ (ULift.{0} ℤ)))).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset (snd X Y ⁻¹' B)))) q = 𝟙 _ := by
    simp
  rw [← hα, hcap, he, Category.comp_id, ModuleCat.comp_apply, hc,
    singularRelativeCap_singularHomologyCrossRelPair_of_linearInt hA hB,
    TopPair.singularKronecker_def, TauCeti.ChainComplex.kronecker_coefficient_naturality,
    ModuleCat.comp_apply, TauCeti.integralCoeffIso_hom_apply, TopPair.singularKronecker_def]
  exact int_smul_eq_zsmul _ _ _

end ULift

end TopCat
