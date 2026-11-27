/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.ShuffleAssoc
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import SymplecticGeometry.Algebra.Category.ModuleCat.ULiftTensor
import SymplecticGeometry.Algebra.Homology.Monoidal.HomologyCrossHomotopy
import SymplecticGeometry.Algebra.Homology.Monoidal.SplitMono
import SymplecticGeometry.AlgebraicTopology.Singular.PairChangeOfCoefficients
import SymplecticGeometry.Algebra.Homology.Monoidal.Abelian
import SymplecticGeometry.Algebra.Homology.Homotopy.DescCokernel

/-!
# Associativity of the homology cross product of pairs

For subsets `A ⊆ X`, `B ⊆ Y` and `D ⊆ Z` of topological spaces, the homology cross product of
pairs `TopCat.singularHomologyCrossRelPair` is associative
(`TopCat.singularHomologyCrossRelPair_assoc`): for `a ∈ Hₚ(X, A; R)`, `b ∈ H_q(Y, B; S)` and
`c ∈ H_r(Z, D; T)`, the map induced by the coefficient associator `(R ⊗ S) ⊗ T ≅ R ⊗ (S ⊗ T)`
and by the associator `(X × Y) × Z ≅ X × (Y × Z)`, a map of pairs
(`TopCat.mapsTo_associator_hom_preimage_union`), sends `(a × b) × c` to `a × (b × c)`, with no
sign. For a coefficient object `R` with an associative multiplication `μ : R ⊗ R ⟶ R`, applied
after each cross product, the same holds without the coefficient associator
(`TopCat.singularHomologyCrossRelPair_mul_assoc`), by the naturality of the cross product of
pairs in the coefficients (`TopCat.singularHomologyCrossRelPair_coefficient_naturality`). With
coefficients in `ULift ℤ` and the multiplication of `ModuleCat.uliftTensorSelfIso`, this is
`TopCat.singularHomologyCrossRelPair_uliftTensorSelfIso_assoc`.

Tau Ceti proves the absolute statement `TopCat.singularHomologyCross_assoc` by cancelling the
isomorphism that the Alexander–Whitney map induces on homology. For pairs that argument would need
the relative Eilenberg–Zilber theorem `TopCat.quasiIso_shufflePair` of Tau Ceti's
`Singular/Kunneth/Pair.lean`. Here, instead, the two iterated shuffle maps are compared at chain
level. The natural homotopy `SSet.shuffleAssocHomotopy` between them,
transported to singular chains along the lax monoidal structure of `TopCat.toSSet`, is
`TopCat.shuffleAssocHomotopy`, natural in the three spaces. By this naturality along the
inclusions of `A`, `B` and `D`, the homotopy followed by the projection to the relative chains
vanishes on the chains of the three pieces of the subspace, so it descends to the tensor product
of the relative chains, one factor at a time, as `TopCat.shufflePair` is built: in the first two
factors by `Homotopy.descCokernel₂`, then in the third by `Homotopy.descCokernel`. This is
`TopCat.shufflePairAssocHomotopy`. On homology, the associativity of the algebraic cross product
and its naturality conclude
(`HomologicalComplex.homologyCross_homologyMap_assoc_of_homotopy`).

The descent of the homotopy follows that of `TopCat.shuffleAlexanderWhitneyPairHomotopy`
(`Singular/Kunneth/RelativePair.lean`), and the homology step follows the proof of Tau Ceti's
`TopCat.singularHomologyCross_assoc` (`TauCeti/AlgebraicTopology/Singular/CrossProduct.lean`),
with the homotopy in place of the Alexander–Whitney map.

## Main definitions

* `TopCat.shuffleAssocHomotopy`: the chain homotopy between the two iterated shuffle maps of
  spaces.
* `TopCat.shufflePairAssocHomotopy`: the chain homotopy between the two iterated shuffle maps of
  pairs.

## Main results

* `TopCat.shuffleAssocHomotopy_hom_naturality`: the homotopy of spaces is natural.
* `TopCat.singularHomologyCrossRelPair_assoc`: associativity of the cross product of pairs.
* `TopCat.singularHomologyCrossRelPair_mul_assoc`: the same, followed by an associative
  multiplication of the coefficients.
* `TopCat.singularHomologyCrossRelPair_uliftTensorSelfIso_assoc`: the same with coefficients in
  `ULift ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the cross product and its associativity.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Absolute

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y Z : TopCat.{w}) (R S T : C)

/-- The comparison of the two composites of lax monoidal structure maps of `toSSet`. -/
private lemma shuffle_whiskerRight_shuffle_eq :
    (shuffle X Y R S ▷ (toSSet.obj Z).chainComplex T) ≫ shuffle (X ⊗ Y) Z (R ⊗ S) T ≫
        ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫
          SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ (S ⊗ T)) =
      ((SSet.shuffle (toSSet.obj X) (toSSet.obj Y) R S ▷ (toSSet.obj Z).chainComplex T) ≫
        SSet.shuffle (toSSet.obj X ⊗ toSSet.obj Y) (toSSet.obj Z) (R ⊗ S) T ≫
        ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app
          ((toSSet.obj X ⊗ toSSet.obj Y) ⊗ toSSet.obj Z) ≫
        SSet.chainComplexMap (α_ (toSSet.obj X) (toSSet.obj Y) (toSSet.obj Z)).hom
          (R ⊗ (S ⊗ T))) ≫
      SSet.chainComplexMap (toSSet.obj X ◁ Functor.LaxMonoidal.μ toSSet Y Z ≫
        Functor.LaxMonoidal.μ toSSet X (Y ⊗ Z)) (R ⊗ (S ⊗ T)) := by
  have h₁ : (SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S) ▷
        (toSSet.obj Z).chainComplex T) ≫
        SSet.shuffle (toSSet.obj (X ⊗ Y)) (toSSet.obj Z) (R ⊗ S) T =
      SSet.shuffle (toSSet.obj X ⊗ toSSet.obj Y) (toSSet.obj Z) (R ⊗ S) T ≫
        SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y ▷ toSSet.obj Z) ((R ⊗ S) ⊗ T) := by
    have := SSet.shuffle_naturality (R := R ⊗ S) (S := T) (Functor.LaxMonoidal.μ toSSet X Y)
      (𝟙 (toSSet.obj Z))
    rwa [SSet.chainComplexMap_id, tensorHom_id, tensorHom_id] at this
  have h₂ := Functor.LaxMonoidal.associativity toSSet X Y Z
  simp only [shuffle_def, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% h₁]
  congr 2
  rw [← Functor.map_comp_assoc, NatTrans.naturality_assoc, ← Functor.map_comp,
    ← Functor.map_comp, Category.assoc, h₂]

/-- The second iterated shuffle map of spaces is that of the singular simplicial sets, followed by
the lax monoidal structure maps of `toSSet`. -/
private lemma whiskerLeft_shuffle_shuffle_eq :
    (α_ _ _ _).hom ≫ ((toSSet.obj X).chainComplex R ◁ shuffle Y Z S T) ≫
        shuffle X (Y ⊗ Z) R (S ⊗ T) =
      ((α_ _ _ _).hom ≫ ((toSSet.obj X).chainComplex R ◁
          SSet.shuffle (toSSet.obj Y) (toSSet.obj Z) S T) ≫
        SSet.shuffle (toSSet.obj X) (toSSet.obj Y ⊗ toSSet.obj Z) R (S ⊗ T)) ≫
      SSet.chainComplexMap (toSSet.obj X ◁ Functor.LaxMonoidal.μ toSSet Y Z ≫
        Functor.LaxMonoidal.μ toSSet X (Y ⊗ Z)) (R ⊗ (S ⊗ T)) := by
  have h₁ : ((toSSet.obj X).chainComplex R ◁
        SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet Y Z) (S ⊗ T)) ≫
        SSet.shuffle (toSSet.obj X) (toSSet.obj (Y ⊗ Z)) R (S ⊗ T) =
      SSet.shuffle (toSSet.obj X) (toSSet.obj Y ⊗ toSSet.obj Z) R (S ⊗ T) ≫
        SSet.chainComplexMap (toSSet.obj X ◁ Functor.LaxMonoidal.μ toSSet Y Z) (R ⊗ (S ⊗ T)) := by
    have := SSet.shuffle_naturality (R := R) (S := S ⊗ T) (𝟙 (toSSet.obj X))
      (Functor.LaxMonoidal.μ toSSet Y Z)
    rwa [SSet.chainComplexMap_id, id_tensorHom, id_tensorHom] at this
  simp only [shuffle_def, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp]

/-- **Associativity of the shuffle map of spaces up to a natural homotopy.** The two iterated
shuffle maps `(C(X; R) ⊗ C(Y; S)) ⊗ C(Z; T) ⟶ C(X × (Y × Z); R ⊗ (S ⊗ T))` are chain homotopic:
the shuffle map of `X × Y` followed by that of `(X × Y) × Z`, the coefficient associator and the
map induced by the associator `(X × Y) × Z ≅ X × (Y × Z)`, and the associator of chain complexes
followed by the shuffle map of `Y × Z` and that of `X × (Y × Z)`. The homotopy is natural in the
three spaces (`TopCat.shuffleAssocHomotopy_hom_naturality`). -/
def shuffleAssocHomotopy :
    _root_.Homotopy ((shuffle X Y R S ▷ (toSSet.obj Z).chainComplex T) ≫
        shuffle (X ⊗ Y) Z (R ⊗ S) T ≫
          ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫
            SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ (S ⊗ T)))
      ((α_ ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S)
          ((toSSet.obj Z).chainComplex T)).hom ≫ ((toSSet.obj X).chainComplex R ◁ shuffle Y Z S T) ≫
        shuffle X (Y ⊗ Z) R (S ⊗ T)) :=
  (_root_.Homotopy.ofEq (shuffle_whiskerRight_shuffle_eq X Y Z R S T)).trans <|
    ((SSet.shuffleAssocHomotopy (toSSet.obj X) (toSSet.obj Y) (toSSet.obj Z) R S T).compRight
      _).trans (_root_.Homotopy.ofEq (whiskerLeft_shuffle_shuffle_eq X Y Z R S T).symm)

/-- The homotopy `TopCat.shuffleAssocHomotopy` is that of the singular simplicial sets, followed
by the lax monoidal structure maps of `toSSet`. -/
lemma shuffleAssocHomotopy_hom (i j : ℕ) :
    (shuffleAssocHomotopy X Y Z R S T).hom i j =
      (SSet.shuffleAssocHomotopy (toSSet.obj X) (toSSet.obj Y) (toSSet.obj Z) R S T).hom i j ≫
        (SSet.chainComplexMap (toSSet.obj X ◁ Functor.LaxMonoidal.μ toSSet Y Z ≫
          Functor.LaxMonoidal.μ toSSet X (Y ⊗ Z)) (R ⊗ (S ⊗ T))).f j := by
  simp [shuffleAssocHomotopy]

variable {X Y Z} in
/-- The homotopy of `TopCat.shuffleAssocHomotopy` is natural in the three spaces: continuous maps
`f : X ⟶ X'`, `g : Y ⟶ Y'` and `h : Z ⟶ Z'` intertwine it with the homotopy for `X'`, `Y'` and
`Z'`, the chains of the target being mapped by `f × (g × h)`. -/
@[reassoc]
lemma shuffleAssocHomotopy_hom_naturality {X' Y' Z' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (h : Z ⟶ Z') (i j : ℕ) :
    ((SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ⊗ₘ
        SSet.chainComplexMap (toSSet.map h) T).f i ≫
        (shuffleAssocHomotopy X' Y' Z' R S T).hom i j =
      (shuffleAssocHomotopy X Y Z R S T).hom i j ≫
        (SSet.chainComplexMap (toSSet.map (f ⊗ₘ (g ⊗ₘ h))) (R ⊗ (S ⊗ T))).f j := by
  have hμ : (toSSet.map f ⊗ₘ (toSSet.map g ⊗ₘ toSSet.map h)) ≫
      (toSSet.obj X' ◁ Functor.LaxMonoidal.μ toSSet Y' Z') ≫
        Functor.LaxMonoidal.μ toSSet X' (Y' ⊗ Z') =
      ((toSSet.obj X ◁ Functor.LaxMonoidal.μ toSSet Y Z) ≫
        Functor.LaxMonoidal.μ toSSet X (Y ⊗ Z)) ≫ toSSet.map (f ⊗ₘ (g ⊗ₘ h)) := by
    rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, tensorHom_comp_whiskerLeft_assoc,
      Functor.LaxMonoidal.μ_natural, whiskerLeft_comp_tensorHom_assoc]
  rw [shuffleAssocHomotopy_hom, shuffleAssocHomotopy_hom,
    SSet.shuffleAssocHomotopy_hom_naturality_assoc, Category.assoc, SSet.chainComplexMap_f_comp,
    SSet.chainComplexMap_f_comp, hμ]

end Absolute

section Relative

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

open scoped ChainComplex

variable (X Y Z : TopCat.{w}) (A : Set X) (B : Set Y) (D : Set Z)

/-- The associator `(X × Y) × Z ≅ X × (Y × Z)` carries the subspace
`((A × Y ∪ X × B) × Z) ∪ (X × Y) × D` of the product of three pairs to
`A × (Y × Z) ∪ X × (B × Z ∪ Y × D)`. -/
theorem mapsTo_associator_hom_preimage_union :
    Set.MapsTo (α_ X Y Z).hom
      (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)
      (fst X (Y ⊗ Z) ⁻¹' A ∪ snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)) := by
  rintro ⟨⟨x, y⟩, z⟩ h
  -- the associator sends `((x, y), z)` to `(x, (y, z))`, and the projections read off the
  -- components, by definition
  exact h.elim (fun h ↦ h.elim Or.inl fun h ↦ Or.inr (Or.inl h)) fun h ↦ Or.inr (Or.inr h)

variable (R S T : C)

/-- On `(C(X; R) ⊗ C(Y; S)) ⊗ C(Z; T)`, the first iterated shuffle map of the pairs, followed by
the coefficient associator and the associator of the spaces, is the first iterated shuffle map
of the spaces followed by the projection to the relative chains. -/
private theorem singularChainComplexπ_tensorHom_shufflePair_assoc_left :
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ TopPair.singularChainComplexπOfSubset S B) ⊗ₘ
          TopPair.singularChainComplexπOfSubset T D) ≫
      (shufflePair X Y A B R S ▷ (TopPair.ofSubset D).singularChainComplex T) ≫
        shufflePair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T ≫
          ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
              snd (X ⊗ Y) Z ⁻¹' D))) ≫
            TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
              (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)) =
      ((shuffle X Y R S ▷ (toSSet.obj Z).chainComplex T) ≫ shuffle (X ⊗ Y) Z (R ⊗ S) T ≫
        ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫
          SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ (S ⊗ T))) ≫
        TopPair.singularChainComplexπOfSubset (R ⊗ (S ⊗ T))
          (fst X (Y ⊗ Z) ⁻¹' A ∪ snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)) := by
  rw [tensorHom_comp_whiskerRight_assoc,
    singularChainComplexπOfSubset_tensorHom_singularChainComplexπOfSubset_shufflePair,
    ← whiskerRight_comp_tensorHom_assoc,
    singularChainComplexπOfSubset_tensorHom_singularChainComplexπOfSubset_shufflePair_assoc,
    ← TopPair.singularChainComplexπOfSubset_coefficient_naturality_assoc,
    ← TopPair.singularChainComplexπOfSubset_naturality]
  simp only [Category.assoc]

/-- On `(C(X; R) ⊗ C(Y; S)) ⊗ C(Z; T)`, the second iterated shuffle map of the pairs is the second
iterated shuffle map of the spaces followed by the projection to the relative chains. -/
private theorem singularChainComplexπ_tensorHom_shufflePair_assoc_right :
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ TopPair.singularChainComplexπOfSubset S B) ⊗ₘ
          TopPair.singularChainComplexπOfSubset T D) ≫
      (α_ ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplex S)
        ((TopPair.ofSubset D).singularChainComplex T)).hom ≫
        ((TopPair.ofSubset A).singularChainComplex R ◁ shufflePair Y Z B D S T) ≫
          shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T) =
      ((α_ ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S)
          ((toSSet.obj Z).chainComplex T)).hom ≫
        ((toSSet.obj X).chainComplex R ◁ shuffle Y Z S T) ≫ shuffle X (Y ⊗ Z) R (S ⊗ T)) ≫
        TopPair.singularChainComplexπOfSubset (R ⊗ (S ⊗ T))
          (fst X (Y ⊗ Z) ⁻¹' A ∪ snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)) := by
  rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc,
    singularChainComplexπOfSubset_tensorHom_singularChainComplexπOfSubset_shufflePair,
    ← whiskerLeft_comp_tensorHom_assoc,
    singularChainComplexπOfSubset_tensorHom_singularChainComplexπOfSubset_shufflePair]
  simp only [Category.assoc]

/-- The homotopy `TopCat.shuffleAssocHomotopy`, followed by the projection to the relative chains
of the product of the three pairs, vanishes on the chains of `X' × (Y' × Z')` for maps `f`, `g`,
`h` whose product lands in the subspace. -/
private theorem shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero {X' Y' Z' : TopCat.{w}}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z)
    (hfgh : Set.range (f ⊗ₘ (g ⊗ₘ h)) ⊆
      fst X (Y ⊗ Z) ⁻¹' A ∪ snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)) (i j : ℕ) :
    ((SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map g) S) ⊗ₘ
        SSet.chainComplexMap (toSSet.map h) T).f i ≫
      (shuffleAssocHomotopy X Y Z R S T).hom i j ≫
        (TopPair.singularChainComplexπOfSubset (R ⊗ (S ⊗ T)) (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).f j = 0 := by
  rw [shuffleAssocHomotopy_hom_naturality_assoc, ← comp_f,
    TopPair.chainComplexMap_comp_singularChainComplexπOfSubset_eq_zero_of_range_subset _ hfgh,
    zero_f, comp_zero]

/-- The first iterated shuffle map of the three pairs, followed by the coefficient associator and
the map induced by the associator of the spaces. -/
private abbrev shufflePairAssocLeft :
    ((TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S) ⊗
        (TopPair.ofSubset D).singularChainComplex T ⟶
      (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
        snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplex (R ⊗ (S ⊗ T)) :=
  (shufflePair X Y A B R S ▷ (TopPair.ofSubset D).singularChainComplex T) ≫
    shufflePair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T ≫
      ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
        (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
          snd (X ⊗ Y) Z ⁻¹' D))) ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
          (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T))

/-- The second iterated shuffle map of the three pairs. -/
private abbrev shufflePairAssocRight :
    ((TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S) ⊗
        (TopPair.ofSubset D).singularChainComplex T ⟶
      (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
        snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplex (R ⊗ (S ⊗ T)) :=
  (α_ ((TopPair.ofSubset A).singularChainComplex R) ((TopPair.ofSubset B).singularChainComplex S)
      ((TopPair.ofSubset D).singularChainComplex T)).hom ≫
    ((TopPair.ofSubset A).singularChainComplex R ◁ shufflePair Y Z B D S T) ≫
      shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T)

/-- The short complex `(C(A) ⊗ C(Y)) ⊗ C(Z) ⟶ (C(X) ⊗ C(Y)) ⊗ C(Z) ⟶ (C(X, A) ⊗ C(Y)) ⊗ C(Z)`. -/
private abbrev shortComplex₁ (Y' : TopCat.{w}) : ShortComplex (ChainComplex C ℕ) :=
  tensorRightShortComplex ((toSSet.obj Z).chainComplex T)
    (tensorRightShortComplex ((toSSet.obj Y').chainComplex S)
      ((TopPair.ofSubset A).singularChainComplexShortComplex R))

/-- The short complex
`(C(X, A) ⊗ C(B)) ⊗ C(Z) ⟶ (C(X, A) ⊗ C(Y)) ⊗ C(Z) ⟶ (C(X, A) ⊗ C(Y, B)) ⊗ C(Z)`. -/
private abbrev shortComplex₂ (Z' : TopCat.{w}) : ShortComplex (ChainComplex C ℕ) :=
  tensorRightShortComplex ((toSSet.obj Z').chainComplex T)
    (tensorLeftShortComplex ((TopPair.ofSubset A).singularChainComplex R)
      ((TopPair.ofSubset B).singularChainComplexShortComplex S))

/-- The short complex
`(C(X, A) ⊗ C(Y, B)) ⊗ C(D) ⟶ (C(X, A) ⊗ C(Y, B)) ⊗ C(Z) ⟶ (C(X, A) ⊗ C(Y, B)) ⊗ C(Z, D)`. -/
private abbrev shortComplex₃ : ShortComplex (ChainComplex C ℕ) :=
  tensorLeftShortComplex
    ((TopPair.ofSubset A).singularChainComplex R ⊗ (TopPair.ofSubset B).singularChainComplex S)
    ((TopPair.ofSubset D).singularChainComplexShortComplex T)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
private theorem shortExact_shortComplex₁ (Y' : TopCat.{w}) :
    (shortComplex₁ X Z A R S T Y').ShortExact := by
  have (q : ℕ) : IsSplitMono (Hom.f (𝟙 ((toSSet.obj Y').chainComplex S)) q) := by
    rw [id_f]
    infer_instance
  have (p : ℕ) := isSplitMono_tensorHom_f
    ((TopPair.ofSubset A).singularChainComplexShortComplex R).f
    (𝟙 ((toSSet.obj Y').chainComplex S)) p
  exact shortExact_tensorRightShortComplex _ _
    (shortExact_tensorRightShortComplex_singularChainComplexShortComplex X Y' A R S)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
private theorem shortExact_shortComplex₂ (Z' : TopCat.{w}) :
    (shortComplex₂ X Y A B R S T Z').ShortExact := by
  have (q : ℕ) : IsSplitMono (Hom.f (𝟙 ((TopPair.ofSubset A).singularChainComplex R)) q) := by
    rw [id_f]
    infer_instance
  have (p : ℕ) := isSplitMono_tensorHom_f (𝟙 ((TopPair.ofSubset A).singularChainComplex R))
    ((TopPair.ofSubset B).singularChainComplexShortComplex S).f p
  exact shortExact_tensorRightShortComplex _ _
    (shortExact_tensorLeftShortComplex_singularChainComplexShortComplex X Y A B R S)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
private theorem shortExact_shortComplex₃ :
    (shortComplex₃ X Y Z A B D R S T).ShortExact :=
  shortExact_tensorLeftShortComplex _
    ((TopPair.ofSubset D).shortExact_singularChainComplexShortComplex T)

omit [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)] in
/-- The three projections of the descent compose to the projection
`(C(X) ⊗ C(Y)) ⊗ C(Z) ⟶ (C(X, A) ⊗ C(Y, B)) ⊗ C(Z, D)`. -/
@[reassoc]
private theorem singularChainComplexπ_tensorHom_id_comp_id_tensorHom_singularChainComplexπ_comp :
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
        𝟙 ((toSSet.obj Z).chainComplex T)) ≫
      ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
          TopPair.singularChainComplexπOfSubset S B) ⊗ₘ 𝟙 ((toSSet.obj Z).chainComplex T)) ≫
        (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
          (TopPair.ofSubset B).singularChainComplex S) ⊗ₘ
          TopPair.singularChainComplexπOfSubset T D) =
      (TopPair.singularChainComplexπOfSubset R A ⊗ₘ TopPair.singularChainComplexπOfSubset S B) ⊗ₘ
        TopPair.singularChainComplexπOfSubset T D := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- The first two steps of the descent of `TopCat.shuffleAssocHomotopy`: to
`(C(X, A) ⊗ C(Y, B)) ⊗ C(Z)`, along the projections in the first and in the second factor. -/
private def shufflePairAssocHomotopy₁₂ :
    _root_.Homotopy
      ((𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
          (TopPair.ofSubset B).singularChainComplex S) ⊗ₘ
          TopPair.singularChainComplexπOfSubset T D) ≫
        shufflePairAssocLeft X Y Z A B D R S T)
      ((𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
          (TopPair.ofSubset B).singularChainComplex S) ⊗ₘ
          TopPair.singularChainComplexπOfSubset T D) ≫
        shufflePairAssocRight X Y Z A B D R S T) :=
  have hS₁ := shortExact_shortComplex₁ X Z A R S T Y
  have hS₂ := shortExact_shortComplex₂ X Y A B R S T Z
  -- the maps of the short exact sequences, written through `TopPair.ιOfSubset` and
  -- `TopPair.singularChainComplexπOfSubset`, so that the conditions below hold by `rw`
  _root_.Homotopy.descCokernel₂ (shuffleAssocHomotopy X Y Z R S T)
    (TopPair.singularChainComplexπOfSubset (R ⊗ (S ⊗ T)) (fst X (Y ⊗ Z) ⁻¹' A ∪
      snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)))
    ((SSet.chainComplexMap (toSSet.map (TopPair.ιOfSubset A)) R ⊗ₘ
      𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ 𝟙 ((toSSet.obj Z).chainComplex T))
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
      𝟙 ((toSSet.obj Z).chainComplex T)) _
    (fun i ↦ (hS₁.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    (fun i j ↦ by
      have h := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (TopPair.ιOfSubset A) (𝟙 Y) (𝟙 Z) (by rintro _ ⟨x, rfl⟩; exact Or.inl x.1.property) i j
      simp only [CategoryTheory.Functor.map_id] at h
      exact h)
    ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      SSet.chainComplexMap (toSSet.map (TopPair.ιOfSubset B)) S) ⊗ₘ
        𝟙 ((toSSet.obj Z).chainComplex T))
    ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
      TopPair.singularChainComplexπOfSubset S B) ⊗ₘ 𝟙 ((toSSet.obj Z).chainComplex T)) _
    (fun i ↦ (hS₂.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ
      𝟙 ((toSSet.obj (TopPair.ofSubset B).snd).chainComplex S)) ⊗ₘ
        𝟙 ((toSSet.obj Z).chainComplex T))
    (fun i ↦ ((shortExact_shortComplex₁ X Z A R S T (TopPair.ofSubset B).snd).map_of_exact
      (HomologicalComplex.eval C _ i)).epi_g)
    ((𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
      SSet.chainComplexMap (toSSet.map (TopPair.ιOfSubset B)) S) ⊗ₘ
        𝟙 ((toSSet.obj Z).chainComplex T))
    (by simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id])
    (fun i j ↦ by
      -- the vanishing of `TopCat.shuffleAssocHomotopy` on the chains of `X × (B × Z)`
      have h := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (𝟙 X) (TopPair.ιOfSubset B) (𝟙 Z)
        (by rintro _ ⟨x, rfl⟩; exact Or.inr (Or.inl x.2.1.property)) i j
      simp only [CategoryTheory.Functor.map_id] at h
      exact h)
    (by rw [singularChainComplexπ_tensorHom_id_comp_id_tensorHom_singularChainComplexπ_comp_assoc,
      singularChainComplexπ_tensorHom_shufflePair_assoc_left])
    (by rw [singularChainComplexπ_tensorHom_id_comp_id_tensorHom_singularChainComplexπ_comp_assoc,
      singularChainComplexπ_tensorHom_shufflePair_assoc_right])

/-- The homotopy `shufflePairAssocHomotopy₁₂` is the homotopy `TopCat.shuffleAssocHomotopy`,
descended. -/
private theorem singularChainComplexπ_f_shufflePairAssocHomotopy₁₂_hom (i j : ℕ) :
    ((TopPair.singularChainComplexπOfSubset R A ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
        𝟙 ((toSSet.obj Z).chainComplex T)).f i ≫
      ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
        TopPair.singularChainComplexπOfSubset S B) ⊗ₘ 𝟙 ((toSSet.obj Z).chainComplex T)).f i ≫
        (shufflePairAssocHomotopy₁₂ X Y Z A B D R S T).hom i j =
      (shuffleAssocHomotopy X Y Z R S T).hom i j ≫
        (TopPair.singularChainComplexπOfSubset (R ⊗ (S ⊗ T)) (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).f j :=
  _root_.Homotopy.π_π_descCokernel₂_hom ..

/-- **Associativity of the shuffle map of pairs up to homotopy.** For subsets `A ⊆ X`, `B ⊆ Y`
and `D ⊆ Z`, the two iterated shuffle maps
`(C(X, A; R) ⊗ C(Y, B; S)) ⊗ C(Z, D; T) ⟶ C(X × (Y × Z), A × (Y × Z) ∪ X × (B × Z ∪ Y × D))`
are chain homotopic: the shuffle map of the pairs `(X, A)` and `(Y, B)`, followed by that of the
product pair with `(Z, D)`, the coefficient associator and the map of pairs induced by the
associator of the spaces, and the associator of chain complexes followed by the shuffle map of
`(Y, B)` and `(Z, D)` and that of `(X, A)` with the product pair. -/
def shufflePairAssocHomotopy :
    _root_.Homotopy
      ((shufflePair X Y A B R S ▷ (TopPair.ofSubset D).singularChainComplex T) ≫
        shufflePair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T ≫
          ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
              snd (X ⊗ Y) Z ⁻¹' D))) ≫
            TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
              (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)))
      ((α_ ((TopPair.ofSubset A).singularChainComplex R)
          ((TopPair.ofSubset B).singularChainComplex S)
          ((TopPair.ofSubset D).singularChainComplex T)).hom ≫
        ((TopPair.ofSubset A).singularChainComplex R ◁ shufflePair Y Z B D S T) ≫
          shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T)) :=
  have hS := shortExact_shortComplex₃ X Y Z A B D R S T
  -- the maps of the short exact sequence, written as in `shufflePairAssocHomotopy₁₂`
  _root_.Homotopy.descCokernel (shufflePairAssocHomotopy₁₂ X Y Z A B D R S T)
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
      (TopPair.ofSubset B).singularChainComplex S) ⊗ₘ
      SSet.chainComplexMap (toSSet.map (TopPair.ιOfSubset D)) T)
    (𝟙 ((TopPair.ofSubset A).singularChainComplex R ⊗
      (TopPair.ofSubset B).singularChainComplex S) ⊗ₘ
      TopPair.singularChainComplexπOfSubset T D)
    (𝟙 _) _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    (fun i j ↦ by
      -- After the epimorphism `(C(X) ⊗ C(Y)) ⊗ C(D) ⟶ (C(X, A) ⊗ C(Y, B)) ⊗ C(D)`, this is the
      -- vanishing of `TopCat.shuffleAssocHomotopy` on the chains of `X × (Y × D)`.
      have : Epi (((TopPair.singularChainComplexπOfSubset R A ⊗ₘ
          𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
            𝟙 ((toSSet.obj (TopPair.ofSubset D).snd).chainComplex T)).f i ≫
          ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
            TopPair.singularChainComplexπOfSubset S B) ⊗ₘ
              𝟙 ((toSSet.obj (TopPair.ofSubset D).snd).chainComplex T)).f i) :=
        @epi_comp _ _ _ _ _ _
          ((shortExact_shortComplex₁ X (TopPair.ofSubset D).snd A R S T Y).map_of_exact
            (HomologicalComplex.eval C _ i)).epi_g _
          ((shortExact_shortComplex₂ X Y A B R S T (TopPair.ofSubset D).snd).map_of_exact
            (HomologicalComplex.eval C _ i)).epi_g
      refine (cancel_epi (((TopPair.singularChainComplexπOfSubset R A ⊗ₘ
          𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
            𝟙 ((toSSet.obj (TopPair.ofSubset D).snd).chainComplex T)).f i ≫
          ((𝟙 ((TopPair.ofSubset A).singularChainComplex R) ⊗ₘ
            TopPair.singularChainComplexπOfSubset S B) ⊗ₘ
              𝟙 ((toSSet.obj (TopPair.ofSubset D).snd).chainComplex T)).f i)).1 ?_
      have e₁ {K₁ K₂ K₃ L₁ L₂ L₃ : ChainComplex C ℕ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
          (f₃ : K₃ ⟶ L₃) :
          ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 K₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 K₃) ≫ (𝟙 (L₁ ⊗ L₂) ⊗ₘ f₃) =
            ((𝟙 K₁ ⊗ₘ 𝟙 K₂) ⊗ₘ f₃) ≫ ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 L₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 L₃) := by
        simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      have h := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (𝟙 X) (𝟙 Y) (TopPair.ιOfSubset D)
        (by rintro _ ⟨x, rfl⟩; exact Or.inr (Or.inr x.2.2.property)) i j
      simp only [CategoryTheory.Functor.map_id] at h
      rw [id_f, Category.comp_id, ← comp_f, ← comp_f_assoc, Category.assoc, e₁, comp_f, comp_f,
        Category.assoc, Category.assoc, singularChainComplexπ_f_shufflePairAssocHomotopy₁₂_hom, h,
        comp_zero])
    (Category.comp_id _).symm (Category.comp_id _).symm

variable [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft T)]
  [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight T)]
  (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n)

/-- **Associativity of the homology cross product of pairs.** For subsets `A ⊆ X`, `B ⊆ Y` and
`D ⊆ Z` and classes `a ∈ Hₚ(X, A; R)`, `b ∈ H_q(Y, B; S)` and `c ∈ H_r(Z, D; T)`, the map
induced by the coefficient associator `(R ⊗ S) ⊗ T ≅ R ⊗ (S ⊗ T)` and by the associator
`(X × Y) × Z ≅ X × (Y × Z)`, a map of pairs, sends `(a × b) × c` to `a × (b × c)`, with no
sign. -/
@[reassoc]
theorem singularHomologyCrossRelPair_assoc :
    singularHomologyCrossRelPair X Y A B R S p q pq hpq ▷
        (TopPair.ofSubset D).singularHomology T r ≫
      singularHomologyCrossRelPair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T
          pq r n hn ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
            snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (α_ X Y Z).hom
            (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)) n =
      (α_ _ _ _).hom ≫
        (TopPair.ofSubset A).singularHomology R p ◁
          singularHomologyCrossRelPair Y Z B D S T q r qr hqr ≫
        singularHomologyCrossRelPair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T)
          p qr n hn' := by
  have := homologyCross_homologyMap_assoc_of_homotopy (shufflePair X Y A B R S)
    (shufflePair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T ≫
      ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
        (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
          snd (X ⊗ Y) Z ⁻¹' D))) ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
          (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)))
    (shufflePair Y Z B D S T) (shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T))
    (shufflePairAssocHomotopy X Y Z A B D R S T) p q r pq qr n hpq hqr hn hn'
  simp only [homologyMap_comp] at this
  simp only [singularHomologyCrossRelPair_def, Category.assoc]
  exact this

variable {R} in
/-- **Associativity of the cross product of pairs followed by a multiplication.** Let
`μ : R ⊗ R ⟶ R` be associative, `(μ ▷ R) ≫ μ = (α_ R R R).hom ≫ (R ◁ μ) ≫ μ`, and write `a × b`
for the cross product of pairs with coefficients in `R` followed by the map induced by `μ`. Then
the map of pairs induced by the associator `(X × Y) × Z ≅ X × (Y × Z)` sends `(a × b) × c` to
`a × (b × c)`. -/
theorem singularHomologyCrossRelPair_mul_assoc (μ : R ⊗ R ⟶ R)
    (hμ : (μ ▷ R) ≫ μ = (α_ R R R).hom ≫ (R ◁ μ) ≫ μ) :
    (singularHomologyCrossRelPair X Y A B R R p q pq hpq ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map μ).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) pq) ▷
        (TopPair.ofSubset D).singularHomology R r ≫
      singularHomologyCrossRelPair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D R R pq r n hn ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map μ).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
            snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (α_ X Y Z).hom
            (mapsTo_associator_hom_preimage_union X Y Z A B D)) R n =
      (α_ _ _ _).hom ≫
        (TopPair.ofSubset A).singularHomology R p ◁
          (singularHomologyCrossRelPair Y Z B D R R q r qr hqr ≫
            homologyMap (((SSetPair.chainComplexFunctor C).map μ).app (TopPair.toSSetPair.obj
              (TopPair.ofSubset (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)))) qr) ≫
        singularHomologyCrossRelPair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R R p qr n hn' ≫
          homologyMap (((SSetPair.chainComplexFunctor C).map μ).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
              snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))))) n := by
  have h₁ := singularHomologyCrossRelPair_coefficient_naturality
    (A := fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (B := D) (p := pq) (q := r) (n := n) (h := hn) μ (𝟙 R)
  have h₂ := singularHomologyCrossRelPair_coefficient_naturality (A := A)
    (B := fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) (p := p) (q := qr) (n := n) (h := hn') (𝟙 R) μ
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, homologyMap_id, tensorHom_id,
    id_tensorHom] at h₁ h₂
  have h₃ := singularHomologyCrossRelPair_assoc X Y Z A B D R R R p q r pq qr n hpq hqr hn hn'
  have h₄ : homologyMap (((SSetPair.chainComplexFunctor C).map (μ ▷ R)).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
          snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
      homologyMap (((SSetPair.chainComplexFunctor C).map μ).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
          snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n =
      homologyMap (((SSetPair.chainComplexFunctor C).map (α_ R R R).hom).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
            snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map (R ◁ μ)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
            snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
          homologyMap (((SSetPair.chainComplexFunctor C).map μ).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪
              snd X Y ⁻¹' B) ∪ snd (X ⊗ Y) Z ⁻¹' D)))) n := by
    simp only [← homologyMap_comp, ← NatTrans.comp_app, ← Functor.map_comp, hμ]
  have h₅ {R₁ R₂ : C} (φ : R₁ ⟶ R₂) := TopPair.singularHomologyMap_coefficient_naturality
    (TopPair.ofSubsetMap (α_ X Y Z).hom (mapsTo_associator_hom_preimage_union X Y Z A B D)) φ n
  rw [comp_whiskerRight_assoc, reassoc_of% h₁, reassoc_of% h₄, h₅, reassoc_of% h₅,
    reassoc_of% h₃, ← reassoc_of% h₂, whiskerLeft_comp_assoc]

end Relative

section ULift

variable (X Y Z : TopCat.{0}) (A : Set X) (B : Set Y) (D : Set Z)
  (p q r pq qr n : ℕ) (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n)

/-- **Associativity of the cross product of pairs with integral coefficients.** For spaces in
`TopCat.{0}` and coefficients in `ULift ℤ`, write `a × b` for the cross product of pairs followed
by the multiplication `ULift ℤ ⊗ ULift ℤ ⟶ ULift ℤ` of `ModuleCat.uliftTensorSelfIso`. Then the
map of pairs induced by the associator `(X × Y) × Z ≅ X × (Y × Z)` sends `(a × b) × c` to
`a × (b × c)`. -/
theorem singularHomologyCrossRelPair_uliftTensorSelfIso_assoc :
    (singularHomologyCrossRelPair X Y A B (ModuleCat.of ℤ (ULift.{0} ℤ))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) p q pq hpq ≫
        homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) pq) ▷
        (TopPair.ofSubset D).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) r ≫
      singularHomologyCrossRelPair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) pq r n hn ≫
        homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
            (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
              snd (X ⊗ Y) Z ⁻¹' D)))) n ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (α_ X Y Z).hom
            (mapsTo_associator_hom_preimage_union X Y Z A B D))
              (ModuleCat.of ℤ (ULift.{0} ℤ)) n =
      (α_ _ _ _).hom ≫
        (TopPair.ofSubset A).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) p ◁
          (singularHomologyCrossRelPair Y Z B D (ModuleCat.of ℤ (ULift.{0} ℤ))
              (ModuleCat.of ℤ (ULift.{0} ℤ)) q r qr hqr ≫
            homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
              (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
                (TopPair.ofSubset (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)))) qr) ≫
        singularHomologyCrossRelPair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D)
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p qr n hn' ≫
          homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
            (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
              (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
                snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))))) n :=
  singularHomologyCrossRelPair_mul_assoc X Y Z A B D p q r pq qr n hpq hqr hn hn'
    (ModuleCat.uliftTensorSelfIso ℤ).hom (ModuleCat.uliftTensorSelfIso_hom_assoc ℤ)

end ULift

end TopCat

end
