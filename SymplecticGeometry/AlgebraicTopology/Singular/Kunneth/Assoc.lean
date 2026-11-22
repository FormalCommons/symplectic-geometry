/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Algebra.Category.ModuleCat.ULiftTensor
public import SymplecticGeometry.Algebra.Homology.Monoidal.HomologyCrossHomotopy
public import SymplecticGeometry.Algebra.Homology.Monoidal.SplitMono
public import SymplecticGeometry.AlgebraicTopology.Singular.PairChangeOfCoefficients
public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.ShuffleAssoc

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
the relative Eilenberg–Zilber theorem `TopCat.quasiIso_shufflePair`, which the library's copy of
Tau Ceti's `Singular/Kunneth/Pair.lean` leaves out. Instead, the two iterated shuffle
maps are compared at chain level. The natural homotopy `SSet.shuffleAssocHomotopy` between them,
transported to singular chains along the lax monoidal structure of `TopCat.toSSet`, is
`TopCat.shuffleAssocHomotopy`, natural in the three spaces. By this naturality along the
inclusions of `A`, `B` and `D`, the homotopy followed by the projection to the relative chains
vanishes on the chains of the three pieces of the subspace, so it descends to the tensor product
of the relative chains, one factor at a time (`Homotopy.descCokernel`), as `TopCat.shufflePair` is
built: this is `TopCat.shufflePairAssocHomotopy`. On homology, the associativity of the algebraic
cross product and its naturality conclude
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

-- Instance search does not find the monoidal structure on chain complexes when `C` is abelian,
-- although its hypotheses hold; it is given here, so that the lemmas of monoidal categories apply
-- to the tensor products of chain complexes below.
noncomputable local instance : MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

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
    (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ⊗ₘ
          (TopPair.ofSubset D).singularChainComplexπ T) ≫
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
        (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
            (R ⊗ (S ⊗ T)) := by
  have h₁ := singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X Y A B R S
  have h₂ := singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair (X ⊗ Y) Z
    (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T
  have h₃ := TopPair.singularChainComplexπ_coefficient_naturality
    (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
      snd (X ⊗ Y) Z ⁻¹' D)) (α_ R S T).hom
  have h₄ := TopPair.singularChainComplexπ_pair_naturality (TopPair.ofSubsetMap (α_ X Y Z).hom
    (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T))
  rw [TopPair.ofSubsetMap_fst] at h₄
  rw [tensorHom_comp_whiskerRight_assoc, h₁]
  refine (congrArg (· ≫ _) (whiskerRight_comp_tensorHom _ _ _).symm).trans ?_
  -- the ambient chains of a pair are the chains of its space only up to unfolding, so the
  -- remaining composites are reassociated by hand
  have key : ((TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S) ⊗ₘ
        (TopPair.ofSubset D).singularChainComplexπ T) ≫
      shufflePair (X ⊗ Y) Z (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) D (R ⊗ S) T ≫
        ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
            snd (X ⊗ Y) Z ⁻¹' D))) ≫
          TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
            (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)) =
      shuffle (X ⊗ Y) Z (R ⊗ S) T ≫
        ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫
          SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ (S ⊗ T)) ≫
            (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
              snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
                (R ⊗ (S ⊗ T)) := by
    have h₃' : (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
          snd (X ⊗ Y) Z ⁻¹' D)).singularChainComplexπ ((R ⊗ S) ⊗ T) ≫
        ((SSetPair.chainComplexFunctor C).map (α_ R S T).hom).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
            snd (X ⊗ Y) Z ⁻¹' D))) =
        ((SSet.chainComplexFunctor C).map (α_ R S T).hom).app (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫
          (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
            snd (X ⊗ Y) Z ⁻¹' D)).singularChainComplexπ (R ⊗ (S ⊗ T)) := h₃.symm
    have h₄' : (TopPair.ofSubset (fst (X ⊗ Y) Z ⁻¹' (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) ∪
          snd (X ⊗ Y) Z ⁻¹' D)).singularChainComplexπ (R ⊗ (S ⊗ T)) ≫
        TopPair.singularChainComplexMap (TopPair.ofSubsetMap (α_ X Y Z).hom
          (mapsTo_associator_hom_preimage_union X Y Z A B D)) (R ⊗ (S ⊗ T)) =
        SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ (S ⊗ T)) ≫
          (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
            snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
              (R ⊗ (S ⊗ T)) := h₄.symm
    exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₂).trans <|
      (Category.assoc _ _ _).trans <| congrArg (shuffle (X ⊗ Y) Z (R ⊗ S) T ≫ ·) <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h₃').trans <|
          (Category.assoc _ _ _).trans <| congrArg
            (((SSet.chainComplexFunctor C).map (α_ R S T).hom).app
              (toSSet.obj ((X ⊗ Y) ⊗ Z)) ≫ ·) h₄'
  refine (Category.assoc _ _ _).trans <|
    (congrArg (shuffle X Y R S ▷ (toSSet.obj Z).chainComplex T ≫ ·) key).trans ?_
  exact ((Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (Category.assoc _ _ _)).symm

/-- On `(C(X; R) ⊗ C(Y; S)) ⊗ C(Z; T)`, the second iterated shuffle map of the pairs is the second
iterated shuffle map of the spaces followed by the projection to the relative chains. -/
private theorem singularChainComplexπ_tensorHom_shufflePair_assoc_right :
    (((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ⊗ₘ
          (TopPair.ofSubset D).singularChainComplexπ T) ≫
      (α_ ((TopPair.ofSubset A).singularChainComplex R)
        ((TopPair.ofSubset B).singularChainComplex S)
        ((TopPair.ofSubset D).singularChainComplex T)).hom ≫
        ((TopPair.ofSubset A).singularChainComplex R ◁ shufflePair Y Z B D S T) ≫
          shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T) =
      ((α_ ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S)
          ((toSSet.obj Z).chainComplex T)).hom ≫
        ((toSSet.obj X).chainComplex R ◁ shuffle Y Z S T) ≫ shuffle X (Y ⊗ Z) R (S ⊗ T)) ≫
        (TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
            (R ⊗ (S ⊗ T)) := by
  have h₁ := singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair Y Z B D S T
  have h₂ := singularChainComplexπ_tensorHom_singularChainComplexπ_shufflePair X (Y ⊗ Z) A
    (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T)
  rw [associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc, h₁]
  -- the ambient chains of a pair are the chains of its space only up to unfolding, so the
  -- composites are reassociated by hand
  refine (congrArg (fun φ ↦ (α_ _ _ _).hom ≫ φ ≫
    shufflePair X (Y ⊗ Z) A (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D) R (S ⊗ T))
      (whiskerLeft_comp_tensorHom _ _ _).symm).trans ?_
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂))).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

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
        ((TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
            (R ⊗ (S ⊗ T))).f j = 0 := by
  -- the tensor products of chain complexes are found along other instances here than in the
  -- statement of the naturality, so the composites are rewritten by hand
  exact (shuffleAssocHomotopy_hom_naturality_assoc R S T f g h i j _).trans <|
    (congrArg (_ ≫ ·) ((comp_f _ _ j).symm.trans ((congrArg (fun φ ↦ φ.f j)
      (TopPair.chainComplexMap_comp_singularChainComplexπ_eq_zero_of_range_subset hfgh
        (R ⊗ (S ⊗ T)))).trans
        (zero_f _ _ j)))).trans comp_zero

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
private theorem shortComplex₁_g_comp_shortComplex₂_g_comp_shortComplex₃_g :
    (shortComplex₁ X Z A R S T Y).g ≫ (shortComplex₂ X Y A B R S T Z).g ≫
        (shortComplex₃ X Y Z A B D R S T).g =
      ((TopPair.ofSubset A).singularChainComplexπ R ⊗ₘ
        (TopPair.ofSubset B).singularChainComplexπ S) ⊗ₘ
          (TopPair.ofSubset D).singularChainComplexπ T := by
  have h {K₁ K₂ K₃ L₁ L₂ L₃ : ChainComplex C ℕ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃) :
      ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 K₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 K₃) ≫ (𝟙 (L₁ ⊗ L₂) ⊗ₘ f₃) =
        (f₁ ⊗ₘ f₂) ⊗ₘ f₃ := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  -- the ambient chains of a pair are the chains of its space only up to unfolding, so the
  -- identity is applied to the three projections rather than rewritten
  exact h _ _ _
/-- The first step of the descent of `TopCat.shuffleAssocHomotopy`: to
`(C(X, A) ⊗ C(Y)) ⊗ C(Z)`, along the projection in the first factor. -/
private def shufflePairAssocHomotopy₁ :
    _root_.Homotopy ((shortComplex₂ X Y A B R S T Z).g ≫ (shortComplex₃ X Y Z A B D R S T).g ≫
        shufflePairAssocLeft X Y Z A B D R S T)
      ((shortComplex₂ X Y A B R S T Z).g ≫ (shortComplex₃ X Y Z A B D R S T).g ≫
        shufflePairAssocRight X Y Z A B D R S T) :=
  have hS := shortExact_shortComplex₁ X Z A R S T Y
  _root_.Homotopy.descCokernel (shuffleAssocHomotopy X Y Z R S T)
    (shortComplex₁ X Z A R S T Y).f (shortComplex₁ X Z A R S T Y).g
    ((TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
      snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ (R ⊗ (S ⊗ T)))
    _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    (fun i j ↦ by
      have h := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (TopPair.ofSubset A).map (𝟙 Y) (𝟙 Z) (by rintro _ ⟨x, rfl⟩; exact Or.inl x.1.property) i j
      simp only [CategoryTheory.Functor.map_id] at h
      exact h)
    ((Category.assoc _ _ _).symm.trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ shufflePairAssocLeft X Y Z A B D R S T) ((Category.assoc _ _ _).trans
        (shortComplex₁_g_comp_shortComplex₂_g_comp_shortComplex₃_g X Y Z A B D R S T))).trans
          (singularChainComplexπ_tensorHom_shufflePair_assoc_left X Y Z A B D R S T))
    ((Category.assoc _ _ _).symm.trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ shufflePairAssocRight X Y Z A B D R S T) ((Category.assoc _ _ _).trans
        (shortComplex₁_g_comp_shortComplex₂_g_comp_shortComplex₃_g X Y Z A B D R S T))).trans
          (singularChainComplexπ_tensorHom_shufflePair_assoc_right X Y Z A B D R S T))

/-- The homotopy `shufflePairAssocHomotopy₁` is the homotopy `TopCat.shuffleAssocHomotopy`,
descended. -/
private theorem shortComplex₁_g_f_shufflePairAssocHomotopy₁_hom (i j : ℕ) :
    (shortComplex₁ X Z A R S T Y).g.f i ≫ (shufflePairAssocHomotopy₁ X Y Z A B D R S T).hom i j =
      (shuffleAssocHomotopy X Y Z R S T).hom i j ≫
        ((TopPair.ofSubset (fst X (Y ⊗ Z) ⁻¹' A ∪
          snd X (Y ⊗ Z) ⁻¹' (fst Y Z ⁻¹' B ∪ snd Y Z ⁻¹' D))).singularChainComplexπ
            (R ⊗ (S ⊗ T))).f j :=
  _root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

/-- The second step of the descent: to `(C(X, A) ⊗ C(Y, B)) ⊗ C(Z)`, along the projection in the
second factor. -/
private def shufflePairAssocHomotopy₂ :
    _root_.Homotopy ((shortComplex₃ X Y Z A B D R S T).g ≫
        shufflePairAssocLeft X Y Z A B D R S T)
      ((shortComplex₃ X Y Z A B D R S T).g ≫ shufflePairAssocRight X Y Z A B D R S T) :=
  have hS := shortExact_shortComplex₂ X Y A B R S T Z
  _root_.Homotopy.descCokernel (shufflePairAssocHomotopy₁ X Y Z A B D R S T)
    (shortComplex₂ X Y A B R S T Z).f (shortComplex₂ X Y A B R S T Z).g (𝟙 _) _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    (fun i j ↦ by
      have : Epi ((shortComplex₁ X Z A R S T (TopPair.ofSubset B).snd).g.f i) :=
        ((shortExact_shortComplex₁ X Z A R S T (TopPair.ofSubset B).snd).map_of_exact
          (HomologicalComplex.eval C _ i)).epi_g
      refine (cancel_epi ((shortComplex₁ X Z A R S T (TopPair.ofSubset B).snd).g.f i)).1 ?_
      have e₁ {K₁ K₂ K₃ L₁ L₂ : ChainComplex C ℕ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
          ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 K₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 K₃) =
            ((𝟙 K₁ ⊗ₘ f₂) ⊗ₘ 𝟙 K₃) ≫ ((f₁ ⊗ₘ 𝟙 L₂) ⊗ₘ 𝟙 K₃) := by
        simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      have e₂ := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (𝟙 X) (TopPair.ofSubset B).map (𝟙 Z)
        (by rintro _ ⟨x, rfl⟩; exact Or.inr (Or.inl x.2.1.property)) i j
      simp only [CategoryTheory.Functor.map_id] at e₂
      have e₃ : (shortComplex₁ X Z A R S T (TopPair.ofSubset B).snd).g ≫
          (shortComplex₂ X Y A B R S T Z).f =
            ((𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ
              SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) S) ⊗ₘ
                𝟙 ((toSSet.obj Z).chainComplex T)) ≫ (shortComplex₁ X Z A R S T Y).g :=
        e₁ _ _
      -- the ambient chains of a pair are the chains of its space only up to unfolding, so the
      -- composites are reassociated by hand
      refine (congrArg (_ ≫ _ ≫ ·) ((congrArg (_ ≫ ·) (id_f _ j)).trans
        (Category.comp_id _))).trans (Eq.trans ?_ comp_zero.symm)
      exact (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ (shufflePairAssocHomotopy₁ X Y Z A B D R S T).hom i j)
          ((comp_f _ _ i).symm.trans ((congrArg (fun φ ↦ φ.f i) e₃).trans
            (comp_f _ _ i)))).trans <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (shortComplex₁_g_f_shufflePairAssocHomotopy₁_hom X Y Z A B D R S T
          i j)).trans e₂)
    (Category.comp_id _).symm (Category.comp_id _).symm

/-- The homotopy `shufflePairAssocHomotopy₂` is the homotopy `shufflePairAssocHomotopy₁`,
descended. -/
private theorem shortComplex₂_g_f_shufflePairAssocHomotopy₂_hom (i j : ℕ) :
    (shortComplex₂ X Y A B R S T Z).g.f i ≫ (shufflePairAssocHomotopy₂ X Y Z A B D R S T).hom i j =
      (shufflePairAssocHomotopy₁ X Y Z A B D R S T).hom i j :=
  (_root_.Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j).trans
    ((congrArg (_ ≫ ·) (id_f _ j)).trans (Category.comp_id _))

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
  _root_.Homotopy.descCokernel (shufflePairAssocHomotopy₂ X Y Z A B D R S T)
    (shortComplex₃ X Y Z A B D R S T).f (shortComplex₃ X Y Z A B D R S T).g (𝟙 _) _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval C _ i)).gIsCokernel)
    (fun i j ↦ by
      have : Epi ((shortComplex₁ X (TopPair.ofSubset D).snd A R S T Y).g.f i ≫
          (shortComplex₂ X Y A B R S T (TopPair.ofSubset D).snd).g.f i) :=
        @epi_comp _ _ _ _ _ _
          ((shortExact_shortComplex₁ X (TopPair.ofSubset D).snd A R S T Y).map_of_exact
            (HomologicalComplex.eval C _ i)).epi_g _
          ((shortExact_shortComplex₂ X Y A B R S T (TopPair.ofSubset D).snd).map_of_exact
            (HomologicalComplex.eval C _ i)).epi_g
      refine (cancel_epi ((shortComplex₁ X (TopPair.ofSubset D).snd A R S T Y).g.f i ≫
          (shortComplex₂ X Y A B R S T (TopPair.ofSubset D).snd).g.f i)).1 ?_
      have e₁ {K₁ K₂ K₃ L₁ L₂ L₃ : ChainComplex C ℕ} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
          (f₃ : K₃ ⟶ L₃) :
          ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 K₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 K₃) ≫ (𝟙 (L₁ ⊗ L₂) ⊗ₘ f₃) =
            ((𝟙 K₁ ⊗ₘ 𝟙 K₂) ⊗ₘ f₃) ≫ ((f₁ ⊗ₘ 𝟙 K₂) ⊗ₘ 𝟙 L₃) ≫ ((𝟙 L₁ ⊗ₘ f₂) ⊗ₘ 𝟙 L₃) := by
        simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      have e₂ := shuffleAssocHomotopy_hom_comp_singularChainComplexπ_eq_zero X Y Z A B D R S T
        (𝟙 X) (𝟙 Y) (TopPair.ofSubset D).map
        (by rintro _ ⟨x, rfl⟩; exact Or.inr (Or.inr x.2.2.property)) i j
      simp only [CategoryTheory.Functor.map_id] at e₂
      have e₃ : (shortComplex₁ X (TopPair.ofSubset D).snd A R S T Y).g ≫
          (shortComplex₂ X Y A B R S T (TopPair.ofSubset D).snd).g ≫
            (shortComplex₃ X Y Z A B D R S T).f =
          ((𝟙 ((toSSet.obj X).chainComplex R) ⊗ₘ 𝟙 ((toSSet.obj Y).chainComplex S)) ⊗ₘ
              SSet.chainComplexMap (toSSet.map (TopPair.ofSubset D).map) T) ≫
            (shortComplex₁ X Z A R S T Y).g ≫ (shortComplex₂ X Y A B R S T Z).g :=
        e₁ _ _ _
      -- the ambient chains of a pair are the chains of its space only up to unfolding, so the
      -- composites are reassociated through an identity between morphisms of `C`
      have e₄ {P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C} (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (c : P₃ ⟶ P₄)
          (d : P₄ ⟶ P₇) (e : P₁ ⟶ P₅) (f : P₅ ⟶ P₆) (g : P₆ ⟶ P₄) (k : P₆ ⟶ P₇) (k' : P₅ ⟶ P₇)
          (hc : (a ≫ b) ≫ c = e ≫ f ≫ g) (hg : g ≫ d = k) (hf : f ≫ k = k') (he : e ≫ k' = 0) :
          (a ≫ b) ≫ c ≫ d = 0 := by
        rw [← Category.assoc, hc, Category.assoc, Category.assoc, hg, hf, he]
      refine (congrArg (_ ≫ _ ≫ ·) ((congrArg (_ ≫ ·) (id_f _ j)).trans
        (Category.comp_id _))).trans (Eq.trans ?_ comp_zero.symm)
      refine e₄ _ _ _ _ _ _ _ _ _ ((Category.assoc _ _ _).trans <|
        ((congrArg (_ ≫ ·) (comp_f _ _ i).symm).trans (comp_f _ _ i).symm).trans <|
          (congrArg (fun φ ↦ φ.f i) e₃).trans <|
            (comp_f _ _ i).trans (congrArg (_ ≫ ·) (comp_f _ _ i)))
        (shortComplex₂_g_f_shufflePairAssocHomotopy₂_hom X Y Z A B D R S T i j)
        (shortComplex₁_g_f_shufflePairAssocHomotopy₁_hom X Y Z A B D R S T i j) e₂)
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
