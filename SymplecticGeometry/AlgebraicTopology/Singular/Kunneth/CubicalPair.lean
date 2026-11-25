/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePair
public import TauCeti.AlgebraicTopology.Singular.Cubical.Kunneth.Excisive
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.CrossProduct

/-!
# The cubical and the simplicial cross product of two pairs

Let `A ⊆ X` and `B ⊆ Y` be subsets of topological spaces, and `k` a commutative ring. Tau Ceti's
Künneth map of a product of pairs, `TauCeti.singularHomologyKunnethPair`, is built from normalized
cubical chains: the cubical cross product of the pairs, `TauCeti.cubicalCrossProductPair`,
followed by the comparison with singular chains, `TauCeti.cubicalChainComplexProdToSingular`. The
library's cross product of the pairs, `TopCat.singularHomologyCrossRelPair`, is built from the
shuffle map of simplicial chains, `TopCat.shufflePair`. This file shows that the two agree in
homology, with no sign, once `k ⊗ k` is identified with `k` by the unitor.

On `N(X, A; k) ⊗ N(Y, B; k)` there are two chain maps to `C(X × Y, A × Y ∪ X × B; k)`:
`TauCeti.cubicalCrossProductPairToSingular`, the cubical cross product of the pairs followed by
the comparison with singular chains, and `TauCeti.singularCrossProductPairOfCubical`, the
comparison maps `TauCeti.cubicalToSingularRel` of the two pairs followed by the shuffle map of the
pairs. Tau Ceti's homotopy between their absolute forms,
`TauCeti.cubicalSingularCrossProductHomotopy`, is natural in both spaces
(`TauCeti.cubicalSingularCrossProductHomotopy_hom_naturality`), so it vanishes on `N(A) ⊗ N(Y)`
and on `N(X) ⊗ N(B)` after the projection to the chains of the pair, and it descends along the
quotient maps in the two factors (`Homotopy.descCokernel`), one after the other.

## Main definitions

* `TauCeti.cubicalCrossProductPairToSingular` and `TauCeti.singularCrossProductPairOfCubical`:
  the two chain maps above.
* `TauCeti.cubicalSingularCrossProductPairHomotopy`: a chain homotopy between them.

## Main results

* `TauCeti.π_tensorHom_π_cubicalCrossProductPairToSingular` and
  `TauCeti.π_tensorHom_π_singularCrossProductPairOfCubical`: on the chains of the spaces, the two
  maps are the absolute ones followed by the projection to the chains of the pair.
* `TauCeti.homologyMap_cubicalCrossProductPairToSingular`: the two maps agree in homology.
* `TauCeti.ιTensorObj_singularHomologyKunnethPair`: on the summand `Hₚ(X, A; k) ⊗ H_q(Y, B; k)`,
  Tau Ceti's Künneth map of the pairs is `TopCat.singularHomologyCrossRelPair` followed by the
  coefficient map of the unitor.

The descent of the homotopy in two steps adapts that of the Eilenberg–Zilber homotopy in
`TopCat.shuffleAlexanderWhitneyPairHomotopy`
(`SymplecticGeometry/AlgebraicTopology/Singular/Kunneth/RelativePair.lean`) to Tau Ceti's
`TauCeti.cubicalSingularCrossProductHomotopy` (Tau Ceti,
`TauCeti/AlgebraicTopology/Singular/Cubical/Comparison/CrossProduct.lean`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product `Hₚ(X, A) ⊗ H_q(Y, B) ⟶ Hₙ(X × Y, A × Y ∪ X × B)`.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII, for the cubical
  cross product and its comparison with the simplicial one.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits

universe u

namespace TauCeti

open TopPair

variable (k : Type u) [CommRing k] {X Y : TopCat.{u}} (A : Set X) (B : Set Y)

/-- The cubical cross product of the pairs `(X, A)` and `(Y, B)` followed by the comparison with
singular chains, `N(X, A; k) ⊗ N(Y, B; k) ⟶ C(X × Y, A × Y ∪ X × B; k)`. -/
def cubicalCrossProductPairToSingular :
    (ofSubset A).cubicalChainComplex k ⊗ (ofSubset B).cubicalChainComplex k ⟶
      (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (ModuleCat.of k k) :=
  cubicalCrossProductPair k (ofSubset A) (ofSubset B) ≫ cubicalChainComplexProdToSingular k A B

theorem cubicalCrossProductPairToSingular_def :
    cubicalCrossProductPairToSingular k A B =
      cubicalCrossProductPair k (ofSubset A) (ofSubset B) ≫
        cubicalChainComplexProdToSingular k A B :=
  (rfl)

/-- The tensor product of the comparison maps of the pairs `(X, A)` and `(Y, B)` followed by the
shuffle map of the product of the pairs, with `k ⊗ k` identified with `k` by the unitor,
`N(X, A; k) ⊗ N(Y, B; k) ⟶ C(X × Y, A × Y ∪ X × B; k)`. -/
def singularCrossProductPairOfCubical :
    (ofSubset A).cubicalChainComplex k ⊗ (ofSubset B).cubicalChainComplex k ⟶
      (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularChainComplex (ModuleCat.of k k) :=
  (cubicalToSingularRel k (ofSubset A) ⊗ₘ cubicalToSingularRel k (ofSubset B)) ≫
    TopCat.shufflePair X Y A B (ModuleCat.of k k) (ModuleCat.of k k) ≫
      ((SSetPair.chainComplexFunctor (ModuleCat.{u} k)).map (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app
        (TopPair.toSSetPair.obj (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))

theorem singularCrossProductPairOfCubical_def :
    singularCrossProductPairOfCubical k A B =
      (cubicalToSingularRel k (ofSubset A) ⊗ₘ cubicalToSingularRel k (ofSubset B)) ≫
        TopCat.shufflePair X Y A B (ModuleCat.of k k) (ModuleCat.of k k) ≫
          ((SSetPair.chainComplexFunctor (ModuleCat.{u} k)).map
              (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app
            (TopPair.toSSetPair.obj (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B))) :=
  (rfl)

/-- On `N(X; k) ⊗ N(Y; k)`, the cubical cross product of the pairs followed by the comparison with
singular chains is the absolute one, `TauCeti.cubicalCrossProductToSingularApp`, followed by the
projection to the chains of the pair `(X × Y, A × Y ∪ X × B)`. -/
theorem π_tensorHom_π_cubicalCrossProductPairToSingular :
    (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)) ≫
      cubicalCrossProductPairToSingular k A B =
      cubicalCrossProductToSingularApp k X Y ≫
        TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
          (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) := by
  have h₂ := whiskerLeft_π_cubicalCrossProductRel k (ofSubset A).fst (ofSubset B)
  have h₄ := π_cubicalToSingularRel k ((ofSubset B).prodLeft (ofSubset A).fst)
  have h₅ := singularRelπ_naturality k (prodLeftToPreimageUnion A B)
  rw [cubicalCrossProductPairToSingular_def, tensorHom_def'_assoc,
    whiskerRight_π_cubicalCrossProductPair_assoc,
    π_cubicalChainComplexProdToSingular, ← Category.assoc, ← Category.assoc, h₂,
    cubicalCrossProductToSingularApp_def]
  have key : cokernel.π ((normalizedCubicalChainComplex k).map ((ofSubset B).prodLeft X).map) ≫
      cubicalToSingularRel k ((ofSubset B).prodLeft (ofSubset A).fst) ≫
        TopPair.singularChainComplexMap (prodLeftToPreimageUnion A B) (ModuleCat.of k k) =
      (cubicalToSingular k).app (X ⊗ Y) ≫ TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
          (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₄)).trans ?_
    rw [Category.assoc, ← h₅]
    exact congrArg (_ ≫ ·) ((congrArg (· ≫ _) ((congrArg (singularChains k).map
      (prodLeftToPreimageUnion_fst A B)).trans ((singularChains k).map_id _))).trans
        ((Category.id_comp _).trans (singularRelπ_eq k _)))
  exact (Category.assoc (cubicalCrossProduct k X Y) _ _).trans
    ((congrArg (cubicalCrossProduct k X Y ≫ ·) key).trans (Category.assoc _ _ _).symm)

/-- On `N(X; k) ⊗ N(Y; k)`, the comparison maps of the pairs followed by the shuffle map of the
pairs are the absolute ones, `TauCeti.singularCrossProductOfCubicalApp`, followed by the
projection to the chains of the pair `(X × Y, A × Y ∪ X × B)`. -/
theorem π_tensorHom_π_singularCrossProductPairOfCubical :
    (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)) ≫
      singularCrossProductPairOfCubical k A B =
      singularCrossProductOfCubicalApp k X Y ≫
        TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
          (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) := by
  rw [singularCrossProductPairOfCubical_def]
  have ha : (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)) ≫
        (cubicalToSingularRel k (ofSubset A) ⊗ₘ cubicalToSingularRel k (ofSubset B)) =
      ((cubicalToSingular k).app X ⊗ₘ (cubicalToSingular k).app Y) ≫
        (TopPair.singularChainComplexπOfSubset (ModuleCat.of k k) A ⊗ₘ
          TopPair.singularChainComplexπOfSubset (ModuleCat.of k k) B) := by
    rw [tensorHom_comp_tensorHom, π_cubicalToSingularRel, π_cubicalToSingularRel, singularRelπ_eq,
      singularRelπ_eq]
    exact (tensorHom_comp_tensorHom (C := ChainComplex (ModuleCat.{u} k) ℕ) _ _ _ _).symm
  have e₁ :=
    TopCat.singularChainComplexπOfSubset_tensorHom_singularChainComplexπOfSubset_shufflePair
      X Y A B (ModuleCat.of k k) (ModuleCat.of k k)
  have e₂ := TopPair.singularChainComplexπOfSubset_coefficient_naturality
    (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) (λ_ (𝟙_ (ModuleCat.{u} k))).hom
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ha).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) e₁).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) e₂.symm))))).trans ?_)
  rw [singularCrossProductOfCubicalApp_def, singularCrossProduct_def,
    singularChainComplexFunctor_map_app]
  -- up to associativity, the two sides differ only in writing the coefficients as
  -- `ModuleCat.of k k` or as the monoidal unit `𝟙_ (ModuleCat k)`, which Mathlib defines
  -- to be `ModuleCat.of k k`;
  -- `rw [Category.assoc]` cannot see through this, so the goal is closed by `rfl`
  rfl

private theorem tensorHom_id_π_comp_π_tensorHom_id :
    HomologicalComplex.tensorHom (𝟙 ((normalizedCubicalChainComplex k).obj X))
        (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)) ≫
      (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        𝟙 ((ofSubset B).cubicalChainComplex k)) =
    (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)) :=
  (tensorHom_comp_tensorHom (C := ChainComplex (ModuleCat.{u} k) ℕ) _ _ _ _).trans
    (congrArg₂ (· ⊗ₘ ·) (Category.id_comp _) (Category.comp_id _))

/-- The singular chains of a product map `f × g : Z × W ⟶ X × Y` vanish in the chains of the pair
`(X × Y, A × Y ∪ X × B)` when `f` lands in `A` or `g` lands in `B`. -/
theorem singularChains_map_tensorHom_comp_singularChainComplexπOfSubset_eq_zero {Z W : TopCat.{u}}
    (f : Z ⟶ X) (g : W ⟶ Y)
    (h : Set.range f ⊆ A ∨ Set.range g ⊆ B) :
    (singularChains k).map (f ⊗ₘ g) ≫
      TopPair.singularChainComplexπOfSubset (ModuleCat.of k k) (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B) =
        0 :=
  chainComplexMap_comp_singularChainComplexπOfSubset_eq_zero_of_range_subset _ (by
    rintro _ ⟨z, rfl⟩
    rcases h with h | h
    · exact Or.inl (h ⟨z.1, rfl⟩)
    · exact Or.inr (h ⟨z.2, rfl⟩))

/-- The homotopy `TauCeti.cubicalSingularCrossProductHomotopy`, descended to `N(X; k) ⊗ N(Y, B; k)`
and projected to the chains of `(X × Y, A × Y ∪ X × B)`. -/
private def homotopyFst :
    Homotopy ((cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        𝟙 ((ofSubset B).cubicalChainComplex k)) ≫ cubicalCrossProductPairToSingular k A B)
      ((cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map) ⊗ₘ
        𝟙 ((ofSubset B).cubicalChainComplex k)) ≫ singularCrossProductPairOfCubical k A B) :=
  have hS := shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k X (ofSubset B)
  Homotopy.descCokernel (cubicalSingularCrossProductHomotopy k X Y)
    (HomologicalComplex.tensorHom (𝟙 _) ((normalizedCubicalChainComplex k).map (ofSubset B).map))
    (HomologicalComplex.tensorHom (𝟙 _)
      (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map)))
    (TopPair.singularChainComplexπOfSubset (ModuleCat.of k k) (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval _ _ i)).gIsCokernel)
    (fun i j ↦ by
      have h := cubicalSingularCrossProductHomotopy_hom_naturality k (𝟙 X) (ofSubset B).map i j
      rw [CategoryTheory.Functor.map_id] at h
      have h₀ : ((singularChains k).map (𝟙 X ⊗ₘ (ofSubset B).map)).f j ≫
          (TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
            (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).f j = 0 :=
        (comp_f _ _ j).symm.trans ((congr_hom
          (singularChains_map_tensorHom_comp_singularChainComplexπOfSubset_eq_zero k A B
            (𝟙 X) (ofSubset B).map (Or.inr (by rintro _ ⟨z, rfl⟩; exact z.property))) j).trans
          (zero_f _ _ j))
      exact ((reassoc_of% h) _).trans ((congrArg (_ ≫ ·) h₀).trans comp_zero))
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (tensorHom_id_π_comp_π_tensorHom_id k A B)).trans
        (π_tensorHom_π_cubicalCrossProductPairToSingular k A B)))
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (tensorHom_id_π_comp_π_tensorHom_id k A B)).trans
        (π_tensorHom_π_singularCrossProductPairOfCubical k A B)))

private theorem tensorHom_id_π_f_homotopyFst_hom (i j : ℕ) :
    (HomologicalComplex.tensorHom (𝟙 ((normalizedCubicalChainComplex k).obj X))
        (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map))).f i ≫
      (homotopyFst k A B).hom i j =
    (cubicalSingularCrossProductHomotopy k X Y).hom i j ≫
      (TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
        (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).f j :=
  Homotopy.π_descCokernel_hom _ _ _ _ _ _ _ _ _ i j

private theorem tensorHom_id_π_f_comp_tensorHom_map_id_f (i : ℕ) :
    (HomologicalComplex.tensorHom (𝟙 ((normalizedCubicalChainComplex k).obj (ofSubset A).snd))
        (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map))).f i ≫
      (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map (ofSubset A).map)
        (𝟙 ((ofSubset B).cubicalChainComplex k))).f i =
    (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map (ofSubset A).map)
        (𝟙 ((normalizedCubicalChainComplex k).obj Y))).f i ≫
      (HomologicalComplex.tensorHom (𝟙 ((normalizedCubicalChainComplex k).obj X))
        (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map))).f i := by
  refine (comp_f _ _ i).symm.trans ((HomologicalComplex.congr_hom ?_ i).trans (comp_f _ _ i))
  exact (tensorHom_comp_tensorHom (C := ChainComplex (ModuleCat.{u} k) ℕ) _ _ _ _).trans
    ((congrArg₂ (· ⊗ₘ ·) ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)).trans
        (tensorHom_comp_tensorHom _ _ _ _).symm)

/-- **The cubical and the simplicial cross product of two pairs are chain homotopic**: the cubical
cross product of the pairs `(X, A)` and `(Y, B)` followed by the comparison with singular chains,
and the tensor product of the comparison maps of the pairs followed by the shuffle map of the
product of the pairs, `N(X, A; k) ⊗ N(Y, B; k) ⟶ C(X × Y, A × Y ∪ X × B; k)`, are chain
homotopic. -/
def cubicalSingularCrossProductPairHomotopy :
    Homotopy (cubicalCrossProductPairToSingular k A B) (singularCrossProductPairOfCubical k A B) :=
  have hS :=
    shortExact_tensorRightShortComplex_cubicalChainComplexShortComplex k (ofSubset A) (ofSubset B)
  Homotopy.descCokernel (homotopyFst k A B)
    (HomologicalComplex.tensorHom ((normalizedCubicalChainComplex k).map (ofSubset A).map)
      (𝟙 _))
    (HomologicalComplex.tensorHom
      (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset A).map)) (𝟙 _))
    (𝟙 _) _
    (fun i ↦ (hS.map_of_exact (HomologicalComplex.eval _ _ i)).gIsCokernel)
    (fun i j ↦ by
      have : Epi ((HomologicalComplex.tensorHom
          (𝟙 ((normalizedCubicalChainComplex k).obj (ofSubset A).snd))
          (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map))).f i) :=
        ((shortExact_tensorLeftShortComplex_cubicalChainComplexShortComplex k (ofSubset A).snd
          (ofSubset B)).map_of_exact (HomologicalComplex.eval _ _ i)).epi_g
      refine (cancel_epi ((HomologicalComplex.tensorHom
          (𝟙 ((normalizedCubicalChainComplex k).obj (ofSubset A).snd))
          (cokernel.π ((normalizedCubicalChainComplex k).map (ofSubset B).map))).f i)).1 ?_
      have h := cubicalSingularCrossProductHomotopy_hom_naturality k (ofSubset A).map (𝟙 Y) i j
      rw [CategoryTheory.Functor.map_id] at h
      rw [comp_zero, id_f, Category.comp_id]
      refine ((reassoc_of% tensorHom_id_π_f_comp_tensorHom_map_id_f k A B i) _).trans
        ((congrArg (_ ≫ ·) (tensorHom_id_π_f_homotopyFst_hom k A B i j)).trans ?_)
      have h₀ : ((singularChains k).map ((ofSubset A).map ⊗ₘ 𝟙 Y)).f j ≫
          (TopPair.singularChainComplexπOfSubset (ModuleCat.of k k)
            (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).f j = 0 :=
        (comp_f _ _ j).symm.trans ((congr_hom
          (singularChains_map_tensorHom_comp_singularChainComplexπOfSubset_eq_zero k A B
            (ofSubset A).map (𝟙 Y) (Or.inl (by rintro _ ⟨z, rfl⟩; exact z.property))) j).trans
          (zero_f _ _ j))
      exact ((reassoc_of% h) _).trans ((congrArg (_ ≫ ·) h₀).trans comp_zero))
    (Category.comp_id _).symm (Category.comp_id _).symm

/-- The cubical and the simplicial cross product of two pairs induce the same map on homology. -/
theorem homologyMap_cubicalCrossProductPairToSingular (n : ℕ) :
    homologyMap (cubicalCrossProductPairToSingular k A B) n =
      homologyMap (singularCrossProductPairOfCubical k A B) n :=
  (cubicalSingularCrossProductPairHomotopy k A B).homologyMap_eq n

/-- **The Künneth map of a product of pairs is the cross product of the pairs.** On the summand
`Hₚ(X, A; k) ⊗ H_q(Y, B; k)`, Tau Ceti's Künneth map `TauCeti.singularHomologyKunnethPair`, built
from cubical chains, is the cross product of the pairs `TopCat.singularHomologyCrossRelPair`,
built from the shuffle map of simplicial chains, followed by the map induced by the
multiplication `k ⊗ k ≅ k` of the coefficients. -/
theorem ιTensorObj_singularHomologyKunnethPair (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj
        (fun p ↦ (ofSubset A).singularHomology (ModuleCat.of k k) p)
        (fun q ↦ (ofSubset B).singularHomology (ModuleCat.of k k) q) p q n h ≫
      singularHomologyKunnethPair k A B n =
      TopCat.singularHomologyCrossRelPair X Y A B (ModuleCat.of k k) (ModuleCat.of k k) p q n h ≫
        homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{u} k)).map
            (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app
          (TopPair.toSSetPair.obj (ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)))) n := by
  rw [ι_singularHomologyKunnethPair, TopCat.singularHomologyCrossRelPair_def,
    ← cancel_epi ((TopPair.singularCubicalHomologyIso k (ofSubset A) p).inv ⊗ₘ
      (TopPair.singularCubicalHomologyIso k (ofSubset B) q).inv),
    tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, Iso.inv_hom_id, id_tensorHom_id,
    Category.id_comp, ← homologyMap_comp, ← cubicalCrossProductPairToSingular_def,
    homologyMap_cubicalCrossProductPairToSingular, singularCrossProductPairOfCubical_def,
    homologyMap_comp, TopPair.singularCubicalHomologyIso_inv,
    TopPair.singularCubicalHomologyIso_inv]
  refine (homologyCross_naturality_assoc (cubicalToSingularRel k (ofSubset A))
    (cubicalToSingularRel k (ofSubset B)) p q n h _).symm.trans ?_
  rw [homologyMap_comp, Category.assoc]

end TauCeti

end

end
