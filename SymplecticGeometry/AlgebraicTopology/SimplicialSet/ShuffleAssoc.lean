/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.TripleAcyclicModels

/-!
# Associativity of the shuffle map up to a natural homotopy

For simplicial sets `K`, `L`, `M` and coefficient objects `R`, `S`, `T`, there are two ways to
assemble the shuffle map `SSet.shuffle` of Eilenberg and Mac Lane into a chain map
`(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C(K × (L × M); R ⊗ (S ⊗ T))`:

* shuffle the first two factors, then the result with the third, and move the target along the
  coefficient associator `(R ⊗ S) ⊗ T ≅ R ⊗ (S ⊗ T)` and the associator
  `(K × L) × M ≅ K × (L × M)`;
* reassociate the tensor product of chain complexes, shuffle the last two factors, then the first
  with the result.

Since Tau Ceti builds `SSet.shuffle` by acyclic models, the two composites are not known to be
equal, and only their maps on homology are compared in Tau Ceti
(`TopCat.singularHomologyCross_assoc`, through the Alexander–Whitney map).  This file shows that
they are chain homotopic (`SSet.shuffleAssocHomotopy`), through a homotopy which is natural in the
three simplicial sets (`SSet.shuffleAssocHomotopy_hom_naturality`).  The parenthesization and the
associators are those of `TopCat.singularHomologyCross_assoc`.

The proof applies the acyclic-models theorem for three factors,
`SSet.tripleTensorChainComplexHomotopy`, after moving the target of the second composite to
`C((K × L) × M; R ⊗ (S ⊗ T))` along the inverse associator.  Both composites are natural by
`SSet.shuffle_naturality`, and in degree zero both send the summand of a triple of vertices
`(x, y, z)` to the vertex `((x, y), z)`, through the coefficient associator, by
`SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero`.  The construction follows that of
Tau Ceti's `SSet.alexanderWhitneyKoszulBraidingHomotopy` and its naturality lemma.

## Main definitions and results

* `SSet.shuffleAssocHomotopy`: the chain homotopy between the two iterated shuffle maps.
* `SSet.shuffleAssocHomotopy_hom_naturality`: it is natural in `K`, `L` and `M`.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* S. Eilenberg and S. Mac Lane, *Acyclic models*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L M : SSet.{w}) (R S T : C)

/-- The shuffle map of the first two factors, then that of the result with the third, followed
by the coefficient associator. -/
private def shuffleShuffleLeft :
    (K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T ⟶
      ((K ⊗ L) ⊗ M).chainComplex (R ⊗ (S ⊗ T)) :=
  (shuffle K L R S ▷ M.chainComplex T) ≫ shuffle (K ⊗ L) M (R ⊗ S) T ≫
    ((chainComplexFunctor C).map (α_ R S T).hom).app ((K ⊗ L) ⊗ M)

/-- The associator of chain complexes, the shuffle map of the last two factors and that of the
first with the result, followed by the map induced by the inverse associator
`K × (L × M) ⟶ (K × L) × M`. -/
private def shuffleShuffleRight :
    (K.chainComplex R ⊗ L.chainComplex S) ⊗ M.chainComplex T ⟶
      ((K ⊗ L) ⊗ M).chainComplex (R ⊗ (S ⊗ T)) :=
  (α_ _ _ _).hom ≫ (K.chainComplex R ◁ shuffle L M S T) ≫ shuffle K (L ⊗ M) R (S ⊗ T) ≫
    chainComplexMap (α_ K L M).inv (R ⊗ (S ⊗ T))

variable {K L M} in
/-- `SSet.shuffleShuffleLeft` is natural in the three simplicial sets. -/
private lemma shuffleShuffleLeft_naturality {K' L' M' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    (h : M ⟶ M') :
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫
        shuffleShuffleLeft K' L' M' R S T =
      shuffleShuffleLeft K L M R S T ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) (R ⊗ (S ⊗ T)) := by
  have h₁ : ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫
      (shuffle K' L' R S ▷ M'.chainComplex T) =
        (shuffle K L R S ▷ M.chainComplex T) ≫
          (chainComplexMap (f ⊗ₘ g) (R ⊗ S) ⊗ₘ chainComplexMap h T) := by
    rw [tensorHom_comp_whiskerRight, shuffle_naturality, whiskerRight_comp_tensorHom]
  simp only [shuffleShuffleLeft, reassoc_of% h₁, shuffle_naturality_assoc, Category.assoc,
    ((chainComplexFunctor C).map (α_ R S T).hom).naturality]

variable {K L M} in
/-- `SSet.shuffleShuffleRight` is natural in the three simplicial sets. -/
private lemma shuffleShuffleRight_naturality {K' L' M' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    (h : M ⟶ M') :
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T) ≫
        shuffleShuffleRight K' L' M' R S T =
      shuffleShuffleRight K L M R S T ≫ chainComplexMap ((f ⊗ₘ g) ⊗ₘ h) (R ⊗ (S ⊗ T)) := by
  have h₁ : (chainComplexMap f R ⊗ₘ (chainComplexMap g S ⊗ₘ chainComplexMap h T)) ≫
      (K'.chainComplex R ◁ shuffle L' M' S T) =
        (K.chainComplex R ◁ shuffle L M S T) ≫
          (chainComplexMap f R ⊗ₘ chainComplexMap (g ⊗ₘ h) (S ⊗ T)) := by
    rw [tensorHom_comp_whiskerLeft, shuffle_naturality, whiskerLeft_comp_tensorHom]
  simp only [shuffleShuffleRight, associator_naturality_assoc, reassoc_of% h₁,
    shuffle_naturality_assoc, Category.assoc, ← Functor.map_comp,
    MonoidalCategory.associator_inv_naturality]

/-- In degree zero, the two iterated shuffle maps agree: both send the summand of a triple of
vertices `(x, y, z)` to the summand of the vertex `((x, y), z)`, through the coefficient
associator. -/
private lemma shuffleShuffleLeft_f_zero :
    (shuffleShuffleLeft K L M R S T).f 0 = (shuffleShuffleRight K L M R S T).f 0 := by
  refine tripleTensorChainComplex_X_hom_ext fun p q r hpqr x y z ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ : p = 0 ∧ q = 0 ∧ r = 0 := by omega
  rw [shuffleShuffleLeft, shuffleShuffleRight, ιTripleTensorChainComplex_def]
  simp only [comp_f, Category.assoc]
  rw [ι_whiskerRight_assoc]
  -- the vertices `(x, y)`, `(y, z)`, `((x, y), z)` and `(x, (y, z))` of the products, named so
  -- that the terms below stay well typed when rewriting
  obtain ⟨xy, hxy⟩ : ∃ v : (K ⊗ L) _⦋0⦌, v = (x, y) := ⟨_, rfl⟩
  obtain ⟨yz, hyz⟩ : ∃ v : (L ⊗ M) _⦋0⦌, v = (y, z) := ⟨_, rfl⟩
  obtain ⟨xyz, hxyz⟩ : ∃ v : ((K ⊗ L) ⊗ M) _⦋0⦌, v = (xy, z) := ⟨_, rfl⟩
  obtain ⟨xyz', hxyz'⟩ : ∃ v : (K ⊗ (L ⊗ M)) _⦋0⦌, v = (x, yz) := ⟨_, rfl⟩
  have hKL : (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
      ιTensorObj (K.chainComplex R) (L.chainComplex S) 0 0 (0 + 0) rfl ≫
        (shuffle K L R S).f (0 + 0) = (K ⊗ L).ιChainComplex xy :=
    hxy ▸ ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero K L R S x y
  have hKLM : ((K ⊗ L).ιChainComplex xy ⊗ₘ M.ιChainComplex z) ≫
      ιTensorObj ((K ⊗ L).chainComplex (R ⊗ S)) (M.chainComplex T) (0 + 0) 0 0 hpqr ≫
        (shuffle (K ⊗ L) M (R ⊗ S) T).f 0 = ((K ⊗ L) ⊗ M).ιChainComplex xyz :=
    hxyz ▸ ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero (K ⊗ L) M (R ⊗ S) T xy z
  have hLM : (L.ιChainComplex y ⊗ₘ M.ιChainComplex z) ≫
      ιTensorObj (L.chainComplex S) (M.chainComplex T) 0 0 0 rfl ≫
        (shuffle L M S T).f 0 = (L ⊗ M).ιChainComplex yz :=
    hyz ▸ ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero L M S T y z
  have hKLM' : (K.ιChainComplex x ⊗ₘ (L ⊗ M).ιChainComplex yz) ≫
      ιTensorObj (K.chainComplex R) ((L ⊗ M).chainComplex (S ⊗ T)) 0 0 0 rfl ≫
        (shuffle K (L ⊗ M) R (S ⊗ T)).f 0 = (K ⊗ (L ⊗ M)).ιChainComplex xyz' :=
    hxyz' ▸ ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero K (L ⊗ M) R (S ⊗ T) x yz
  rw [ι_ι_associator_hom_assoc _ _ _ 0 0 0 (0 + 0) 0 0 rfl rfl hpqr rfl,
    tensorHom_def'_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    Category.assoc, hKL, ← tensorHom_def'_assoc, reassoc_of% hKLM,
    associator_naturality_assoc, ι_whiskerLeft_assoc, tensorHom_comp_whiskerLeft_assoc,
    tensorHom_comp_whiskerLeft_assoc, Category.assoc, hLM, reassoc_of% hKLM',
    ιChainComplex_chainComplexFunctor_map_app_f, ι_chainComplexMap_f]
  -- the inverse associator sends `(x, (y, z))` to `((x, y), z)`, by definition
  subst hxy hyz hxyz hxyz'
  rfl


/-- **Associativity of the shuffle map up to homotopy.**  The two iterated shuffle maps
`(C(K; R) ⊗ C(L; S)) ⊗ C(M; T) ⟶ C(K × (L × M); R ⊗ (S ⊗ T))` are chain homotopic: the shuffle
map of `K × L` followed by that of `(K × L) × M`, the coefficient associator and the associator
of the simplicial sets, and the associator of chain complexes followed by the shuffle map of
`L × M` and that of `K × (L × M)`.  The homotopy is natural in the three simplicial sets
(`SSet.shuffleAssocHomotopy_hom_naturality`). -/
def shuffleAssocHomotopy :
    Homotopy ((shuffle K L R S ▷ M.chainComplex T) ≫ shuffle (K ⊗ L) M (R ⊗ S) T ≫
        ((chainComplexFunctor C).map (α_ R S T).hom).app ((K ⊗ L) ⊗ M) ≫
          chainComplexMap (α_ K L M).hom (R ⊗ (S ⊗ T)))
      ((α_ _ _ _).hom ≫ (K.chainComplex R ◁ shuffle L M S T) ≫ shuffle K (L ⊗ M) R (S ⊗ T)) :=
  (Homotopy.ofEq (by simp only [shuffleShuffleLeft, Category.assoc])).trans <|
    ((tripleTensorChainComplexHomotopy (fun K L M ↦ shuffleShuffleLeft K L M R S T)
      (fun K L M ↦ shuffleShuffleRight K L M R S T)
      (fun _ _ _ _ _ _ f g h ↦ shuffleShuffleLeft_naturality R S T f g h)
      (fun _ _ _ _ _ _ f g h ↦ shuffleShuffleRight_naturality R S T f g h)
      (fun K L M ↦ shuffleShuffleLeft_f_zero K L M R S T) K L M).compRight
        (chainComplexMap (α_ K L M).hom (R ⊗ (S ⊗ T)))).trans <|
      -- cancelling the inverse associator `K × (L × M) ⟶ (K × L) × M` against the associator
      Homotopy.ofEq (by
        rw [shuffleShuffleRight, Category.assoc, Category.assoc, Category.assoc,
          ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id])

variable {K L M} in
/-- The homotopy of `SSet.shuffleAssocHomotopy` is natural in the three simplicial sets: maps
`f : K ⟶ K'`, `g : L ⟶ L'` and `h : M ⟶ M'` intertwine it with the homotopy for `K'`, `L'` and
`M'`, the chains of the target being mapped by `f × (g × h)`. -/
@[reassoc]
lemma shuffleAssocHomotopy_hom_naturality {K' L' M' : SSet.{w}} (f : K ⟶ K') (g : L ⟶ L')
    (h : M ⟶ M') (i j : ℕ) :
    ((chainComplexMap f R ⊗ₘ chainComplexMap g S) ⊗ₘ chainComplexMap h T).f i ≫
        (shuffleAssocHomotopy K' L' M' R S T).hom i j =
      (shuffleAssocHomotopy K L M R S T).hom i j ≫
        (chainComplexMap (f ⊗ₘ (g ⊗ₘ h)) (R ⊗ (S ⊗ T))).f j := by
  simp only [shuffleAssocHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compRight_hom, Pi.zero_apply, zero_add, add_zero]
  rw [tripleTensorChainComplexHomotopy_hom_naturality_assoc, Category.assoc,
    chainComplexMap_f_comp, chainComplexMap_f_comp,
    MonoidalCategory.associator_naturality]

end SSet

end
