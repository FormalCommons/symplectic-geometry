/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Unit
import SymplecticGeometry.AlgebraicTopology.Singular.CrossProduct
import SymplecticGeometry.Algebra.Category.ModuleCat.ULiftTensor
import SymplecticGeometry.AlgebraicTopology.Singular.PairChangeOfCoefficients

/-!
# The relative cross product with the class of a point

For a pair `(X, B)`, a space `Y`, a point `y` of `Y` and a morphism `t : 𝟙_ C ⟶ S`, this file
computes the relative cross product (`TopCat.singularHomologyCrossRel`) of a class
`a ∈ Hₚ(X, B; R)` with the class `t[y] ∈ H₀(Y; S)` of `y` weighted by `t`: it is the image of `a`
under the coefficient map `R ≅ R ⊗ 𝟙_ C ⟶ R ⊗ S`, `r ↦ r ⊗ t`, followed by the map of pairs
`(X, B) ⟶ (X × Y, B × Y)`, `x ↦ (x, y)`
(`TopCat.singularHomology₀Section_singularHomologyCrossRel`). With coefficients `ULift ℤ`,
`t = 1`, and the product `ULift ℤ ⊗ ULift ℤ ≅ ULift ℤ` applied afterwards, the change of
coefficients cancels and only the map of pairs remains
(`TopCat.singularHomologyCrossRel_singularHomology₀Section_one_uliftTensorSelfIso`).

On chains, the shuffle product with a singular vertex, followed by the projection to the first
factor, is a change of coefficients (`TopCat.rightUnitor_inv_whiskerLeft_shuffle_f_fst`, copied
from Tau Ceti's main branch into `SymplecticGeometry/AlgebraicTopology/Singular/CrossProduct.lean`);
the relative shuffle map is induced by the shuffle map, so the same holds for relative chains. The
proofs adapt that of `TopCat.singularHomology₀Section_singularHomologyCross` and of its private
step `TopCat.singularHomology₀Section_singularHomologyCross_map_fst` (Tau Ceti's main branch,
`TauCeti/AlgebraicTopology/Singular/CrossProduct.lean`, commit `ef2c0780f7`), which treat the
absolute cross product, to the relative one.

## Main results

* `TopCat.singularHomology₀Section_singularHomologyCrossRel`: the relative cross product with the
  class of a point.
* `TopCat.singularHomologyCrossRel_singularHomology₀Section_one_uliftTensorSelfIso`: its form
  over `ULift ℤ`, with the coefficients multiplied back into `ULift ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the relative cross product.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomologicalComplex Limits
  AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  (X Y : TopCat.{w}) (B : Set X) (R S : C)

/-- On relative chains, the relative shuffle product with a vertex `y`, weighted by `t`,
followed by the projection `(X × Y, B × Y) ⟶ (X, B)` is the coefficient map `r ↦ r ⊗ t`. -/
private theorem rightUnitor_inv_whiskerLeft_shuffleRel_f_fst (p : ℕ) (y : Y) (t : 𝟙_ C ⟶ S) :
    (ρ_ (((TopPair.ofSubset B).singularChainComplex R).X p)).inv ≫
        (((TopPair.ofSubset B).singularChainComplex R).X p ◁
          (t ≫ (toSSet.obj Y).ιChainComplex (toSSetObj₀Equiv.symm y))) ≫
        ιTensorObj ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
          p 0 p (add_zero p) ≫ (shuffleRel X Y B R S).f p ≫
          (TopPair.singularChainComplexMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B)) (R ⊗ S)).f p =
      (((SSetPair.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))).f p := by
  refine (cancel_epi (((TopPair.ofSubset B).singularChainComplexπ R).f p)).1 ?_
  have h₁ := congrArg (fun φ ↦ φ.f p)
    (TopCat.singularChainComplexπ_tensorHom_id_shuffleRel X Y B R S)
  have h₂ := congrArg (fun φ ↦ φ.f p) (TopPair.singularChainComplexπ_pair_naturality
    (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B)) (R ⊗ S))
  have h₃ := congrArg (fun φ ↦ φ.f p)
    (TopPair.singularChainComplexπ_coefficient_naturality (TopPair.ofSubset B)
      ((ρ_ R).inv ≫ R ◁ t))
  simp only [comp_f, TopPair.ofSubsetMap_fst] at h₁ h₂ h₃
  rw [TauCeti.singularChainComplexFunctor_map_app] at h₃
  have h₄ := ι_tensorHom ((TopPair.ofSubset B).singularChainComplexπ R)
    (𝟙 ((toSSet.obj Y).chainComplex S)) p 0 p (add_zero p)
  rw [id_f, tensorHom_id] at h₄
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, ← reassoc_of% h₄]
  -- `h₁`, `h₂` and `h₃` restated in degree `p`, with the tensor product of chain maps written as
  -- `HomologicalComplex.tensorHom` and the composites split, as in the goal; the chain complexes
  -- appear there in forms that agree with those of `h₁`, `h₂` and `h₃` only up to unfolding.
  have h₁' : (HomologicalComplex.tensorHom ((TopPair.ofSubset B).singularChainComplexπ R)
      (𝟙 ((toSSet.obj Y).chainComplex S))).f p ≫ (shuffleRel X Y B R S).f p =
      (shuffle X Y R S).f p ≫
        ((TopPair.ofSubset (fst X Y ⁻¹' B)).singularChainComplexπ (R ⊗ S)).f p := h₁
  rw [reassoc_of% h₁']
  replace h₂ : (SSet.chainComplexMap (toSSet.map (fst X Y)) (R ⊗ S)).f p ≫
      ((TopPair.ofSubset B).singularChainComplexπ (R ⊗ S)).f p = _ := h₂
  refine Eq.trans (congrArg (fun φ ↦ _ ≫ _ ≫ _ ≫ φ)
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂.symm))) ?_
  have h₅ := rightUnitor_inv_whiskerLeft_shuffle_f_fst_assoc X Y R S p y t
    (((TopPair.ofSubset B).singularChainComplexπ (R ⊗ S)).f p)
  replace h₃ : (((SSet.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app (toSSet.obj X)).f p ≫
      ((TopPair.ofSubset B).singularChainComplexπ (R ⊗ S)).f p = _ := h₃
  exact h₅.trans h₃

variable (p : ℕ)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((TopPair.ofSubset B).singularChainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles 0))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev 0)))]

/-- The relative cross product with the class of a point, followed by the projection
`(X × Y, B × Y) ⟶ (X, B)`, is the coefficient map `r ↦ r ⊗ t`. -/
private theorem singularHomology₀Section_singularHomologyCrossRel_map_fst (y : Y) (t : 𝟙_ C ⟶ S) :
    (ρ_ _).inv ≫ (_ ◁ (t ≫ TauCeti.singularHomology₀Section S y)) ≫
        singularHomologyCrossRel X Y B R S p 0 p (add_zero p) ≫
          TopPair.singularHomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B)) (R ⊗ S) p =
      homologyMap (((SSetPair.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))) p := by
  have hi : cyclesCross ((TopPair.ofSubset B).singularChainComplex R)
      ((toSSet.obj Y).chainComplex S) p 0 p (add_zero p) ≫
      ((TopPair.ofSubset B).singularChainComplex R ⊗ (toSSet.obj Y).chainComplex S).iCycles p =
      (((TopPair.ofSubset B).singularChainComplex R).iCycles p ⊗ₘ
        ((toSSet.obj Y).chainComplex S).iCycles 0) ≫ ιTensorObj _ _ p 0 p (add_zero p) :=
    cyclesCross_iCycles _ _ p 0 p (add_zero p)
  have hcycles : (ρ_ (((TopPair.ofSubset B).singularChainComplex R).cycles p)).inv ≫
      (((TopPair.ofSubset B).singularChainComplex R).cycles p ◁
        (t ≫ ((toSSet.obj Y).chainComplex S).liftCycles
          ((toSSet.obj Y).ιChainComplex (toSSetObj₀Equiv.symm y)) 0 (by simp) (by simp))) ≫
      cyclesCross ((TopPair.ofSubset B).singularChainComplex R) ((toSSet.obj Y).chainComplex S)
        p 0 p (add_zero p) ≫
      cyclesMap (shuffleRel X Y B R S ≫ TopPair.singularChainComplexMap
        (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B)) (R ⊗ S)) p =
      cyclesMap (((SSetPair.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))) p := by
    apply (cancel_mono (iCycles _ p)).1
    simp only [Category.assoc, cyclesMap_i]
    rw [reassoc_of% hi, whiskerLeft_comp_tensorHom_assoc, Category.assoc, liftCycles_i,
      rightUnitor_inv_comp_tensorHom_assoc, comp_f,
      rightUnitor_inv_whiskerLeft_shuffleRel_f_fst]
  -- The statement is proved for the homology objects of the relative singular chain complexes,
  -- which are the relative singular homology objects by definition, and read back through
  -- `singularHomologyCrossRel_def`.
  have key : (ρ_ (((TopPair.ofSubset B).singularChainComplex R).homology p)).inv ≫
      (((TopPair.ofSubset B).singularChainComplex R).homology p ◁
        (t ≫ SSet.ιHomology₀ S (toSSetObj₀Equiv.symm y))) ≫
      (homologyCross ((TopPair.ofSubset B).singularChainComplex R)
        ((toSSet.obj Y).chainComplex S) p 0 p (add_zero p) ≫
          homologyMap (shuffleRel X Y B R S) p) ≫
        homologyMap (TopPair.singularChainComplexMap
          (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B)) (R ⊗ S)) p =
      homologyMap (((SSetPair.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset B))) p := by
    apply (cancel_epi (((TopPair.ofSubset B).singularChainComplex R).homologyπ p)).1
    rw [Category.assoc, SSet.ιHomology₀_def, ← Category.assoc t,
      ← rightUnitor_inv_comp_tensorHom_assoc, ← whiskerLeft_comp_tensorHom_assoc,
      homologyπ_tensorHom_homologyCross_assoc]
    simp only [homologyπ_naturality_assoc, homologyπ_naturality]
    rw [← cyclesMap_comp_assoc, reassoc_of% hcycles]
  rw [singularHomologyCrossRel_def, TauCeti.singularHomology₀Section_def]
  exact key

/-- **The relative cross product with the class of a point.** For a point `y` of `Y` and a
morphism `t : 𝟙_ C ⟶ S`, which selects a coefficient of `S`, the relative cross product `a × t[y]`
of a class `a ∈ Hₚ(X, B; R)` with the class of `y` weighted by `t` is the image of `a` under the
coefficient map `R ≅ R ⊗ 𝟙_ C ⟶ R ⊗ S`, `r ↦ r ⊗ t`, followed by the map of pairs
`(X, B) ⟶ (X × Y, B × Y)`, `x ↦ (x, y)`. -/
@[reassoc, elementwise]
theorem singularHomology₀Section_singularHomologyCrossRel (y : Y) (t : 𝟙_ C ⟶ S) :
    (ρ_ _).inv ≫ (_ ◁ (t ≫ TauCeti.singularHomology₀Section S y)) ≫
        singularHomologyCrossRel X Y B R S p 0 p (add_zero p) =
      homologyMap (((SSetPair.chainComplexFunctor C).map ((ρ_ R).inv ≫ R ◁ t)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset B))) p ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (lift (𝟙 X) (ofHom (ContinuousMap.const X y)))
            (fun _ h ↦ h)) (R ⊗ S) p := by
  let c : Y ⟶ Y := ofHom (ContinuousMap.const Y y)
  have hc : TauCeti.singularHomology₀Section S y =
      TauCeti.singularHomology₀Section S y ≫ ((singularHomologyFunctor C 0).obj S).map c :=
    (TauCeti.singularHomology₀Section_naturality S c y).symm
  have hpair : TopPair.ofSubsetMap (𝟙 X ⊗ₘ c)
      (mapsTo_tensorHom_preimage_fst (𝟙 X) c fun _ h ↦ h) =
      TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ B) ≫
        TopPair.ofSubsetMap (lift (𝟙 X) (ofHom (ContinuousMap.const X y)))
          (fun _ h ↦ h) :=
    (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _
      (CartesianMonoidalCategory.hom_ext _ _ (by simp) (by ext; simp [c]))).symm
  have hnat := singularHomologyCrossRel_naturality X Y B R S p 0 p (add_zero p) (𝟙 X)
    (fun _ h ↦ h) c
  have hid : TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ h ↦ h) R p =
      𝟙 ((TopPair.ofSubset B).singularHomology R p) :=
    (congrArg (TopPair.singularHomologyMap · R p) (TopPair.ofSubsetMap_id _)).trans
      (TopPair.singularHomologyMap_id _ _ _)
  rw [hpair, TopPair.singularHomologyMap_comp, hid, id_tensorHom] at hnat
  rw [hc, ← Category.assoc t, whiskerLeft_comp_assoc]
  refine (congrArg (fun φ ↦ (ρ_ _).inv ≫ _ ≫ φ) hnat).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _)
    (singularHomology₀Section_singularHomologyCrossRel_map_fst X Y B R S p y t))
  simp only [Category.assoc]

/-- **The relative cross product with the class of a point, over `ℤ`.** With coefficients
`ULift ℤ`, the relative cross product of a class `a ∈ Hₚ(X, B)` with the class of a point `y`
of `Y`, carried back to `ULift ℤ` by the product `ULift ℤ ⊗ ULift ℤ ≅ ULift ℤ`, is the image
of `a` under the map of pairs `(X, B) ⟶ (X × Y, B × Y)`, `x ↦ (x, y)`. -/
theorem singularHomologyCrossRel_singularHomology₀Section_one_uliftTensorSelfIso
    (X Y : TopCat.{0}) (B : Set X) (p : ℕ) (y : Y)
    (a : ((TopPair.ofSubset B).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) p :
      ModuleCat.{0} ℤ)) :
    homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (fst X Y ⁻¹' B)))) p
      (singularHomologyCrossRel X Y B (ModuleCat.of ℤ (ULift.{0} ℤ))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p (add_zero p)
        (a ⊗ₜ TauCeti.singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) y 1)) =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (lift (𝟙 X) (ofHom (ContinuousMap.const X y))) (fun _ h ↦ h))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p a := by
  have hpt := singularHomology₀Section_singularHomologyCrossRel_apply X Y B
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p y
    (ModuleCat.ofHom (ULift.moduleEquiv.symm : ℤ ≃ₗ[ℤ] ULift.{0} ℤ).toLinearMap) a
  -- `ρ⁻¹` and the whiskering act on `a ⊗ 1` by definition, and `ULift.up 1 = 1`.
  have hpt' : singularHomologyCrossRel X Y B (ModuleCat.of ℤ (ULift.{0} ℤ))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p (add_zero p)
      (a ⊗ₜ TauCeti.singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) y 1) = _ :=
    (Eq.trans rfl hpt).trans rfl
  let f : TopPair.ofSubset B ⟶ TopPair.ofSubset (fst X Y ⁻¹' B) :=
    TopPair.ofSubsetMap (lift (𝟙 X) (ofHom (ContinuousMap.const X y))) (fun _ h ↦ h)
  have key : homologyMap (((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map
          (ρ_ (ModuleCat.of ℤ (ULift.{0} ℤ))).inv).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset B)) ≫
        ((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map (ModuleCat.of ℤ (ULift.{0} ℤ) ◁
          ModuleCat.ofHom (ULift.moduleEquiv.symm : ℤ ≃ₗ[ℤ] ULift.{0} ℤ).toLinearMap)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset B))) p ≫
      TopPair.singularHomologyMap f
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p ≫
      homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) p =
      TopPair.singularHomologyMap f (ModuleCat.of ℤ (ULift.{0} ℤ)) p := by
    rw [← TopPair.singularHomologyMap_coefficient_naturality, ← Category.assoc, ← homologyMap_comp,
      ← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
      ModuleCat.rightUnitor_inv_whiskerLeft_uliftTensorSelfIso_hom,
      CategoryTheory.Functor.map_id, NatTrans.id_app, homologyMap_id, Category.id_comp]
  rw [hpt']
  exact ConcreteCategory.congr_hom key a

end TopCat

end
