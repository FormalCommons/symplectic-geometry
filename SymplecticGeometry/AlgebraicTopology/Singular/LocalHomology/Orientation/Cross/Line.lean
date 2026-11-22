/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import SymplecticGeometry.AlgebraicTopology.Singular.Contractible
public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.Connecting
public import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePoint
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Sheets
public import SymplecticGeometry.AlgebraicTopology.Singular.Nullhomotopic
public import SymplecticGeometry.AlgebraicTopology.Singular.PairChangeOfCoefficients
public import SymplecticGeometry.Algebra.Category.ModuleCat.ULiftTensor

/-!
# The sign of the cross product of local orientations with the real line

Let `F` be a real normed space of dimension `m + 1`, `z` a local orientation of `F` at the
origin, and `ι` the local orientation of `ℝ` selected by its standard orientation. The cross
product `z × ι` (`TauCeti.LocalOrientation.cross`) and Tau Ceti's ordered product
`TauCeti.LocalOrientation.prod z ι` differ by the sign `TauCeti.LocalOrientation.crossSign m 0`.
This file shows that this sign is `(-1) ^ (m + 1)`
(`TauCeti.LocalOrientation.crossSign_zero_right`).

Both classes are read through the connecting morphism of `(F × ℝ, (F × ℝ) ∖ {0})` followed by the
map to the homology of `(F × ℝ) ∖ {0}` relative to `(F ∖ {0}) × ℝ`, which is injective
(`TauCeti.injective_singularHomologyπ_singularHomologyδ_prod`): `F × ℝ` is contractible and the
inclusion of `(F ∖ {0}) × ℝ` into `(F × ℝ) ∖ {0}` is nullhomotopic. For `t ≠ 0` let `jₜ` be the
sheet `x ↦ (x, t)` (`TauCeti.prodSheetPairMap`).

* The ordered product goes to `j₋₁ z - j₁ z`
  (`TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_prod`, from the suspension that
  builds Tau Ceti's sphere generators).
* The cross product goes to `(-1) ^ (m + 1) • (j₋₁ z - j₁ z)`
  (`TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_cross`). The connecting morphism
  of the product of the pairs `(F, F ∖ {0})` and `(ℝ, ℝ ∖ {0})` in the second factor
  (`TopCat.singularHomologyCrossRelPair_comp_singularHomologyδ_comp_singularHomologyπ`) sends
  `z × ι` to `(-1) ^ (m + 1)` times the image of the relative cross product `z × δι`. The
  boundary `δι` is `[-1] - [1]` in `H₀(ℝ ∖ {0})` (`TauCeti.singularHomologyδ_localOrientation_real`,
  from Tau Ceti's generator `[-b 0] - [b 0]` of the reduced homology of the zero-sphere), and the
  relative cross product with the class of a point `t` is the map induced by `jₜ`
  (`TopCat.singularHomology₀Section_singularHomologyCrossRel`).

The two classes are local orientations of `F × ℝ`, which are not their own reversals, so the
sign is `(-1) ^ (m + 1)`.

## Main results

* `TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_real` and
  `TauCeti.singularHomologyδ_localOrientation_real`: the boundary of the local orientation of `ℝ`.
* `TauCeti.injective_singularHomologyπ_singularHomologyδ_prod`: the reading map is injective.
* `TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_cross`: the cross product read on
  the sheets.
* `TauCeti.LocalOrientation.crossSign_zero_right`: `crossSign m 0 = (-1) ^ (m + 1)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (the homology of spheres), Section 3.3 (local orientations) and Section 3.B (the
  relative cross product and its boundary formula).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Section 9.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits AlgebraicTopology Metric
  Module Set

universe v u

namespace TauCeti

section Real

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (R : C)

/-- **The boundary of the local homology generator of the line.** The inverse of the oriented local
homology isomorphism `H₁(ℝ, ℝ ∖ {0}; R) ≅ R` of the identity chart, for the standard orientation
of `ℝ`, followed by the connecting morphism of `(ℝ, ℝ ∖ {0})`, is `[-1] - [1]`, the difference of
the classes of the points `-1` and `1` of `ℝ ∖ {0}`. -/
theorem singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_real :
    (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl ℝ) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) (Basis.singleton (Fin 1) ℝ).orientation
        (finrank_self ℝ)).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).singularHomologyδ R 1 0 =
    singularHomology₀Section R (X := TopCat.of ({0}ᶜ : Set ℝ)) ⟨-1, by norm_num⟩ -
      singularHomology₀Section R (X := TopCat.of ({0}ᶜ : Set ℝ)) ⟨1, by norm_num⟩ := by
  let e := complSingletonHomotopyEquivSphere (0 : ℝ)
  let b : OrthonormalBasis (Fin 1) ℝ ℝ := OrthonormalBasis.singleton (Fin 1) ℝ
  have hS : reducedSingularHomologySphereIsoOfOrientation R (Basis.singleton (Fin 1) ℝ).orientation
      (finrank_self ℝ) = reducedSingularHomologySphereIso R b :=
    reducedSingularHomologySphereIsoOfOrientation_eq R _ _ b
      (congrArg Basis.orientation (Basis.toBasis_toOrthonormalBasis _ _))
  -- `H₀` of radial projection `ℝ ∖ {0} ⟶ S⁰` has a left inverse, induced by the inclusion.
  have hid : ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom e.toFun) ≫
      ((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom e.invFun) = 𝟙 _ := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor e.left_inv.some R 0
  have hhom := singularHomologyComplSingletonIsoOfOrientation_refl_hom R
    (OpenPartialHomeomorph.mem_refl_source (0 : ℝ)) (Basis.singleton (Fin 1) ℝ).orientation
    (finrank_self ℝ)
  rw [hS] at hhom
  -- The inverse of the local homology isomorphism, followed by the reduced connecting morphism
  -- and radial projection, is the inverse of the sphere generator.
  have hinv : (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl ℝ)
      (x := 0) (OpenPartialHomeomorph.mem_refl_source _) (Basis.singleton (Fin 1) ℝ).orientation
      (finrank_self ℝ)).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).reducedSingularHomologyδ R 0 ≫
        (reducedSingularHomologyFunctor R 0).map (TopCat.ofHom e.toFun) =
      (reducedSingularHomologySphereIso R b).inv := by
    rw [← cancel_mono (reducedSingularHomologySphereIso R b).hom, Iso.inv_hom_id,
      Category.assoc, Category.assoc, ← hhom, Iso.inv_hom_id]
  have : Mono (((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom e.toFun)) :=
    mono_of_mono_fac hid
  refine (cancel_mono (((singularHomologyFunctor C 0).obj R).map (TopCat.ofHom e.toFun))).1 ?_
  rw [← TopPair.reducedSingularHomologyδ_comp_ι]
  -- The reduced homology of `ℝ ∖ {0}` appears as that of the subspace of the pair, which `rw`
  -- does not identify with `TopCat.of ({0}ᶜ : Set ℝ)`.
  erw [Category.assoc, Category.assoc, ← (reducedSingularHomologyι R 0).naturality,
    reassoc_of% hinv]
  rw [reducedSingularHomologySphereIso_inv_ι, Preadditive.sub_comp,
    singularHomology₀Section_naturality, singularHomology₀Section_naturality]
  have hb : b 0 = 1 := OrthonormalBasis.singleton_apply _
  congr 2 <;> ext <;> simp [e, hb]

/-- **The boundary of the local orientation of the line.** The connecting morphism of
`(ℝ, ℝ ∖ {0})` sends the local orientation of `ℝ` selected by its standard orientation to the class
`[-1] - [1]` in `H₀(ℝ ∖ {0}; ℤ)`. -/
theorem singularHomologyδ_localOrientation_real :
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).singularHomologyδ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) 1 0 rfl
      ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ)).val =
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of ({0}ᶜ : Set ℝ))
        ⟨-1, by norm_num⟩ 1 -
      singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of ({0}ᶜ : Set ℝ))
        ⟨1, by norm_num⟩ 1 := by
  rw [Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  exact ConcreteCategory.congr_hom
    (singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_real
      (ModuleCat.of ℤ (ULift.{0} ℤ))) 1

end Real

section Prod

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The identity of `F × ℝ`, as a map from the inner pair `(A × ℝ ∪ F × B, A × ℝ)` of the triple of
`(F, A)` and `(ℝ, B)`, for `A = F ∖ {0}` and `B = ℝ ∖ {0}`, to the pair
`((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`. -/
private def prodComplZeroInnerPairMap :
    TopTriple.innerPair.obj (TopPair.prodUnionTripleFst ({0}ᶜ : Set (TopCat.of F))
      ({0}ᶜ : Set (TopCat.of ℝ))) ⟶
      TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ))) {x | (x : F × ℝ).1 ≠ 0} :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun p ↦ ⟨(TopCat.tensorObjIsoProd F ℝ).hom p.val,
      mapsTo_preimage_fst_compl_union_preimage_snd_compl (0 : F) (0 : ℝ) p.property⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun p ↦ ⟨⟨(TopCat.tensorObjIsoProd F ℝ).hom p.val,
      mapsTo_preimage_fst_compl_union_preimage_snd_compl (0 : F) (0 : ℝ) (Or.inl p.property)⟩,
      -- the first coordinate of the image, read in `F × ℝ`
      show ((TopCat.tensorObjIsoProd F ℝ).hom p.val).1 ≠ 0 by
        rw [TopCat.tensorObjIsoProd_hom_apply]; exact p.property⟩, by fun_prop⟩)
    (by ext; rfl)

omit [NormedSpace ℝ F] in
private theorem coe_prodComplZeroInnerPairMap_fst_apply (p) :
    Subtype.val (p := fun x : F × ℝ ↦ x ∈ ({0}ᶜ : Set (F × ℝ)))
        (TopPair.Hom.fst (prodComplZeroInnerPairMap (F := F)) p) =
      (TopCat.tensorObjIsoProd F ℝ).hom p.val :=
  (rfl)

omit [NormedSpace ℝ F] in
/-- The sheet `x ↦ (x, t)` of `F × ℝ` is the inclusion of `F` at the point `t` of `ℝ ∖ {0}`,
followed by the excision map of the product of the pairs and `prodComplZeroInnerPairMap`. -/
private theorem ofSubsetMap_lift_comp_prodExcisionFst_comp_prodComplZeroInnerPairMap {t : ℝ}
    (ht : t ≠ 0) :
    TopPair.ofSubsetMap (lift (𝟙 (TopCat.of F))
        (TopCat.ofHom (ContinuousMap.const F (⟨t, ht⟩ : ({0}ᶜ : Set ℝ)))))
        (B := ({0}ᶜ : Set (TopCat.of F)))
        (B' := fst (TopCat.of F) (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ⁻¹'
          ({0}ᶜ : Set (TopCat.of F))) (fun _ h ↦ h) ≫
      TopPair.prodExcisionFst ({0}ᶜ : Set (TopCat.of F)) ({0}ᶜ : Set (TopCat.of ℝ)) ≫
        prodComplZeroInnerPairMap = prodSheetPairMap ht := by
  refine TopPair.hom_ext_of_fst _ ?_
  -- The middle space is the subspace of the pair `(ℝ, ℝ ∖ {0})` and also `TopCat.of (ℝ ∖ {0})`,
  -- which agree only up to unfolding, so these steps use `erw`.
  rw [TopPair.Hom.fst_comp]
  erw [TopPair.Hom.fst_comp]
  rw [prodSheetPairMap_fst]
  ext x
  refine Subtype.ext ?_
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    coe_prodComplZeroInnerPairMap_fst_apply, TopCat.tensorObjIsoProd_hom_apply]
  erw [TopPair.prodExcisionFst_fst, TopPair.ofSubsetMap_fst]
  -- both sides are `(x, t)`; the left side is a pair of projections of it by definition
  exact Eq.trans rfl (coe_prodSheet_apply (F := F) ht (x : F)).symm

omit [NormedSpace ℝ F] in
/-- The relative cross product of a class `a` of `(F, F ∖ {0})` with the class of the point `t` of
`ℝ ∖ {0}`, carried to `((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)` and to the coefficients `ULift ℤ`, is the
image of `a` under the sheet `x ↦ (x, t)`. -/
private theorem homologyMap_singularHomologyCrossRel_singularHomology₀Section
    {p : ℕ} {t : ℝ} (ht : t ≠ 0)
    (a : ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularHomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) p : ModuleCat.{0} ℤ)) :
    HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ))) {x | (x : F × ℝ).1 ≠ 0}))) p
      (TopPair.singularHomologyMap prodComplZeroInnerPairMap
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p
        (TopPair.singularHomologyMap
          (TopPair.prodExcisionFst ({0}ᶜ : Set (TopCat.of F)) ({0}ᶜ : Set (TopCat.of ℝ)))
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p
          (TopCat.singularHomologyCrossRel (TopCat.of F)
            (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ({0}ᶜ : Set (TopCat.of F))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p rfl
            (a ⊗ₜ singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
              (X := TopCat.of ({0}ᶜ : Set ℝ)) ⟨t, ht⟩ 1)))) =
      TopPair.singularHomologyMap (prodSheetPairMap (F := F) ht)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) p a := by
  have hpt := ConcreteCategory.congr_hom
    (TopCat.singularHomology₀Section_singularHomologyCrossRel (TopCat.of F)
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ({0}ᶜ : Set (TopCat.of F))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p
      (⟨t, ht⟩ : ({0}ᶜ : Set ℝ))
      (ModuleCat.ofHom (ULift.moduleEquiv.symm : ℤ ≃ₗ[ℤ] ULift.{0} ℤ).toLinearMap)) a
  have hpt' : TopCat.singularHomologyCrossRel (TopCat.of F)
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ({0}ᶜ : Set (TopCat.of F))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p rfl
      (a ⊗ₜ singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ))
        (X := TopCat.of ({0}ᶜ : Set ℝ)) ⟨t, ht⟩ 1) =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (lift (𝟙 (TopCat.of F))
          (TopCat.ofHom (ContinuousMap.const F (⟨t, ht⟩ : ({0}ᶜ : Set ℝ)))))
          (B := ({0}ᶜ : Set (TopCat.of F)))
          (B' := fst (TopCat.of F) (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ⁻¹'
            ({0}ᶜ : Set (TopCat.of F))) (fun _ h ↦ h))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p
        (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map
          ((ρ_ (ModuleCat.of ℤ (ULift.{0} ℤ))).inv ≫ ModuleCat.of ℤ (ULift.{0} ℤ) ◁
            ModuleCat.ofHom (ULift.moduleEquiv.symm : ℤ ≃ₗ[ℤ] ULift.{0} ℤ).toLinearMap)).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))))) p a) :=
    -- `ρ⁻¹` and the whiskering act on `a ⊗ 1` by definition, and `ULift.up 1 = 1`
    (Eq.trans rfl hpt).trans rfl
  have hj := (congrArg (_ ≫ ·) (TopPair.singularHomologyMap_comp _ _ _ _).symm).trans
    ((TopPair.singularHomologyMap_comp _ _ _ _).symm.trans
      (congrArg (TopPair.singularHomologyMap ·
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p)
      (ofSubsetMap_lift_comp_prodExcisionFst_comp_prodComplZeroInnerPairMap (F := F) ht)))
  have hc := TopPair.singularHomologyMap_coefficient_naturality (prodSheetPairMap (F := F) ht)
    (ModuleCat.uliftTensorSelfIso ℤ).hom p
  rw [← hj] at hc
  have hc' := ConcreteCategory.congr_hom hc
    (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map
      ((ρ_ (ModuleCat.of ℤ (ULift.{0} ℤ))).inv ≫ ModuleCat.of ℤ (ULift.{0} ℤ) ◁
        ModuleCat.ofHom (ULift.moduleEquiv.symm : ℤ ≃ₗ[ℤ] ULift.{0} ℤ).toLinearMap)).app
      (TopPair.toSSetPair.obj (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))))) p a)
  simp only [ConcreteCategory.comp_apply] at hc'
  -- As above, `erw` sees through the two forms of `ℝ ∖ {0}`.
  erw [hpt']
  refine hc'.symm.trans (congrArg _ ?_)
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, ← NatTrans.comp_app,
    ← Functor.map_comp, ModuleCat.rightUnitor_inv_whiskerLeft_uliftTensorSelfIso_hom ℤ,
    CategoryTheory.Functor.map_id, NatTrans.id_app, HomologicalComplex.homologyMap_id]
  -- the identity applied to `a`
  rfl

/-- The inclusion of `(F ∖ {0}) × ℝ` into `(F × ℝ) ∖ {0}` is nullhomotopic: it contracts onto
`(0, 1)` along `s ↦ ((1 - s) x, (1 - s) t + s)`. -/
theorem nullhomotopic_map_prodComplZeroPair :
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
      {x | (x : F × ℝ).1 ≠ 0}).map.hom.Nullhomotopic := by
  refine ⟨⟨(0, 1), by simp⟩, ⟨{
    toFun := fun q ↦ ⟨((1 - (q.1 : ℝ)) • (q.2.val : F × ℝ).1,
      (1 - (q.1 : ℝ)) * (q.2.val : F × ℝ).2 + q.1), fun h ↦ ?_⟩
    continuous_toFun := by fun_prop
    map_zero_left := fun x ↦ Subtype.ext (Prod.ext (by simp; rfl) (by simp; rfl))
    map_one_left := fun x ↦ Subtype.ext (Prod.ext (by simp; rfl) (by simp; rfl)) }⟩⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Prod.fst_zero, Prod.snd_zero, smul_eq_zero, sub_eq_zero] at h1 h2
  rcases h1 with h1 | h1
  · rw [← h1, sub_self, zero_mul, zero_add] at h2
    exact one_ne_zero h2
  · exact q.2.property h1

/-- The connecting morphism of `(F × ℝ, (F × ℝ) ∖ {0})` in positive degree, followed by the map
`Hₘ₊₁((F × ℝ) ∖ {0}) ⟶ Hₘ₊₁((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`, is injective: `F × ℝ` is
contractible, and the inclusion of `(F ∖ {0}) × ℝ` into `(F × ℝ) ∖ {0}` is nullhomotopic. -/
theorem injective_singularHomologyπ_singularHomologyδ_prod (m : ℕ) :
    Function.Injective fun x ↦
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl x) := by
  have hπ : Mono ((TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
      {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)) :=
    ((TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
      {x | (x : F × ℝ).1 ≠ 0}).singularHomology_exact_space _ (m + 1)).mono_g
      (TopCat.singularHomologyFunctor_map_eq_zero_of_nullhomotopic _
        nullhomotopic_map_prodComplZeroPair m.succ_ne_zero)
  have : ContractibleSpace (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).fst :=
    inferInstanceAs (ContractibleSpace (F × ℝ))
  exact ((ModuleCat.mono_iff_injective _).1 hπ).comp ((ModuleCat.mono_iff_injective _).1
    (TopPair.mono_singularHomologyδ_of_contractibleSpace _ _ (m + 1)))

omit [NormedSpace ℝ F] in
/-- The first steps of `TauCeti.LocalOrientation.singularHomologyπ_singularHomologyδ_cross`: the
coefficient change `ULift ℤ ⊗ ULift ℤ ⟶ ULift ℤ` and the identification of `F × ℝ` with the
product of the pairs commute with the connecting morphisms and with the maps to relative
homology. -/
private theorem singularHomologyπ_singularHomologyδ_localHomologyCross {m : ℕ}
    (y : ((TopPair.ofSubset (fst (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of F)) ∪
      snd (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of ℝ)))).singularHomology
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) :
          ModuleCat.{0} ℤ)) :
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl
        (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
          (ModuleCat.uliftTensorSelfIso ℤ).hom).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))))) (m + 2)
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
            (mapsTo_preimage_fst_compl_union_preimage_snd_compl (0 : F) (0 : ℝ)))
            (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) y))) =
    HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app (TopPair.toSSetPair.obj
          (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ))) {x | (x : F × ℝ).1 ≠ 0})))
      (m + 1)
      (TopPair.singularHomologyMap prodComplZeroInnerPairMap
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
        ((TopTriple.innerPair.obj (TopPair.prodUnionTripleFst ({0}ᶜ : Set (TopCat.of F))
          ({0}ᶜ : Set (TopCat.of ℝ)))).singularHomologyπ
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
          ((TopPair.ofSubset (fst (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of F)) ∪
            snd (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of ℝ)))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl
            y))) := by
  have h₁ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyδ_coefficient_naturality
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))) (ModuleCat.uliftTensorSelfIso ℤ).hom
      (m + 2) (m + 1) rfl)
  simp only [ConcreteCategory.comp_apply] at h₁
  rw [← h₁]
  have h₂ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_coefficient_naturality
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ))) {x | (x : F × ℝ).1 ≠ 0})
      (ModuleCat.uliftTensorSelfIso ℤ).hom (m + 1))
  simp only [ConcreteCategory.comp_apply] at h₂
  -- The homology of `(F × ℝ) ∖ {0}` is that of the subspace of `(F × ℝ, (F × ℝ) ∖ {0})` and that
  -- of the ambient space of the next pair, which agree only up to unfolding: hence `erw`.
  erw [h₂]
  have h₃ := ConcreteCategory.congr_hom (TopPair.singularHomologyδ_naturality
    (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ))
    (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl (0 : F) (0 : ℝ)))
    (m + 2) (m + 1) rfl)
  erw [← h₃]
  have hg : TopPair.Hom.fst (prodComplZeroInnerPairMap (F := F)) = TopPair.Hom.snd
      (TopPair.ofSubsetMap _
        (mapsTo_preimage_fst_compl_union_preimage_snd_compl (0 : F) (0 : ℝ))) := by
    ext p
    refine Subtype.ext ?_
    erw [TopPair.ofSubsetMap_snd_apply]
    -- both are the image of `p` in `F × ℝ`
    rfl
  have h₄ := ConcreteCategory.congr_hom
    (TopPair.singularHomologyπ_naturality (f := prodComplZeroInnerPairMap (F := F))
      (R := ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (n := m + 1))
  rw [hg] at h₄
  erw [h₄]
  -- the composite applied to an element is the composition of the applications
  rfl

/-- **The cross product of a local orientation with that of the line, read on the sheets.** Let
`F` be a real normed space of dimension `m + 1`, `z` a local orientation of `F` at `0`, and `ι`
the local orientation of `ℝ` selected by its standard orientation. The connecting morphism of
`(F × ℝ, (F × ℝ) ∖ {0})`, followed by the map
`Hₘ₊₁((F × ℝ) ∖ {0}) ⟶ Hₘ₊₁((F × ℝ) ∖ {0}, (F ∖ {0}) × ℝ)`, sends the cross product `z × ι` to
`(-1) ^ (m + 1) • (j₋₁ z - j₁ z)`, where `jₜ` is the sheet `x ↦ (x, t)`
(`TauCeti.prodSheetPairMap`). -/
theorem LocalOrientation.singularHomologyπ_singularHomologyδ_cross {m : ℕ}
    (hF : finrank ℝ F = m + 1) (z : LocalOrientation F 0 (m + 1)) :
    (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set (F × ℝ)))
        {x | (x : F × ℝ).1 ≠ 0}).singularHomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (F × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl
        (LocalOrientation.cross (n := 0) (d := m + 1) hF (finrank_self ℝ) rfl z
          ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ))).val) =
    ((-1 : ℤ) ^ (m + 1)) •
      (TopPair.singularHomologyMap (prodSheetPairMap (F := F) (neg_ne_zero.2 one_ne_zero))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val -
        TopPair.singularHomologyMap (prodSheetPairMap (F := F) one_ne_zero)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) z.val) := by
  rw [LocalOrientation.coe_cross, localHomologyCross_def]
  simp only [ConcreteCategory.comp_apply]
  erw [singularHomologyπ_singularHomologyδ_localHomologyCross]
  have h₅ := ConcreteCategory.congr_hom
    (TopCat.singularHomologyCrossRelPair_comp_singularHomologyδ_comp_singularHomologyπ
      (TopCat.of F) (TopCat.of ℝ) ({0}ᶜ : Set (TopCat.of F)) ({0}ᶜ : Set (TopCat.of ℝ))
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) 1 (m + 2) rfl
      (q' := 0) (n' := m + 1) rfl rfl)
    (z.val ⊗ₜ ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ)).val)
  have h₅' : (TopTriple.innerPair.obj (TopPair.prodUnionTripleFst ({0}ᶜ : Set (TopCat.of F))
        ({0}ᶜ : Set (TopCat.of ℝ)))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
      ((TopPair.ofSubset (fst (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of F)) ∪
          snd (TopCat.of F) (TopCat.of ℝ) ⁻¹' ({0}ᶜ : Set (TopCat.of ℝ)))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl
        (TopCat.singularHomologyCrossRelPair (TopCat.of F) (TopCat.of ℝ) ({0}ᶜ : Set (TopCat.of F))
          ({0}ᶜ : Set (TopCat.of ℝ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ))
          (m + 1) 1 (m + 2) rfl
          (z.val ⊗ₜ ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation
            (finrank_self ℝ)).val))) =
      ((-1 : ℤ) ^ (m + 1)) • TopPair.singularHomologyMap
        (TopPair.prodExcisionFst ({0}ᶜ : Set (TopCat.of F)) ({0}ᶜ : Set (TopCat.of ℝ)))
        (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)
        (TopCat.singularHomologyCrossRel (TopCat.of F)
          (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).snd ({0}ᶜ : Set (TopCat.of F))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1) 0 (m + 1) rfl
          (z.val ⊗ₜ (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℝ))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) 1 0 rfl
            ((Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ)).val)) :=
    -- the whiskering and the scalar act on `z ⊗ ι` by definition
    h₅.trans rfl
  erw [ConcreteCategory.comp_apply, h₅', map_zsmul, map_zsmul]
  congr 1
  erw [singularHomologyδ_localOrientation_real, TensorProduct.tmul_sub, map_sub, map_sub, map_sub,
    map_sub,
    homologyMap_singularHomologyCrossRel_singularHomology₀Section,
    homologyMap_singularHomologyCrossRel_singularHomology₀Section]

/-- **The sign of the cross product with the line.** The sign `crossSign m 0`, by which the cross
product of a local orientation of a real vector space of dimension `m + 1` with a local
orientation of `ℝ` differs from their ordered product `TauCeti.LocalOrientation.prod`
(`TauCeti.LocalOrientation.coe_cross_eq_crossSign_smul`), is `(-1) ^ (m + 1)`. -/
theorem LocalOrientation.crossSign_zero_right (m : ℕ) :
    LocalOrientation.crossSign m 0 = (-1) ^ (m + 1) := by
  have hF : finrank ℝ (Fin (m + 1) → ℝ) = m + 1 := Module.finrank_fin_fun ℝ
  let z := (Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation hF
  let ι := (Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ)
  let w := LocalOrientation.prod (n := 0) (d := m + 1) hF (finrank_self ℝ) rfl z ι
  have hc := LocalOrientation.coe_cross_eq_crossSign_smul (n := 0) (d := m + 1) hF
    (finrank_self ℝ) rfl z ι
  have h₁ := LocalOrientation.singularHomologyπ_singularHomologyδ_cross hF z
  have h₂ := LocalOrientation.singularHomologyπ_singularHomologyδ_prod hF z
  have key : (LocalOrientation.crossSign m 0 : ℤ) • w.val = ((-1 : ℤ) ^ (m + 1)) • w.val := by
    let Φ := ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ((Fin (m + 1) → ℝ) × ℝ)))).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 2) (m + 1) rfl ≫
      (TopPair.ofSubset (X := TopCat.of ({0}ᶜ : Set ((Fin (m + 1) → ℝ) × ℝ)))
        {x | (x : (Fin (m + 1) → ℝ) × ℝ).1 ≠ 0}).singularHomologyπ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (m + 1)).hom
    refine injective_singularHomologyπ_singularHomologyδ_prod m ?_
    exact (congrArg Φ hc.symm).trans ((h₁.trans (congrArg _ h₂.symm)).trans (map_zsmul Φ _ _).symm)
  -- A local orientation of `F × ℝ` is not its own reversal.
  have hw : w.val ≠ -w.val := by
    have hFR : finrank ℝ ((Fin (m + 1) → ℝ) × ℝ) = m + 1 + 1 := by simp
    have := FiniteDimensional.of_finrank_eq_succ hFR
    obtain ⟨ω, hω⟩ := Orientation.localOrientation_surjective hFR w
    replace hω : ω.localOrientation hFR = w := hω
    intro h
    have h' : ω.localOrientation hFR = (-ω).localOrientation hFR := by
      rw [Orientation.localOrientation_neg]
      exact Subtype.ext (by rw [hω, LocalOrientation.coe_neg]; exact h)
    exact Module.Ray.ne_neg_self ω (Orientation.localOrientation_injective hFR h')
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rcases Int.units_eq_one_or (LocalOrientation.crossSign m 0) with h | h <;>
  rcases neg_one_pow_eq_or ℤ (m + 1) with h' | h' <;>
  simp only [h, h', Units.val_one, Units.val_neg, one_zsmul, neg_one_zsmul] at key ⊢
  all_goals exact absurd (by first | exact key | exact key.symm) hw

end Prod

end TauCeti
