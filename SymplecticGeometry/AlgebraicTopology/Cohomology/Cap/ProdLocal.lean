/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.LinearAlgebra.Orientation.Prod
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.CrossRelPair
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Sign

/-!
# The local cap computation on a product of vector spaces

Let `P` and `Q` be real normed spaces, of dimensions `r` and `m`, with orientations `ω` of `P`
and `ω'` of `Q`. Take the cross product of the local orientations of `P` and `Q` at the origin,
normal factor `P` first (`TauCeti.LocalOrientation.cross`), read it relative to
`(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with the pull-back along the first projection of the generator
`Orientation.modelThomGenerator ω` of `Hʳ(P, P ∖ 0; ℤ)`, with the cap product of the excisive
couple `((P ∖ 0) × Q, P × (Q ∖ 0))` (`TopCat.singularRelativeCap`), and push the result forward
along the second projection. The result is the local orientation of `ω'`
(`Orientation.singularRelativeCap_modelThomGenerator_cross_localOrientation`).

The computation holds for any classes and any points: for points `x ∈ X` and `y ∈ Y` of `T₁`
spaces, a class `u ∈ Hᵖ(X, X ∖ x; ℤ)` and local homology classes `o` at `x` and `z` at `y`,
the same construction applied to the local homology cross product
`SymplecticGeometry.localHomologyCross` of `o` and `z` gives `⟨u, o⟩ • z`
(`SymplecticGeometry.singularRelativeCap_localHomologyCross`). This is
`TopCat.singularRelativeCap_singularHomologyCrossRelPair_ulift`, once the local cross product is
read back as the cross product of the pairs
(`SymplecticGeometry.localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv`).

Take for `o` the local orientation of `ω` and for `u` the generator, so that `⟨u, o⟩ = 1`
(`Orientation.kronecker_localCohomologyClass`). Then the construction gives back any local class
`z` of `Q`, in any degree and with no hypothesis on `Q`
(`Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_localOrientation`). The
local cap computation is the case where `z` is the local orientation of `ω'`, and the case
`m = 0` is the case where `Q` is a point and `z` any class of `H₀(Q, Q ∖ 0; ℤ)`.

The cross product is also the local orientation of the orientation of `P × Q` that puts `ω'`
first: `ω'.prod ω` of `Q × P`, carried to `P × Q` by the exchange of factors. This is
`TauCeti.LocalOrientation.cross_eq_map_prodComm_prod` with Tau Ceti's
`TauCeti.LocalOrientation.prod_localOrientation` and `Orientation.localOrientation_map`, so that
no sign is counted
(`Orientation.singularRelativeCap_modelThomGenerator_localOrientation_map_prodComm`).

When `r = 0`, `Orientation.localOrientation` does not apply and the point class of `P` takes its
place. The general formula then shows that the generator pairs with the point class of `P` to
`±1`, the sign of `ω`
(`Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_of_zero`).

## Main results

* `SymplecticGeometry.singularRelativeCap_localHomologyCross`:
  `pr₂_*((o × z) ⌢ pr₁^* u) = ⟨u, o⟩ • z` for the cross product of local homology classes.
* `Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_localOrientation`: the
  cross product of the local orientation of `ω` with any local class `z` of `Q` gives back `z`;
  for `Q` a point, this is the case `m = 0`.
* `Orientation.singularRelativeCap_modelThomGenerator_cross_localOrientation`: the local cap
  computation, for `r = k + 1` and `m = l + 1`, normal factor first.
* `Orientation.singularRelativeCap_modelThomGenerator_localOrientation_map_prodComm`: the same, with
  the cross product read as the local orientation of the orientation that puts `ω'` first.
* `Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_of_zero`: the case
  `r = 0`.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, Sections 6 and 7 (the cap product of cross
  products, and the Thom isomorphism).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §11 (the Thom class and the dual class of a submanifold).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Module TauCeti

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace SymplecticGeometry

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]

/-- **Capping a local cross product with a class of the first factor**,
`pr₂_*((o × z) ⌢ pr₁^* u) = ⟨u, o⟩ • z`: for points `x ∈ X` and `y ∈ Y` of `T₁` spaces, a class
`u ∈ Hᵖ(X, X ∖ x; ℤ)` with chain coefficients and values `ULift ℤ`, and local homology classes
`o ∈ Hₚ(X, X ∖ x; ℤ)` and `z ∈ H_q(Y, Y ∖ y; ℤ)`, read the cross product
`localHomologyCross x y p q n h (o ⊗ z)` relative to `(X ∖ x) × Y ∪ X × (Y ∖ y)`, cap it with the
pull-back of `u` along the first projection, with the cap product of the excisive couple
`((X ∖ x) × Y, X × (Y ∖ y))` along the right unitor of `ULift ℤ`, and push forward along the
second projection to `H_q(Y, Y ∖ y; ℤ)`. The result is `z` scaled by the Kronecker pairing
`⟨u, o⟩`. -/
theorem singularRelativeCap_localHomologyCross (x : X) (y : Y) {p q n : ℕ} (h : p + q = n)
    (u : (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))).singularCohomology
      (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{0} ℤ)) p)
    (o : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p)
    (z : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set Y) q) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (snd (TopCat.of X) (TopCat.of Y)) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q
        (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom
          (fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X)))
          (snd (TopCat.of X) (TopCat.of Y) ⁻¹' ({y}ᶜ : Set (TopCat.of Y)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton) p q n h
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of X) (TopCat.of Y)) (Set.mapsTo_preimage _ _)) p u)
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
              (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl x y))
            (ModuleCat.of ℤ (ULift.{0} ℤ)) n
            ((localHomologyCross x y p q n h).hom (o ⊗ₜ z)))) =
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X))).singularKronecker ℤ p u o).down • z := by
  subst h
  have hcancel : ∀ (T : SSetPair) w, HomologicalComplex.homologyMap
      (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app T) (p + q)
      (HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).inv).app T) (p + q) w) = w := fun T w ↦ by
    rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp, ← NatTrans.comp_app,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      HomologicalComplex.homologyMap_id, ModuleCat.id_apply]
  -- The local cross product, read back relative to `(X ∖ x) × Y ∪ X × (Y ∖ y)`, is the cross
  -- product of the pairs with its coefficients multiplied.
  have hback : TopPair.singularHomologyMap (TopPair.ofSubsetMap _
        (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl x y))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (p + q)
        ((localHomologyCross x y p q (p + q) rfl).hom (o ⊗ₜ z)) =
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) (p + q)
        (TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q (p + q) rfl
          (o ⊗ₜ z)) := by
    rw [← localHomologyCross_comp_homologyMap_uliftTensorSelfIso_inv_apply x y p q (p + q) rfl]
    -- The multiplication of the coefficients and its inverse cancel.
    exact (hcancel _ _).symm
  rw [hback]
  exact TopCat.singularRelativeCap_singularHomologyCrossRelPair_ulift isOpen_compl_singleton
    isOpen_compl_singleton u o z

end SymplecticGeometry

namespace Orientation

open SymplecticGeometry

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {k l d : ℕ}

omit [NormedSpace ℝ Q] in
/-- **Capping the cross product of a local orientation with the generator.** For an orientation
`ω` of `P`, of dimension `k + 1`, and any local class `z ∈ H_q(Q, Q ∖ 0; ℤ)`, in any degree `q`
and with no hypothesis on `Q`, read the local cross product of the local orientation selected by
`ω` with `z` relative to `(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with the pull-back of
`ω.modelThomGenerator hP` along the first projection, and push forward along the second
projection: the result is `z`. Taking for `z` the local orientation selected by an orientation of
`Q` gives the local cap computation
(`singularRelativeCap_modelThomGenerator_cross_localOrientation`); taking `Q` of dimension zero
and `q = 0` gives its case `m = 0`, which no cross product of local orientations covers. -/
theorem singularRelativeCap_modelThomGenerator_localHomologyCross_localOrientation
    {q n : ℕ} (hP : finrank ℝ P = k + 1) (h : k + 1 + q = n) (ω : Orientation ℝ P (Fin (k + 1)))
    (z : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set Q) q) :
    haveI := FiniteDimensional.of_finrank_eq_succ hP
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q
        (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          (k + 1) q n h
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
            (k + 1) (ω.modelThomGenerator hP))
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
              (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
                (0 : P) (0 : Q))) (ModuleCat.of ℤ (ULift.{0} ℤ)) n
            ((localHomologyCross (0 : P) (0 : Q) (k + 1) q n h).hom
              ((ω.localOrientation hP).val ⊗ₜ z)))) = z := by
  have := FiniteDimensional.of_finrank_eq_succ hP
  rw [modelThomGenerator_eq_localCohomologyClass, singularRelativeCap_localHomologyCross,
    kronecker_localCohomologyClass]
  exact one_smul ℤ _

/-- **The local cap computation**, normal factor first. For orientations `ω` of `P` and `ω'` of
`Q`, of dimensions `k + 1` and `l + 1`, read the cross product of their local orientations at the
origin, `P` first, relative to `(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with the pull-back along the
first projection of the generator `ω.modelThomGenerator hP` of `Hᵏ⁺¹(P, P ∖ 0; ℤ)`, with the cap
product of the excisive couple `((P ∖ 0) × Q, P × (Q ∖ 0))`, and push forward along the second
projection. The result is the local orientation of `Q` selected by `ω'`. -/
theorem singularRelativeCap_modelThomGenerator_cross_localOrientation
    (hP : finrank ℝ P = k + 1) (hQ : finrank ℝ Q = l + 1) (hd : k + 1 + (l + 1) = d + 1)
    (ω : Orientation ℝ P (Fin (k + 1))) (ω' : Orientation ℝ Q (Fin (l + 1))) :
    haveI := FiniteDimensional.of_finrank_eq_succ hP
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (l + 1)
        (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          (k + 1) (l + 1) (d + 1) hd
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
            (k + 1) (ω.modelThomGenerator hP))
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
              (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
                (0 : P) (0 : Q))) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1)
            (LocalOrientation.cross hP hQ hd (ω.localOrientation hP)
              (ω'.localOrientation hQ)).val)) =
      (ω'.localOrientation hQ).val := by
  rw [LocalOrientation.coe_cross]
  exact singularRelativeCap_modelThomGenerator_localHomologyCross_localOrientation hP hd ω _

/-- **The local cap computation, with the orientation that puts `ω'` first.** For orientations
`ω` of `P` and `ω'` of `Q`, of dimensions `k + 1` and `l + 1`, take the local orientation of
`P × Q` at the origin selected by the product orientation `ω'.prod ω` of `Q × P`, carried to
`P × Q` by the exchange of factors. Read it relative to `(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with
the pull-back along the first projection of `ω.modelThomGenerator hP`, with the cap product of the
excisive couple `((P ∖ 0) × Q, P × (Q ∖ 0))`, and push forward along the second projection. The
result is the local orientation of `Q` selected by `ω'`. -/
theorem singularRelativeCap_modelThomGenerator_localOrientation_map_prodComm
    (hP : finrank ℝ P = k + 1) (hQ : finrank ℝ Q = l + 1) (hd : l + 1 + (k + 1) = d + 1)
    (ω : Orientation ℝ P (Fin (k + 1))) (ω' : Orientation ℝ Q (Fin (l + 1))) :
    haveI := FiniteDimensional.of_finrank_eq_succ hP
    haveI := FiniteDimensional.of_finrank_eq_succ hQ
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (l + 1)
        (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          (k + 1) (l + 1) (d + 1) (by omega)
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
            (k + 1) (ω.modelThomGenerator hP))
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
              (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
                (0 : P) (0 : Q))) (ModuleCat.of ℤ (ULift.{0} ℤ)) (d + 1)
            (((Orientation.reindex ℝ (Q × P) (finCongr hd) (ω'.prod ω hQ hP)).map (Fin (d + 1))
              (ContinuousLinearEquiv.prodComm ℝ Q P).toLinearEquiv).localOrientation
                (finrank_prod_eq_succ hP hQ (by omega))).val)) =
      (ω'.localOrientation hQ).val := by
  have hd' : k + 1 + (l + 1) = d + 1 := by omega
  rw [localOrientation_map _ _ (finrank_prod_eq_succ hQ hP hd),
    ← LocalOrientation.prod_localOrientation,
    ← LocalOrientation.cross_eq_map_prodComm_prod hP hQ hd' hd]
  exact singularRelativeCap_modelThomGenerator_cross_localOrientation hP hQ hd' ω ω'

omit [NormedSpace ℝ Q] in
open Classical in
/-- **The local cap computation when the normal factor is a point.** For `P` of dimension zero,
an orientation `ω` of `P` (of the empty index type) and any class `z` of `H_q(Q, Q ∖ 0; ℤ)`, read
the local cross product of the point class of `P` with `z` relative to
`(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with the pull-back of `ω.modelThomGenerator hP` along the first
projection, and push forward along the second projection: the result is `z` when `ω` is the
positive orientation and `-z` otherwise. This is the case `r = 0` of the local cap computation. -/
theorem singularRelativeCap_modelThomGenerator_localHomologyCross_of_zero
    [FiniteDimensional ℝ P] {q : ℕ} (hP : finrank ℝ P = 0) (ω : Orientation ℝ P (Fin 0))
    (z : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set Q) q) :
    TopPair.singularHomologyMap
        (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q
        (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          0 q q (zero_add q)
          (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst (TopCat.of P) (TopCat.of Q)) (Set.mapsTo_preimage _ _))
            0 (ω.modelThomGenerator hP))
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap _
              (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
                (0 : P) (0 : Q))) (ModuleCat.of ℤ (ULift.{0} ℤ)) q
            ((localHomologyCross (0 : P) (0 : Q) 0 q q (zero_add q)).hom
              ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
                (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ z)))) =
      if ω = positiveOrientation then z else -z := by
  rw [singularRelativeCap_localHomologyCross, kronecker_modelThomGenerator_zero]
  split_ifs <;> simp

end Orientation
