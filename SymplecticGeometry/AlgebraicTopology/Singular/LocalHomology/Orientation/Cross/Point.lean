/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.LinearAlgebra.Orientation.Prod
import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.RelativePoint
import SymplecticGeometry.AlgebraicTopology.Singular.PairChangeOfCoefficients
import TauCeti.AlgebraicTopology.Singular.Kunneth.Pair

/-!
# The cross product of local homology classes with the class of a point

This file computes the local cross product `SymplecticGeometry.localHomologyCross` when one of
the two classes is the class of a point in degree zero, Tau Ceti's `localHomologyPointClass`.

* For any spaces, a class `a` of `Hₚ(X, X ∖ {x}; ℤ)` times the class of `y` in
  `H₀(Y, Y ∖ {y}; ℤ)` is the image of `a` under the inclusion `x' ↦ (x', y)`
  (`SymplecticGeometry.localHomologyCross_tmul_localHomologyPointClass`). The cross product of
  pairs with a class that comes from the absolute homology of `Y` is the relative cross product
  read in the product of the pairs (Tau Ceti's
  `TopCat.singularHomologyCrossRel_comp_singularHomologyMap`), and over `ULift ℤ` the relative
  cross product with the class of a point is the image under that inclusion
  (`TopCat.singularHomologyCrossRel_singularHomology₀Section_one_uliftTensorSelfIso`).
* For a real normed space `P` of dimension zero and a local orientation `z` of a space `Q` of
  dimension `m + 1` at the origin, the class of the origin of `P` times `z` is the image of `z`
  under the inclusion `y ↦ (0, y)`
  (`SymplecticGeometry.localHomologyCross_localHomologyPointClass_tmul`). No cross product with
  a point on the left is computed on chains here. Instead, both sides are crossed on the left with
  a local orientation `r` of the line: the first case, the associativity of the cross product
  (`SymplecticGeometry.localHomologyCross_assoc`) and its naturality show that the two products
  agree, and the cross product with `r` of a multiple `c • v` of a local orientation `v` is
  `c` times a local orientation, which has infinite order, so `c = 1`
  (`SymplecticGeometry.eq_one_of_localHomologyCross_tmul_zsmul_eq`). The image of `z` is also
  `z` carried by the continuous linear equivalence `Q ≃ P × Q`
  (`TauCeti.LocalOrientation.coe_map_uniqueProd_symm_complZeroPairIso`, and
  `TauCeti.LocalOrientation.coe_map_prodUnique_symm_complZeroPairIso` for a factor on the right).

In terms of orientations, the local orientation of the identity chart of a zero-dimensional
space is the class of the origin (`TauCeti.localOrientationOfZeroDimChart_coe`), and a space of
dimension zero has two orientations, `positiveOrientation` and its negative. The product
orientation with the positive one is the image under the inclusion of the other factor
(`Orientation.prod_positiveOrientation_right`). Hence:

* the class of the origin of `P` times the local orientation of `ω'` is the local orientation of
  `ω'.prod ω`, carried to `P × Q` by the exchange of factors, when `ω` is the positive orientation
  of `P`, and its negative otherwise
  (`Orientation.localHomologyCross_localOrientationOfZeroDimChart_tmul_localOrientation`);
* the local orientation of `ω` times the class of the origin of `Q` is the local orientation of
  `ω.prod ω'`, when `ω'` is the positive orientation of `Q`, and its negative otherwise
  (`Orientation.localHomologyCross_localOrientation_tmul_localOrientationOfZeroDimChart`).

The sign is that of `ω` (or `ω'`), as in
`Orientation.singularRelativeCap_modelThomGenerator_localHomologyCross_of_zero`.

## Main results

* `SymplecticGeometry.localHomologyCross_tmul_localHomologyPointClass`: the cross product with
  the class of a point on the right.
* `SymplecticGeometry.localHomologyCross_localHomologyPointClass_tmul`: the cross product of a
  local orientation with the class of the origin of a zero-dimensional space on the left.
* `SymplecticGeometry.eq_one_of_localHomologyCross_tmul_zsmul_eq`: crossing with a local
  orientation tells apart the multiples of a local orientation.
* `Orientation.localHomologyCross_localOrientationOfZeroDimChart_tmul_localOrientation`,
  `Orientation.localHomologyCross_localOrientation_tmul_localOrientationOfZeroDimChart`: the same
  for the local orientations selected by orientations, with the sign of the zero-dimensional
  orientation.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B (the cross product) and Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Set Module TauCeti
open TopCat (mapsTo_preimage_fst_compl_union_preimage_snd_compl)

namespace SymplecticGeometry

section General

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The cross product with the class of a point.** For points `x` of `X` and `y` of `Y` and a
class `a` of `Hₚ(X, X ∖ {x}; ℤ)`, the cross product of `a` with the class of `y` in
`H₀(Y, Y ∖ {y}; ℤ)` is the image of `a` under the inclusion `X → X × Y`, `x' ↦ (x', y)`. -/
theorem localHomologyCross_tmul_localHomologyPointClass (x : X) (y : Y) (p : ℕ)
    (a : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p) :
    (localHomologyCross x y p 0 p (add_zero p)).hom
        (a ⊗ₜ localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set Y) y 1) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        ((ContinuousMap.id X).prodMk (ContinuousMap.const X y))
        (fun _ h ↦ congrArg Prod.fst (Set.mem_singleton_iff.1 h)) p a := by
  have hT := TopCat.singularHomologyCrossRel_comp_singularHomologyMap (TopCat.of X) (TopCat.of Y)
    ({x}ᶜ : Set (TopCat.of X)) ({y}ᶜ : Set (TopCat.of Y)) (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p (add_zero p)
  have hT' := ConcreteCategory.congr_hom hT (a ⊗ₜ singularHomology₀Section
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of Y) y 1)
  -- The maps of pairs `x' ↦ (x', y)`, from `(X × Y, X ∖ {x} × Y)` to the product of the pairs,
  -- and from there to `(X × Y, (X × Y) ∖ {(x, y)})`.
  let L : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of X)) ⟶
      TopPair.ofSubset (fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X))) :=
    TopPair.ofSubsetMap (lift (𝟙 (TopCat.of X)) (TopCat.ofHom (ContinuousMap.const X y)))
      (fun _ h ↦ h)
  let G : TopPair.ofSubset (fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X))) ⟶
      TopPair.ofSubset (fst (TopCat.of X) (TopCat.of Y) ⁻¹' ({x}ᶜ : Set (TopCat.of X)) ∪
        snd (TopCat.of X) (TopCat.of Y) ⁻¹' ({y}ᶜ : Set (TopCat.of Y))) :=
    TopPair.ofSubsetMap (𝟙 (TopCat.of X ⊗ TopCat.of Y)) (fun _ hz ↦ Or.inl hz)
  let M := TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y)
  have hF : L ≫ G ≫ M = TopPair.ofSubsetMap (B := ({x}ᶜ : Set (TopCat.of X)))
      (B' := ({(x, y)}ᶜ : Set (TopCat.of (X × Y))))
      (TopCat.ofHom ((ContinuousMap.id X).prodMk (ContinuousMap.const X y)))
      (fun x' hx' h ↦ hx' (congrArg Prod.fst h)) :=
    (congrArg (L ≫ ·) (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _
      ((mapsTo_preimage_fst_compl_union_preimage_snd_compl x y).comp fun _ hz ↦ Or.inl hz)
      rfl)).trans
      (TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (by
        ext x' <;> rw [ConcreteCategory.comp_apply, TopCat.tensorObjIsoProd_hom_apply]
        · exact ConcreteCategory.congr_hom (lift_fst (𝟙 (TopCat.of X))
            (TopCat.ofHom (ContinuousMap.const X y))) x'
        · exact ConcreteCategory.congr_hom (lift_snd (𝟙 (TopCat.of X))
            (TopCat.ofHom (ContinuousMap.const X y))) x'))
  have h1 : TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y)
      ({x}ᶜ : Set (TopCat.of X))
      ({y}ᶜ : Set (TopCat.of Y)) (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p
      (add_zero p) (a ⊗ₜ (TopPair.ofSubset ({y}ᶜ : Set (TopCat.of Y))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0
        (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of Y) y 1)) =
      TopPair.singularHomologyMap G (ModuleCat.of ℤ (ULift.{0} ℤ) ⊗ ModuleCat.of ℤ (ULift.{0} ℤ)) p
        (TopCat.singularHomologyCrossRel (TopCat.of X) (TopCat.of Y) ({x}ᶜ : Set (TopCat.of X))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p 0 p (add_zero p)
          (a ⊗ₜ singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of Y) y
            1)) := by
    rw [TopCat.singularHomologyCrossRelPair_def]
    refine Eq.trans ?_ hT'.symm
    -- `TensorProduct.map` acts on `a ⊗ s` factorwise by definition.
    rfl
  have hpc : localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({y} : Set Y) y 1 =
      (TopPair.ofSubset ({y}ᶜ : Set (TopCat.of Y))).singularHomologyπ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) 0
        (singularHomology₀Section (ModuleCat.of ℤ (ULift.{0} ℤ)) (X := TopCat.of Y) y 1) :=
    localHomologyPointClass_def_apply _ _ _ _
  rw [hpc, localHomologyCross_def, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h1,
    ← ConcreteCategory.comp_apply (TopPair.singularHomologyMap G _ p),
    ← TopPair.singularHomologyMap_comp, ← ConcreteCategory.comp_apply,
    ← TopPair.singularHomologyMap_coefficient_naturality, ConcreteCategory.comp_apply,
    TopCat.singularHomologyCrossRel_singularHomology₀Section_one_uliftTensorSelfIso,
    ← ConcreteCategory.comp_apply, ← TopPair.singularHomologyMap_comp, hF]
  exact (ConcreteCategory.congr_hom (localHomologyMap_def ..) a).symm

end General

/-- **Crossing with a local orientation detects multiples of a local orientation.** For local
orientations `r` of `E` and `v` of `F` at the origin, in the dimensions of the spaces, if
`r × (c • v) = r × v` then `c = 1`. -/
theorem eq_one_of_localHomologyCross_tmul_zsmul_eq {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {k l d : ℕ}
    (hE : finrank ℝ E = k + 1) (hF : finrank ℝ F = l + 1) (h : k + 1 + (l + 1) = d + 1)
    (r : LocalOrientation E 0 (k + 1)) (v : LocalOrientation F 0 (l + 1)) {c : ℤ}
    (hc : (localHomologyCross (0 : E) (0 : F) (k + 1) (l + 1) (d + 1) h).hom
        (r.val ⊗ₜ (c • v.val)) =
      (localHomologyCross (0 : E) (0 : F) (k + 1) (l + 1) (d + 1) h).hom (r.val ⊗ₜ v.val)) :
    c = 1 := by
  have hw := isLocalOrientation_localHomologyCross hE hF h r v
  apply (hw.linearEquiv (singularHomologyComplZeroIso (finrank_prod_eq_succ hE hF h))).injective
  rw [hw.linearEquiv_apply, hw.linearEquiv_apply, one_smul]
  refine Eq.trans ?_ hc
  rw [    show r.val ⊗ₜ (c • v.val) = c • (r.val ⊗ₜ[ℤ] v.val) from
      map_zsmul (TensorProduct.mk ℤ _ _ r.val) c v.val, map_zsmul]

end SymplecticGeometry

namespace TauCeti.LocalOrientation

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q]

/-- For a space `P` with one point, a local orientation `z` of `Q` at the origin carried to
`P × Q` by the continuous linear equivalence `y ↦ (0, y)` is the image of `z` under that
inclusion. -/
theorem coe_map_uniqueProd_symm_complZeroPairIso [Unique P] {d : ℕ}
    (z : LocalOrientation Q 0 d) :
    (z.map (ContinuousLinearEquiv.uniqueProd ℝ Q P).symm.complZeroPairIso).val =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        ((ContinuousMap.const Q (0 : P)).prodMk (ContinuousMap.id Q))
        (fun _ h ↦ congrArg Prod.snd (Set.mem_singleton_iff.1 h)) d z.val := by
  rw [coe_map, ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom]
  exact ConcreteCategory.congr_hom (localHomologyMap_congr (ModuleCat.of ℤ (ULift.{0} ℤ))
    (j₁ := (((ContinuousLinearEquiv.uniqueProd ℝ Q P).symm : Q →L[ℝ] P × Q) : C(Q, P × Q)))
    (j₂ := (ContinuousMap.const Q (0 : P)).prodMk (ContinuousMap.id Q))
    (ContinuousMap.ext fun _ ↦ Prod.ext (Subsingleton.elim (α := P) _ _) rfl) _ _) _

/-- For a space `Q` with one point, a local orientation `z` of `P` at the origin carried to
`P × Q` by the continuous linear equivalence `x ↦ (x, 0)` is the image of `z` under that
inclusion. -/
theorem coe_map_prodUnique_symm_complZeroPairIso [Unique Q] {d : ℕ}
    (z : LocalOrientation P 0 d) :
    (z.map (ContinuousLinearEquiv.prodUnique ℝ P Q).symm.complZeroPairIso).val =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        ((ContinuousMap.id P).prodMk (ContinuousMap.const P (0 : Q)))
        (fun _ h ↦ congrArg Prod.fst (Set.mem_singleton_iff.1 h)) d z.val := by
  rw [coe_map, ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom]
  exact ConcreteCategory.congr_hom (localHomologyMap_congr (ModuleCat.of ℤ (ULift.{0} ℤ))
    (j₁ := (((ContinuousLinearEquiv.prodUnique ℝ P Q).symm : P →L[ℝ] P × Q) : C(P, P × Q)))
    (j₂ := (ContinuousMap.id P).prodMk (ContinuousMap.const P (0 : Q)))
    (ContinuousMap.ext fun _ ↦ Prod.ext rfl (Subsingleton.elim (α := Q) _ _)) _ _) _

end TauCeti.LocalOrientation

namespace SymplecticGeometry

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {m : ℕ}

omit [NormedSpace ℝ P] [NormedSpace ℝ Q] in
/-- The cross product on the left with a class `w` of the line, of the class of the origin of `P`
times a class `z` of `Q`, is that of the image of `z` under `y ↦ (0, y)`: the associativity of the
cross product, the cross product with the class of a point on the right, and naturality. -/
private theorem localHomologyCross_tmul_localHomologyCross_localHomologyPointClass_tmul
    (hd : 1 + (m + 1) = m + 1 + 1)
    (w : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set ℝ) 1)
    (z : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set Q)
      (m + 1)) :
    (localHomologyCross (0 : ℝ) (0 : P × Q) 1 (m + 1) (m + 1 + 1) hd).hom
        (w ⊗ₜ (localHomologyCross (0 : P) (0 : Q) 0 (m + 1) (m + 1) (zero_add _)).hom
          (localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set P) 0 1 ⊗ₜ z)) =
      (localHomologyCross (0 : ℝ) (0 : P × Q) 1 (m + 1) (m + 1 + 1) hd).hom
        (w ⊗ₜ localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
          ((ContinuousMap.const Q (0 : P)).prodMk (ContinuousMap.id Q))
          (fun _ h ↦ congrArg Prod.snd (Set.mem_singleton_iff.1 h)) (m + 1) z) := by
  have hA := localHomologyCross_assoc_apply (0 : ℝ) (0 : P) (0 : Q) 1 0 (m + 1) 1 (m + 1)
    (m + 1 + 1) (add_zero 1) (zero_add _) hd hd
    ((w ⊗ₜ localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set P) 0 1) ⊗ₜ z)
  simp only [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply] at hA
  rw [localHomologyCross_tmul_localHomologyPointClass,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at hA
  refine hA.symm.trans ?_
  have hid {Z : Type} [TopologicalSpace Z] (zz : Z) (k : ℕ) (h) :
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id Z) (S := {zz})
        (T := {zz}) h k = 𝟙 _ := by
    rw [localHomologyMap_id]
    exact localHomologyRestriction_refl _ _ _
  have hz := ConcreteCategory.congr_hom (hid (0 : Q) (m + 1) (fun _ h ↦ h)) z
  have hw := ConcreteCategory.congr_hom (hid (0 : ℝ) 1 (fun _ h ↦ h)) w
  simp only [ConcreteCategory.id_apply] at hz hw
  have n1 := ConcreteCategory.congr_hom
    (localHomologyMap_tensorHom_localHomologyMap_localHomologyCross
    ((ContinuousMap.id ℝ).prodMk (ContinuousMap.const ℝ (0 : P))) (ContinuousMap.id Q)
    (x := 0) (x' := (0, 0)) (y := 0) (y' := 0)
    (fun _ h ↦ congrArg Prod.fst (Set.mem_singleton_iff.1 h))
    (fun _ h ↦ h) 1 (m + 1) (m + 1 + 1) hd) (w ⊗ₜ z)
  have n2 := ConcreteCategory.congr_hom
    (localHomologyMap_tensorHom_localHomologyMap_localHomologyCross
    (ContinuousMap.id ℝ) ((ContinuousMap.const Q (0 : P)).prodMk (ContinuousMap.id Q))
    (x := 0) (x' := 0) (y := 0) (y' := (0, 0)) (fun _ h ↦ h)
    (fun _ h ↦ congrArg Prod.snd (Set.mem_singleton_iff.1 h)) 1 (m + 1) (m + 1 + 1) hd)
    (w ⊗ₜ z)
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    hz, hw] at n1 n2
  rw [n1, ← ConcreteCategory.comp_apply, localHomologyMap_comp]
  refine Eq.trans ?_ n2.symm
  exact ConcreteCategory.congr_hom
    (localHomologyMap_congr _ (ContinuousMap.ext fun _ ↦ rfl) _ _) _

/-- **The cross product with the class of the origin of a zero-dimensional space, on the left.**
For a finite-dimensional real normed space `P` of dimension zero and a local orientation `z` of
`Q` at the origin, of dimension `m + 1`, the cross product of the class of the origin in
`H₀(P, P ∖ {0}; ℤ)` with `z` is the image of `z` under the inclusion `Q → P × Q`,
`y ↦ (0, y)`. -/
theorem localHomologyCross_localHomologyPointClass_tmul [FiniteDimensional ℝ P]
    (hP : finrank ℝ P = 0) (hQ : finrank ℝ Q = m + 1) (z : LocalOrientation Q 0 (m + 1)) :
    (localHomologyCross (0 : P) (0 : Q) 0 (m + 1) (m + 1) (zero_add _)).hom
        (localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set P) 0 1 ⊗ₜ z.val) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        ((ContinuousMap.const Q (0 : P)).prodMk (ContinuousMap.id Q))
        (fun _ h ↦ congrArg Prod.snd (Set.mem_singleton_iff.1 h)) (m + 1) z.val := by
  have : Subsingleton P := Module.finrank_zero_iff.1 hP
  let := uniqueOfSubsingleton (0 : P)
  have hPQ : finrank ℝ (P × Q) = m + 1 :=
    (ContinuousLinearEquiv.uniqueProd ℝ Q P).toLinearEquiv.finrank_eq.trans hQ
  -- `v` is the image of `z`, a local orientation of `P × Q`; both sides are multiples of it.
  let v := z.map (ContinuousLinearEquiv.uniqueProd ℝ Q P).symm.complZeroPairIso
  have hv : v.val = _ := LocalOrientation.coe_map_uniqueProd_symm_complZeroPairIso (P := P) z
  rw [← hv]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (localHomologyCross (0 : P) (0 : Q) 0 (m + 1) (m + 1) (zero_add _)).hom
      (localHomologyPointClass (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set P) 0 1 ⊗ₜ z.val) =
      c • v.val :=
    ⟨_, ((LinearEquiv.apply_symm_apply _ _).symm.trans
      (v.property.linearEquiv_apply (singularHomologyComplZeroIso hPQ) _))⟩
  -- Crossed on the left with a local orientation `r` of the line, the two sides agree.
  let r := (Basis.singleton (Fin 1) ℝ).orientation.localOrientation (finrank_self ℝ)
  have hd : 1 + (m + 1) = m + 1 + 1 := by omega
  have key := localHomologyCross_tmul_localHomologyCross_localHomologyPointClass_tmul (P := P) hd
    r.val z.val
  rw [← hv, hc] at key
  rw [hc, eq_one_of_localHomologyCross_tmul_zsmul_eq (finrank_self ℝ) hPQ hd r v key, one_smul]

end SymplecticGeometry

namespace Orientation

open SymplecticGeometry

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {m : ℕ}

open Classical in
/-- **The cross product with the point class of a zero-dimensional space, on the left.** Let `P`
have dimension zero, with an orientation `ω`, and `Q` dimension `m + 1`, with an orientation
`ω'`. The cross product of the local orientation of the identity chart of `P` at the origin, the
class of the origin, with the local orientation of `ω'` is the local orientation of the product
orientation `ω'.prod ω` of `Q × P`, carried to `P × Q` by the exchange of factors, if `ω` is the
positive orientation, and its negative otherwise. -/
theorem localHomologyCross_localOrientationOfZeroDimChart_tmul_localOrientation
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q] (hP : finrank ℝ P = 0)
    (hQ : finrank ℝ Q = m + 1) (ω : Orientation ℝ P (Fin 0)) (ω' : Orientation ℝ Q (Fin (m + 1))) :
    (localHomologyCross (0 : P) (0 : Q) 0 (m + 1) (m + 1) (zero_add _)).hom
        ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
          (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ (ω'.localOrientation hQ).val) =
      if ω = positiveOrientation then
        (((ω'.prod ω hQ hP).map (Fin (m + 1)) (LinearEquiv.prodComm ℝ Q P)).localOrientation
          (by rw [Module.finrank_prod, hP, hQ, zero_add])).val
      else
        -(((ω'.prod ω hQ hP).map (Fin (m + 1)) (LinearEquiv.prodComm ℝ Q P)).localOrientation
          (by rw [Module.finrank_prod, hP, hQ, zero_add])).val := by
  have : Subsingleton P := Module.finrank_zero_iff.1 hP
  let := uniqueOfSubsingleton (0 : P)
  have hPQ : finrank ℝ (P × Q) = m + 1 := by rw [Module.finrank_prod, hP, hQ, zero_add]
  let J : Q ≃L[ℝ] P × Q := (ContinuousLinearEquiv.uniqueProd ℝ Q P).symm
  -- The point class times `ω'` is the local orientation of `ω'` carried to `P × Q` by `J`.
  have hJω : (localHomologyCross (0 : P) (0 : Q) 0 (m + 1) (m + 1) (zero_add _)).hom
      ((localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
        (OpenPartialHomeomorph.mem_refl_source _) hP).val ⊗ₜ (ω'.localOrientation hQ).val) =
      ((ω'.map (Fin (m + 1)) J.toLinearEquiv).localOrientation hPQ).val := by
    rw [localOrientationOfZeroDimChart_coe, localHomologyCross_localHomologyPointClass_tmul hP hQ,
      localOrientation_map J ω' hQ hPQ]
    exact (LocalOrientation.coe_map_uniqueProd_symm_complZeroPairIso _).symm
  -- Linear algebra: `J` is the inclusion `Q → Q × P` followed by the exchange of factors.
  have hlin : (ω'.prod positiveOrientation hQ hP).map (Fin (m + 1)) (LinearEquiv.prodComm ℝ Q P) =
      ω'.map (Fin (m + 1)) J.toLinearEquiv := by
    rw [prod_positiveOrientation_right, ← Orientation.map_trans]
    congr 1
  rw [hJω]
  rcases (Module.finBasisOfFinrankEq ℝ P hP).orientation_eq_or_eq_neg ω with h | h <;>
    rw [Basis.orientation_isEmpty] at h <;> subst h
  · rw [ite_eq_left rfl, hlin]
  · rw [ite_eq_right (Module.Ray.ne_neg_self _).symm, prod_neg_right, Orientation.map_neg,
      localOrientation_neg, LocalOrientation.coe_neg, neg_neg, hlin]

open Classical in
/-- **The cross product with the point class of a zero-dimensional space, on the right.** Let `P`
have dimension `m + 1`, with an orientation `ω`, and `Q` dimension zero, with an orientation
`ω'`. The cross product of the local orientation of `ω` with the local orientation of the
identity chart of `Q` at the origin, the class of the origin, is the local orientation of the
product orientation `ω.prod ω'` if `ω'` is the positive orientation, and its negative
otherwise. -/
theorem localHomologyCross_localOrientation_tmul_localOrientationOfZeroDimChart
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q] (hP : finrank ℝ P = m + 1)
    (hQ : finrank ℝ Q = 0) (ω : Orientation ℝ P (Fin (m + 1))) (ω' : Orientation ℝ Q (Fin 0)) :
    (localHomologyCross (0 : P) (0 : Q) (m + 1) 0 (m + 1) (add_zero _)).hom
        ((ω.localOrientation hP).val ⊗ₜ (localOrientationOfZeroDimChart
          (OpenPartialHomeomorph.refl Q) (OpenPartialHomeomorph.mem_refl_source _) hQ).val) =
      if ω' = positiveOrientation then
        ((ω.prod ω' hP hQ).localOrientation (by rw [Module.finrank_prod, hP, hQ, add_zero])).val
      else
        -((ω.prod ω' hP hQ).localOrientation
          (by rw [Module.finrank_prod, hP, hQ, add_zero])).val := by
  have : Subsingleton Q := Module.finrank_zero_iff.1 hQ
  let := uniqueOfSubsingleton (0 : Q)
  have hPQ : finrank ℝ (P × Q) = m + 1 := by rw [Module.finrank_prod, hP, hQ, add_zero]
  let J : P ≃L[ℝ] P × Q := (ContinuousLinearEquiv.prodUnique ℝ P Q).symm
  have hJω : (localHomologyCross (0 : P) (0 : Q) (m + 1) 0 (m + 1) (add_zero _)).hom
      ((ω.localOrientation hP).val ⊗ₜ (localOrientationOfZeroDimChart
        (OpenPartialHomeomorph.refl Q) (OpenPartialHomeomorph.mem_refl_source _) hQ).val) =
      ((ω.map (Fin (m + 1)) J.toLinearEquiv).localOrientation hPQ).val := by
    rw [localOrientationOfZeroDimChart_coe, localHomologyCross_tmul_localHomologyPointClass,
      localOrientation_map J ω hP hPQ]
    exact (LocalOrientation.coe_map_prodUnique_symm_complZeroPairIso _).symm
  -- `J` is `LinearEquiv.prodUnique` inverted, as a continuous linear equivalence.
  have hJ' : J.toLinearEquiv = (LinearEquiv.prodUnique (R := ℝ) (M := P) (M₂ := Q)).symm := rfl
  rw [hJω, hJ']
  rcases (Module.finBasisOfFinrankEq ℝ Q hQ).orientation_eq_or_eq_neg ω' with h | h <;>
    rw [Basis.orientation_isEmpty] at h <;> subst h
  · rw [ite_eq_left rfl, prod_positiveOrientation_right]
  · rw [ite_eq_right (Module.Ray.ne_neg_self _).symm, prod_neg_right, localOrientation_neg,
      LocalOrientation.coe_neg, neg_neg, prod_positiveOrientation_right]

end Orientation
