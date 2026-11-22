/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
import SymplecticGeometry.AlgebraicTopology.Singular.Kunneth.Assoc
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Line

/-!
# The sign of the cross product of local orientations

For real normed spaces `E` and `F` of dimensions `m + 1` and `n + 1`, the cross product of local
orientations at the origin (`TauCeti.LocalOrientation.cross`) and Tau Ceti's ordered product
`TauCeti.LocalOrientation.prod` differ by the sign `TauCeti.LocalOrientation.crossSign m n`
(`Orientation/Cross/Basic.lean`). This file computes it:
`crossSign m n = (-1) ^ ((m + 1) * (n + 1))` (`TauCeti.LocalOrientation.crossSign_eq`).

The computation is an induction on `n`, starting from `crossSign m 0 = (-1) ^ (m + 1)`
(`TauCeti.LocalOrientation.crossSign_zero_right`, in `Orientation/Cross/Line.lean`).

* The cross product of local homology classes is associative: the associator
  `(X × Y) × Z ≃ₜ X × (Y × Z)` sends `(a × b) × c` to `a × (b × c)`
  (`TauCeti.localHomologyCross_assoc`). This is the associativity of the cross product of pairs
  with coefficients multiplied in `ULift ℤ`
  (`TopCat.singularHomologyCrossRelPair_uliftTensorSelfIso_assoc`), read through the maps of
  pairs that identify `(X ∖ {x}) × Y ∪ X × (Y ∖ {y})` with the complement of `(x, y)`.
* Hence the cross product of local orientations is associative
  (`TauCeti.LocalOrientation.map_prodAssoc_cross`), as the ordered product is
  (`TauCeti.LocalOrientation.map_prodAssoc_prod`). Comparing `(z × z') × z''` with
  `z × (z' × z'')` both ways gives the cocycle relation
  `crossSign m n * crossSign (m + n + 1) p = crossSign n p * crossSign m (n + p + 1)`
  (`TauCeti.LocalOrientation.crossSign_mul_crossSign`), since a local orientation has infinite
  order (`TauCeti.LocalOrientation.units_smul_coe_inj`).
* With `p = 0` this gives `crossSign m (n + 1) = crossSign m n * (-1) ^ (m + 1)`
  (`TauCeti.LocalOrientation.crossSign_succ_right`).

The sign is that of Tau Ceti's exchange `E × F ≃ F × E` on ordered products
(`TauCeti.LocalOrientation.coe_map_prodComm_prod`), so the cross product `z × z'` is the ordered
product `z' × z` transported along `F × E ≃ E × F`
(`TauCeti.LocalOrientation.cross_eq_map_prodComm_prod`).

## Main results

* `TauCeti.localHomologyCross_assoc`: associativity of the cross product of local homology classes.
* `TauCeti.LocalOrientation.map_prodAssoc_cross`: associativity of the cross product of local
  orientations.
* `TauCeti.LocalOrientation.crossSign_eq`: `crossSign m n = (-1) ^ ((m + 1) * (n + 1))`.
* `TauCeti.LocalOrientation.coe_cross_eq_neg_one_pow_smul`,
  `TauCeti.LocalOrientation.coe_cross_localOrientation_eq_neg_one_pow_smul`: the cross product of
  local orientations, and of those selected by orientations `ω` and `ω'`, is
  `(-1) ^ ((m + 1) * (n + 1))` times the ordered product, and the local orientation selected by
  `ω.prod ω'`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 3.2 and 3.3 (cross products and local orientations) and Section 3.B (the relative cross
  product).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Sections 9 and 10.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Set Module

namespace TauCeti

section Assoc

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The local homology cross product is the cross product of pairs, then the multiplication of
coefficients, then the map of pairs given by the identity of `X × Y`. -/
private theorem localHomologyCross_eq (x : X) (y : Y) (p q n : ℕ) (h : p + q = n) :
    localHomologyCross x y p q n h =
      TopCat.singularHomologyCrossRelPair (TopCat.of X) (TopCat.of Y) {x}ᶜ {y}ᶜ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (ModuleCat.of ℤ (ULift.{0} ℤ)) p q n h ≫
      HomologicalComplex.homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        (ModuleCat.uliftTensorSelfIso ℤ).hom).app _) n ≫
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap _ (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y)) _ n := by
  rw [localHomologyCross_def, TopPair.singularHomologyMap_coefficient_naturality]

/-- **Associativity of the cross product of local homology classes.** The map of local homology
induced by the associator `(X × Y) × Z ≃ₜ X × (Y × Z)` sends `(a × b) × c` to `a × (b × c)`. -/
theorem localHomologyCross_assoc (x : X) (y : Y) (z : Z) (p q r pq qr n : ℕ) (hpq : p + q = pq)
    (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n) :
    (localHomologyCross x y p q pq hpq ▷
        localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({z} : Set Z) r) ≫
      localHomologyCross (x, y) z pq r n hn ≫
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
          ((Homeomorph.prodAssoc X Y Z : (X × Y) × Z ≃ₜ X × Y × Z) : C((X × Y) × Z, X × Y × Z))
          (by rintro ⟨⟨a, b⟩, c⟩ h; simpa [Homeomorph.prodAssoc, and_assoc] using h) n =
      (α_ _ _ _).hom ≫
        (localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set X) p ◁
          localHomologyCross y z q r qr hqr) ≫
        localHomologyCross x (y, z) p qr n hn' := by
  -- The two ambient maps from `(X ⊗ Y) ⊗ Z` to `X × (Y × Z)` agree.
  have hK₁ : ((TopCat.tensorObjIsoProd X Y).hom ⊗ₘ 𝟙 (TopCat.of Z)) ≫
      (TopCat.tensorObjIsoProd (X × Y) Z).hom ≫
        TopCat.ofHom ((Homeomorph.prodAssoc X Y Z : (X × Y) × Z ≃ₜ X × Y × Z) :
          C((X × Y) × Z, X × Y × Z)) =
      (α_ (TopCat.of X) (TopCat.of Y) (TopCat.of Z)).hom ≫
        (𝟙 (TopCat.of X) ⊗ₘ (TopCat.tensorObjIsoProd Y Z).hom) ≫
          (TopCat.tensorObjIsoProd X (Y × Z)).hom := by
    simp only [TopCat.tensorObjIsoProd_hom_eq_id]
    -- Both sides are now `((a, b), c) ↦ (a, (b, c))`: the associator of `TopCat` is that of the
    -- product, and no lemma states it as `Homeomorph.prodAssoc`.
    rfl
  -- The cross products of pairs are natural in the maps that identify the subspaces with the
  -- complements of points, the identity on the other factor.
  have hZ : MapsTo (𝟙 (TopCat.of Z)) ({z}ᶜ : Set (TopCat.of Z)) {z}ᶜ := fun _ h ↦ h
  have hX : MapsTo (𝟙 (TopCat.of X)) ({x}ᶜ : Set (TopCat.of X)) {x}ᶜ := fun _ h ↦ h
  have hid : TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of Z))
      hZ) (ModuleCat.of ℤ (ULift.{0} ℤ)) r = 𝟙 _ :=
    (congrArg (TopPair.singularHomologyMap · _ r) (TopPair.ofSubsetMap_id _)).trans
      (TopPair.singularHomologyMap_id _ _ _)
  have hid' : TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of X))
      hX) (ModuleCat.of ℤ (ULift.{0} ℤ)) p = 𝟙 _ :=
    (congrArg (TopPair.singularHomologyMap · _ p) (TopPair.ofSubsetMap_id _)).trans
      (TopPair.singularHomologyMap_id _ _ _)
  have hnatL := TopCat.singularHomologyCrossRelPair_naturality (TopCat.of X ⊗ TopCat.of Y)
    (TopCat.of Z) _ ({z}ᶜ : Set (TopCat.of Z)) (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) pq r n hn (TopCat.tensorObjIsoProd X Y).hom
    (mapsTo_preimage_fst_compl_union_preimage_snd_compl x y) (𝟙 _) hZ
  have hnatR := TopCat.singularHomologyCrossRelPair_naturality (TopCat.of X)
    (TopCat.of Y ⊗ TopCat.of Z) ({x}ᶜ : Set (TopCat.of X)) _ (ModuleCat.of ℤ (ULift.{0} ℤ))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) p qr n hn' (𝟙 _) hX
    (TopCat.tensorObjIsoProd Y Z).hom (mapsTo_preimage_fst_compl_union_preimage_snd_compl y z)
  rw [hid, tensorHom_id] at hnatL
  rw [hid', id_tensorHom] at hnatR
  have hA := TopCat.singularHomologyCrossRelPair_uliftTensorSelfIso_assoc (TopCat.of X)
    (TopCat.of Y) (TopCat.of Z) {x}ᶜ {y}ᶜ {z}ᶜ p q r pq qr n hpq hqr hn hn'
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc] at hA
  -- Write each local cross product as a cross product of pairs, then the coefficient map, then the
  -- map of pairs, and move the maps of pairs to the end of both sides.
  rw [localHomologyCross_eq, localHomologyCross_eq, localHomologyCross_eq, localHomologyCross_eq]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hnatL, reassoc_of% hnatR]
  rw [← reassoc_of% (TopPair.singularHomologyMap_coefficient_naturality _
      (ModuleCat.uliftTensorSelfIso ℤ).hom n),
    ← reassoc_of% (TopPair.singularHomologyMap_coefficient_naturality _
      (ModuleCat.uliftTensorSelfIso ℤ).hom n)]
  simp only [localHomologyMap_def]
  -- Both sides now start with the two sides of `hA`; the maps of pairs that follow agree.
  rw [← reassoc_of% hA, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    ← TopPair.singularHomologyMap_comp]
  refine congrArg (fun φ ↦ _ ≫ _ ≫ _ ≫ _ ≫ TopPair.singularHomologyMap φ _ n) ?_
  refine TopPair.hom_ext_of_fst _ ?_
  simp only [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst]
  exact hK₁

end Assoc

namespace LocalOrientation

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m n p d : ℕ}

/-- **Associativity of the cross product of local orientations.** Transport along
`(E × F) × G ≃ E × (F × G)` carries `(z × z') × z''` to `z × (z' × z'')`. -/
theorem map_prodAssoc_cross {e f : ℕ} (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hG : finrank ℝ G = p + 1) (he : m + 1 + (n + 1) = e + 1) (hf : n + 1 + (p + 1) = f + 1)
    (hd : e + 1 + (p + 1) = d + 1) (he' : m + 1 + (f + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1))
    (z'' : LocalOrientation G 0 (p + 1)) :
    (cross (finrank_prod_eq_succ hE hF he) hG hd (cross hE hF he z z') z'').map
        (ContinuousLinearEquiv.prodAssoc ℝ E F G).complZeroPairIso =
      cross hE (finrank_prod_eq_succ hF hG hf) he' z (cross hF hG hf z' z'') := by
  refine Subtype.ext ?_
  rw [coe_map, coe_cross, coe_cross, coe_cross, coe_cross,
    ContinuousLinearEquiv.singularHomologyMap_complZeroPairIso_hom]
  -- Apply associativity to `(z ⊗ z') ⊗ z''`, with `z ⊗ z'` typed as an element of the tensor
  -- product in `ModuleCat`, whose module structure the outer tensor product uses.
  have h (w : ↑(localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set E)
      (m + 1) ⊗ localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({0} : Set F)
        (n + 1))) := ConcreteCategory.congr_hom (localHomologyCross_assoc (0 : E) (0 : F) (0 : G)
    (m + 1) (n + 1) (p + 1) (e + 1) (f + 1) (d + 1) he hf hd he') (w ⊗ₜ z''.val)
  specialize h (z.val ⊗ₜ z'.val)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply] at h
  rw [localHomologyMap_congr _ (j₁ := ((Homeomorph.prodAssoc E F G : (E × F) × G ≃ₜ E × F × G) :
    C((E × F) × G, E × F × G))) (j₂ := ((ContinuousLinearEquiv.prodAssoc ℝ E F G :
    (E × F) × G →L[ℝ] E × F × G) : C((E × F) × G, E × F × G))) (ContinuousMap.ext fun _ ↦ rfl),
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at h
  simp only [Prod.mk_zero_zero] at h
  exact h

/-- A local orientation of a real vector space of positive dimension has infinite order, so its
multiples by the units `±1` of `ℤ` are distinct. -/
theorem units_smul_coe_inj (hE : finrank ℝ E = m + 1) (w : LocalOrientation E 0 (m + 1))
    {u u' : ℤˣ} : (u : ℤ) • w.val = (u' : ℤ) • w.val ↔ u = u' := by
  refine ⟨fun h ↦ Units.ext ?_, fun h ↦ h ▸ rfl⟩
  have h' := (w.property.zsmul_eq_zero_iff (singularHomologyComplSingletonIsoOfFinrankEq _
    (OpenPartialHomeomorph.refl _) (Set.mem_univ 0) hE) (c := (u : ℤ) - u')).1
    (by rw [sub_zsmul, h, add_neg_cancel])
  exact sub_eq_zero.1 h'

/-- If the class of `w` is `u` times the class of `w'`, for a unit `u` of `ℤ`, then the same holds
for their ordered products with `z'` on the right. -/
private theorem coe_prod_left_of_coe_eq_units_smul (hE : finrank ℝ E = m + 1)
    (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1)
    {w w' : LocalOrientation E 0 (m + 1)} {u : ℤˣ} (h : w.val = (u : ℤ) • w'.val)
    (z' : LocalOrientation F 0 (n + 1)) :
    (prod hE hF hd w z').val = (u : ℤ) • (prod hE hF hd w' z').val := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [Units.val_one, one_smul] at h ⊢
    rw [Subtype.ext h]
  · rw [Units.val_neg, Units.val_one, neg_one_zsmul, ← coe_neg] at h
    rw [Subtype.ext h, prod_neg_left, coe_neg, Units.val_neg, Units.val_one, neg_one_zsmul]

/-- If the class of `w` is `u` times the class of `w'`, for a unit `u` of `ℤ`, then the same holds
for their ordered products with `z` on the left. -/
private theorem coe_prod_right_of_coe_eq_units_smul (hE : finrank ℝ E = m + 1)
    (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    {w w' : LocalOrientation F 0 (n + 1)} {u : ℤˣ} (h : w.val = (u : ℤ) • w'.val) :
    (prod hE hF hd z w).val = (u : ℤ) • (prod hE hF hd z w').val := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [Units.val_one, one_smul] at h ⊢
    rw [Subtype.ext h]
  · rw [Units.val_neg, Units.val_one, neg_one_zsmul, ← coe_neg] at h
    rw [Subtype.ext h, prod_neg_right, coe_neg, Units.val_neg, Units.val_one, neg_one_zsmul]

/-- **The cocycle relation of the cross product sign**, from the associativity of the cross
product (`TauCeti.LocalOrientation.map_prodAssoc_cross`) and of the ordered product
(`TauCeti.LocalOrientation.map_prodAssoc_prod`). -/
theorem crossSign_mul_crossSign (m n p : ℕ) :
    crossSign m n * crossSign (m + n + 1) p = crossSign n p * crossSign m (n + p + 1) := by
  have hE : finrank ℝ (Fin (m + 1) → ℝ) = m + 1 := Module.finrank_fin_fun ℝ
  have hF : finrank ℝ (Fin (n + 1) → ℝ) = n + 1 := Module.finrank_fin_fun ℝ
  have hG : finrank ℝ (Fin (p + 1) → ℝ) = p + 1 := Module.finrank_fin_fun ℝ
  have he : m + 1 + (n + 1) = m + n + 1 + 1 := by omega
  have hf : n + 1 + (p + 1) = n + p + 1 + 1 := by omega
  have hd : m + n + 1 + 1 + (p + 1) = m + n + p + 2 + 1 := by omega
  have he' : m + 1 + (n + p + 1 + 1) = m + n + p + 2 + 1 := by omega
  have hEF := finrank_prod_eq_succ hE hF he
  have hFG := finrank_prod_eq_succ hF hG hf
  let s := (Pi.basisFun ℝ (Fin (m + 1))).orientation.localOrientation hE
  let s' := (Pi.basisFun ℝ (Fin (n + 1))).orientation.localOrientation hF
  let s'' := (Pi.basisFun ℝ (Fin (p + 1))).orientation.localOrientation hG
  have hL := congrArg Subtype.val (map_prodAssoc_cross hE hF hG he hf hd he' s s' s'')
  rw [coe_map, coe_cross_eq_crossSign_smul hEF hG hd,
    coe_prod_left_of_coe_eq_units_smul hEF hG hd (coe_cross_eq_crossSign_smul hE hF he s s'),
    smul_smul, map_zsmul, ← coe_map, map_prodAssoc_prod hE hF hG he hf hd he',
    coe_cross_eq_crossSign_smul hE hFG he',
    coe_prod_right_of_coe_eq_units_smul hE hFG he' s (coe_cross_eq_crossSign_smul hF hG hf s' s''),
    smul_smul, ← Units.val_mul, ← Units.val_mul,
    units_smul_coe_inj (finrank_prod_eq_succ hE hFG he')] at hL
  rw [mul_comm (crossSign m n), hL, mul_comm]

/-- The sign of the cross product grows by `(-1) ^ (m + 1)` when the dimension of the second
factor grows by one. -/
theorem crossSign_succ_right (m n : ℕ) :
    crossSign m (n + 1) = crossSign m n * (-1) ^ (m + 1) := by
  have h := crossSign_mul_crossSign m n 0
  rw [crossSign_zero_right, crossSign_zero_right, add_zero,
    show m + n + 1 + 1 = m + 1 + (n + 1) by omega, pow_add] at h
  calc crossSign m (n + 1)
      = (-1) ^ (n + 1) * ((-1) ^ (n + 1) * crossSign m (n + 1)) := by
        rw [← mul_assoc, Int.units_mul_self, one_mul]
    _ = crossSign m n * (-1) ^ (m + 1) := by
        rw [← h, mul_left_comm, mul_left_comm _ ((-1 : ℤˣ) ^ (m + 1)), Int.units_mul_self, mul_one]

/-- **The sign of the cross product of local orientations**: the cross product of local
orientations of real vector spaces of dimensions `m + 1` and `n + 1` is `(-1) ^ ((m + 1) * (n + 1))`
times their ordered product `TauCeti.LocalOrientation.prod`. -/
theorem crossSign_eq (m n : ℕ) : crossSign m n = (-1) ^ ((m + 1) * (n + 1)) := by
  induction n with
  | zero => rw [crossSign_zero_right, zero_add, mul_one]
  | succ n ih =>
    rw [crossSign_succ_right, ih, ← pow_add, Nat.mul_succ (m + 1) (n + 1)]

/-- **The cross product of local orientations, with its sign.** For local orientations `z` of `E`
and `z'` of `F` at the origin, of dimensions `m + 1` and `n + 1`, the cross product `z × z'` is
`(-1) ^ ((m + 1) * (n + 1))` times the ordered product `TauCeti.LocalOrientation.prod`, as local
homology classes. -/
theorem coe_cross_eq_neg_one_pow_smul (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (z : LocalOrientation E 0 (m + 1))
    (z' : LocalOrientation F 0 (n + 1)) :
    (cross hE hF hd z z').val = (-1 : ℤ) ^ ((m + 1) * (n + 1)) • (prod hE hF hd z z').val := by
  rw [coe_cross_eq_crossSign_smul, crossSign_eq, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]

/-- **The cross product of the local orientations selected by two orientations.** For
orientations `ω` of `E` and `ω'` of `F`, of dimensions `m + 1` and `n + 1`, the cross product of
the local orientations they select is `(-1) ^ ((m + 1) * (n + 1))` times the local orientation
selected by the product orientation `ω.prod ω'`, reindexed by `Fin (m + 1 + (n + 1)) ≃ Fin (d + 1)`.
-/
theorem coe_cross_localOrientation_eq_neg_one_pow_smul (hE : finrank ℝ E = m + 1)
    (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1) (ω : Orientation ℝ E (Fin (m + 1)))
    (ω' : Orientation ℝ F (Fin (n + 1))) :
    (cross hE hF hd (ω.localOrientation hE) (ω'.localOrientation hF)).val =
      haveI := FiniteDimensional.of_finrank_eq_succ hE
      haveI := FiniteDimensional.of_finrank_eq_succ hF
      (-1 : ℤ) ^ ((m + 1) * (n + 1)) • ((Orientation.reindex ℝ (E × F) (finCongr hd)
        (ω.prod ω' hE hF)).localOrientation (finrank_prod_eq_succ hE hF hd)).val := by
  rw [coe_cross_eq_neg_one_pow_smul, prod_localOrientation]

/-- The cross product `z × z'` is the ordered product `z' × z`, the factor `F` first, transported
along the exchange `F × E ≃ E × F`. -/
theorem cross_eq_map_prodComm_prod (hE : finrank ℝ E = m + 1) (hF : finrank ℝ F = n + 1)
    (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1)
    (z : LocalOrientation E 0 (m + 1)) (z' : LocalOrientation F 0 (n + 1)) :
    cross hE hF hd z z' =
      (prod hF hE hd' z' z).map (ContinuousLinearEquiv.prodComm ℝ F E).complZeroPairIso :=
  Subtype.ext (by rw [coe_map_prodComm_prod hF hE hd' hd, coe_cross_eq_neg_one_pow_smul, mul_comm])

end LocalOrientation

end TauCeti
