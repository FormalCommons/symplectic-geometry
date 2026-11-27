/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Cross.Basic
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

* The cross product of local orientations is associative
  (`TauCeti.LocalOrientation.map_prodAssoc_cross`, in `Orientation/Cross/Basic.lean`), as the
  ordered product is (`TauCeti.LocalOrientation.map_prodAssoc_prod`). Comparing `(z × z') × z''`
  with `z × (z' × z'')` both ways gives the cocycle relation
  `crossSign m n * crossSign (m + n + 1) p = crossSign n p * crossSign m (n + p + 1)`
  (`TauCeti.LocalOrientation.crossSign_mul_crossSign`), since a local orientation has infinite
  order (`TauCeti.IsLocalOrientation.linearEquiv`).
* With `p = 0` this gives `crossSign m (n + 1) = crossSign m n * (-1) ^ (m + 1)`
  (`TauCeti.LocalOrientation.crossSign_succ_right`).

The sign is that of Tau Ceti's exchange `E × F ≃ F × E` on ordered products
(`TauCeti.LocalOrientation.coe_map_prodComm_prod`), so the cross product `z × z'` is the ordered
product `z' × z` transported along `F × E ≃ E × F`
(`TauCeti.LocalOrientation.cross_eq_map_prodComm_prod`); for the local orientations selected by
orientations `ω` and `ω'`, it is the one selected by `ω'.prod ω`, carried along the exchange
(`TauCeti.LocalOrientation.cross_localOrientation_eq_map_prodComm`).

## Main results

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

namespace LocalOrientation

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m n p d : ℕ}

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
    smul_smul, ← Units.val_mul, ← Units.val_mul] at hL
  simp only [← IsLocalOrientation.linearEquiv_apply
    (singularHomologyComplZeroIso (finrank_prod_eq_succ hE hFG he')) (Subtype.property _)] at hL
  rw [mul_comm (crossSign m n), Units.ext (LinearEquiv.injective _ hL), mul_comm]

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
@[simp]
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

/-- For orientations `ω` of `E` and `ω'` of `F`, of dimensions `m + 1` and `n + 1`, the cross
product of the local orientations they select, `E` first, is the local orientation of `E × F`
selected by the product orientation `ω'.prod ω` of `F × E`, reindexed by
`Fin (n + 1 + (m + 1)) ≃ Fin (d + 1)` and carried to `E × F` by the exchange of factors. -/
theorem cross_localOrientation_eq_map_prodComm (hE : finrank ℝ E = m + 1)
    (hF : finrank ℝ F = n + 1) (hd : m + 1 + (n + 1) = d + 1) (hd' : n + 1 + (m + 1) = d + 1)
    (ω : Orientation ℝ E (Fin (m + 1))) (ω' : Orientation ℝ F (Fin (n + 1))) :
    cross hE hF hd (ω.localOrientation hE) (ω'.localOrientation hF) =
      haveI := FiniteDimensional.of_finrank_eq_succ hE
      haveI := FiniteDimensional.of_finrank_eq_succ hF
      ((Orientation.reindex ℝ (F × E) (finCongr hd') (ω'.prod ω hF hE)).map (Fin (d + 1))
        (ContinuousLinearEquiv.prodComm ℝ F E).toLinearEquiv).localOrientation
          (finrank_prod_eq_succ hE hF hd) := by
  rw [Orientation.localOrientation_map _ _ (finrank_prod_eq_succ hF hE hd'),
    ← prod_localOrientation, cross_eq_map_prodComm_prod hE hF hd hd']

end LocalOrientation

end TauCeti
