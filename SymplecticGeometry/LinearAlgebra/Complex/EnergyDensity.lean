/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import TauCeti.Geometry.Symplectic.AlmostComplex
import SymplecticGeometry.LinearAlgebra.Complex.TopForm
import SymplecticGeometry.LinearAlgebra.Alternating.Basic

/-!
# The energy density of a linear map into a space with a two-form

Let `V` be a real vector space with an alternating form `ω` of degree two and a complex structure
`J`, and let `j` be a complex structure on a second real vector space `W`. For a linear map
`L : W → V` put `b (v, w) = ω (L v, J (L w))`. The energy density of `L` is the alternating form

`ε_L (v, w) = ¼ (b (j v, w) + b (w, j v) - b (v, j w) - b (j w, v))`

on `W` (`AlternatingMap.energyDensity`). It is alternating for every `ω` and `J`, and on a pair
`(e, j e)` it takes the value `½ (ω (L e, J L e) + ω (L j e, J L j e))`. For a form `dvol` on `W`,
the squared norm `|L|²` of `L` for `dvol (·, j ·)` and `ω (·, J ·)`
(`AlternatingMap.energyNormSq`) satisfies `|L|² dvol = 2 ε_L` when `W` is a plane and `dvol ≠ 0`.

This is the linear algebra of the energy of a map from a Riemann surface, read at one point; the
manifold statements in `SymplecticGeometry.Geometry.Symplectic.JHolomorphic.Energy.Density` are
derived from these. Tau Ceti's `TauCeti.SymplecticForm.stdComplexLineEnergyDensity` is the
corresponding density on the standard complex line, for a nondegenerate `ω`; here `ω` may be
degenerate.

## Main results

* `AlternatingMap.energyDensity_apply_complexFrame`: the value on a pair `(e, j e)`.
* `AlternatingMap.energyDensity_apply_complexFrame_nonneg` and
  `AlternatingMap.energyDensity_apply_complexFrame_eq_zero_iff`: if `ω (v, J v) > 0` for
  `v ≠ 0`, the density is nonnegative on pairs `(e, j e)`, and zero on one exactly when
  `L e = 0` and `L (j e) = 0`.
* `AlternatingMap.energyNormSq_eq`: on a plane, `|L|²` may be computed from any nonzero `e`;
  `AlternatingMap.energyNormSq_smul_eq_two_smul_energyDensity`: `|L|² dvol = 2 ε_L`.
* `AlternatingMap.energyDensity_eq_two_smul_add`: for `J`-invariant `ω`, on a plane,
  `ε_L = 2 ε_{∂̄L} + L^* ω`, with `∂̄L = ½ (L + J ∘ L ∘ j)` Tau Ceti's `complexAntilinearPart`.
  Both sides are top forms on a plane, so it suffices to compare them on one pair `(e, j e)`,
  where it is the Wirtinger identity, proved as in Tau Ceti's
  `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_sub_two_mul_symplecticForm` but without
  nondegeneracy.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §4.5,
  equation (4.5.4).
* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  §2.2.
* [C. Wendl, *Lectures on Holomorphic Curves in Symplectic and Contact Geometry*][Wendl2010],
  equation (2.6), Definition 2.18 and Proposition 2.19.
-/

public section

open Module TauCeti

noncomputable section

namespace AlternatingMap

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  (ω : V [⋀^Fin 2]→ₗ[ℝ] ℝ) (J : AlmostComplexStructure V) (j : AlmostComplexStructure W)

/-- The bilinear form `(v, w) ↦ ¼ (b (j v) w + b w (j v) - b v (j w) - b (j w) v)` for
`b v w = ω (L v) (J (L w))`, whose alternating map is the energy density. -/
private def energyBilin (L : W →ₗ[ℝ] V) : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  let b := ω.toMultilinearMap.toBilinMap.compl₁₂ L (J.toLinearMap ∘ₗ L)
  (4⁻¹ : ℝ) • (b ∘ₗ j.toLinearMap + b.flip ∘ₗ j.toLinearMap - b.compl₂ j.toLinearMap -
    b.flip.compl₂ j.toLinearMap)

private lemma energyBilin_apply (L : W →ₗ[ℝ] V) (v w : W) :
    energyBilin ω J j L v w = 4⁻¹ * (ω ![L (j v), J (L w)] + ω ![L w, J (L (j v))] -
      ω ![L v, J (L (j w))] - ω ![L (j w), J (L v)]) := by
  simp [energyBilin, MultilinearMap.toBilinMap_apply]

private lemma isAlt_energyBilin (L : W →ₗ[ℝ] V) : (energyBilin ω J j L).IsAlt := fun v ↦ by
  rw [energyBilin_apply]
  ring

/-- The energy density `ε_L` of a linear map `L : W → V`, for an alternating form `ω` and a
complex structure `J` on `V` and a complex structure `j` on `W`: the alternating form on `W`
given by `ε_L (v, w) = ¼ (b (j v, w) + b (w, j v) - b (v, j w) - b (j w, v))` with
`b (v, w) = ω (L v, J (L w))`. On a pair `(e, j e)` it is `½ (ω (L e, J (L e)) + ω (L (j e),
J (L (j e))))` (`energyDensity_apply_complexFrame`). -/
def energyDensity (L : W →ₗ[ℝ] V) : W [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (isAlt_energyBilin ω J j L).toAlternatingMap

/-- The energy density on a pair of vectors, by its four-term formula. -/
theorem energyDensity_apply (L : W →ₗ[ℝ] V) (v w : W) :
    ω.energyDensity J j L ![v, w] = 4⁻¹ * (ω ![L (j v), J (L w)] + ω ![L w, J (L (j v))] -
      ω ![L v, J (L (j w))] - ω ![L (j w), J (L v)]) := by
  rw [energyDensity, LinearMap.IsAlt.toAlternatingMap_apply, energyBilin_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- On a pair `(e, j e)`, the energy density is `½ (ω (L e, J (L e)) + ω (L (j e), J (L (j e))))`.
-/
theorem energyDensity_apply_complexFrame (L : W →ₗ[ℝ] V) (e : W) :
    ω.energyDensity J j L ![e, j e] =
      2⁻¹ * (ω ![L e, J (L e)] + ω ![L (j e), J (L (j e))]) := by
  rw [energyDensity_apply, j.apply_apply]
  have hω (v w : V) : ω ![v, w] = ω.toMultilinearMap.toBilinMap v w :=
    (MultilinearMap.toBilinMap_apply _ v w).symm
  simp only [hω, map_neg, LinearMap.neg_apply]
  ring

/-- The energy density of the zero map vanishes. -/
@[simp]
theorem energyDensity_zero : ω.energyDensity J j (0 : W →ₗ[ℝ] V) = 0 := by
  ext v w
  rw [energyDensity_apply]
  have h0 (w : V) : ω ![0, w] = 0 := ω.map_coord_zero 0 rfl
  simp only [LinearMap.zero_apply, h0, add_zero, sub_zero, mul_zero, zero_apply]

variable {ω J} in
/-- If `ω (v, J v) > 0` for every `v ≠ 0`, then `ω (v, J v) ≥ 0` for every `v`. -/
theorem apply_complexFrame_nonneg (hω : ∀ v, v ≠ 0 → 0 < ω ![v, J v]) (v : V) :
    0 ≤ ω ![v, J v] := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [ω.map_coord_zero 0 rfl]
  · exact (hω v hv).le

variable {ω J} in
/-- If `ω (v, J v) > 0` for every `v ≠ 0`, the energy density is nonnegative on every pair
`(e, j e)`. -/
theorem energyDensity_apply_complexFrame_nonneg (hω : ∀ v, v ≠ 0 → 0 < ω ![v, J v])
    (L : W →ₗ[ℝ] V) (e : W) : 0 ≤ ω.energyDensity J j L ![e, j e] := by
  rw [energyDensity_apply_complexFrame]
  exact mul_nonneg (by norm_num)
    (add_nonneg (apply_complexFrame_nonneg hω _) (apply_complexFrame_nonneg hω _))

variable {ω J} in
/-- If `ω (v, J v) > 0` for every `v ≠ 0`, the energy density vanishes on a pair `(e, j e)`
exactly when `L` vanishes on `e` and `j e`. -/
theorem energyDensity_apply_complexFrame_eq_zero_iff (hω : ∀ v, v ≠ 0 → 0 < ω ![v, J v])
    (L : W →ₗ[ℝ] V) (e : W) :
    ω.energyDensity J j L ![e, j e] = 0 ↔ L e = 0 ∧ L (j e) = 0 := by
  have h (v : V) : ω ![v, J v] = 0 ↔ v = 0 := by
    refine ⟨fun hv ↦ by_contra fun hv' ↦ (hω v hv').ne' hv, ?_⟩
    rintro rfl
    exact ω.map_coord_zero 0 rfl
  rw [energyDensity_apply_complexFrame, mul_eq_zero, or_iff_right (by norm_num),
    add_eq_zero_iff_of_nonneg (apply_complexFrame_nonneg hω _) (apply_complexFrame_nonneg hω _),
    h, h]

open scoped Classical in
/-- The squared norm `|L|²` of a linear map `L : W → V` for the form `dvol (·, j ·)` on the
source and `ω (·, J ·)` on the target: the value
`(ω (L e, J (L e)) + ω (L (j e), J (L (j e)))) / dvol (e, j e)` for a nonzero `e` chosen once, and
`0` if `W` is zero. On a plane, any nonzero `e` gives the same value (`energyNormSq_eq`). -/
def energyNormSq (dvol : W [⋀^Fin 2]→ₗ[ℝ] ℝ) (L : W →ₗ[ℝ] V) : ℝ :=
  if h : ∃ e : W, e ≠ 0 then
    (ω ![L h.choose, J (L h.choose)] + ω ![L (j h.choose), J (L (j h.choose))]) /
      dvol ![h.choose, j h.choose]
  else 0

open scoped Classical in
/-- The squared norm by its definition. -/
theorem energyNormSq_def (dvol : W [⋀^Fin 2]→ₗ[ℝ] ℝ) (L : W →ₗ[ℝ] V) :
    ω.energyNormSq J j dvol L =
      if h : ∃ e : W, e ≠ 0 then
        (ω ![L h.choose, J (L h.choose)] + ω ![L (j h.choose), J (L (j h.choose))]) /
          dvol ![h.choose, j h.choose]
      else 0 :=
  (rfl)

/-- On a plane, the squared norm of `L` is
`(ω (L e, J (L e)) + ω (L (j e), J (L (j e)))) / dvol (e, j e)` for every nonzero `e`. -/
theorem energyNormSq_eq (h2 : finrank ℝ W = 2) (dvol : W [⋀^Fin 2]→ₗ[ℝ] ℝ) (L : W →ₗ[ℝ] V)
    {e : W} (he : e ≠ 0) :
    ω.energyNormSq J j dvol L =
      (ω ![L e, J (L e)] + ω ![L (j e), J (L (j e))]) / dvol ![e, j e] := by
  have h : ∃ e : W, e ≠ 0 := ⟨e, he⟩
  have key (e : W) : ω ![L e, J (L e)] + ω ![L (j e), J (L (j e))] =
      2 * ω.energyDensity J j L ![e, j e] := by
    rw [energyDensity_apply_complexFrame]
    ring
  simp only [energyNormSq_def, h, ↓reduceDIte]
  rw [key, key, mul_div_assoc, mul_div_assoc,
    j.alternatingMap_apply_div_apply_eq h2 he h.choose_spec]

/-- On a plane, for a nonzero form `dvol`, `|L|² dvol = 2 ε_L`. -/
theorem energyNormSq_smul_eq_two_smul_energyDensity (h2 : finrank ℝ W = 2)
    {dvol : W [⋀^Fin 2]→ₗ[ℝ] ℝ} (hdvol : dvol ≠ 0) (L : W →ₗ[ℝ] V) :
    ω.energyNormSq J j dvol L • dvol = (2 : ℝ) • ω.energyDensity J j L := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℝ) (h2 ▸ two_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : W)
  have hd : dvol ![e, j e] ≠ 0 := fun hd ↦
    hdvol (j.alternatingMap_ext h2 he (by rw [hd, zero_apply]))
  refine j.alternatingMap_ext h2 he ?_
  rw [smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, energyNormSq_eq ω J j h2 dvol L he,
    energyDensity_apply_complexFrame]
  field_simp

variable {ω J j} in
/-- If `ω (v, J v) > 0` and `dvol (w, j w) > 0` for all nonzero `v` and `w`, the squared norm is
nonnegative. -/
theorem energyNormSq_nonneg (hω : ∀ v, v ≠ 0 → 0 < ω ![v, J v]) {dvol : W [⋀^Fin 2]→ₗ[ℝ] ℝ}
    (hdvol : ∀ w, w ≠ 0 → 0 < dvol ![w, j w]) (L : W →ₗ[ℝ] V) :
    0 ≤ ω.energyNormSq J j dvol L := by
  rw [energyNormSq_def]
  split_ifs with h
  · refine div_nonneg ?_ (hdvol _ h.choose_spec).le
    have := energyDensity_apply_complexFrame_nonneg j hω L h.choose
    rw [energyDensity_apply_complexFrame] at this
    linarith
  · exact le_rfl

variable {ω J} in
/-- **The pointwise energy identity.** If `ω` is `J`-invariant, then on a plane `W` the energy
density of `L` is twice that of its complex-antilinear part `∂̄L = ½ (L + J ∘ L ∘ j)` plus the
pullback of `ω` by `L`: `ε_L = 2 ε_{∂̄L} + L^* ω`. -/
theorem energyDensity_eq_two_smul_add (hinv : ∀ v w, ω ![J v, J w] = ω ![v, w])
    (h2 : finrank ℝ W = 2) (L : W →ₗ[ℝ] V) :
    ω.energyDensity J j L =
      (2 : ℝ) • ω.energyDensity J j (complexAntilinearPart j.toLinearMap J.toLinearMap L) +
        ω.compLinearMap L := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℝ) (h2 ▸ two_pos)
  obtain ⟨e, he⟩ := exists_ne (0 : W)
  refine j.alternatingMap_ext h2 he ?_
  have hAe := complexAntilinearPart_apply j.toLinearMap J.toLinearMap L e
  have hAje : complexAntilinearPart j.toLinearMap J.toLinearMap L (j e) =
      -J (complexAntilinearPart j.toLinearMap J.toLinearMap L e) :=
    (isComplexAntilinear_complexAntilinearPart j.square_neg J.square_neg L).apply e
  rw [add_apply, smul_apply, smul_eq_mul, compLinearMap_apply, energyDensity_apply_complexFrame,
    energyDensity_apply_complexFrame, hAje, hAe]
  have hinv' (v w : V) := hinv v w
  have hB := ω.isAlt_toBilinMap
  have hL : (fun i ↦ L (![e, j e] i)) = ![L e, L (j e)] := (FinVec.etaExpand_eq _).symm
  rw [hL]
  have hω (v w : V) : ω ![v, w] = ω.toMultilinearMap.toBilinMap v w :=
    (MultilinearMap.toBilinMap_apply _ v w).symm
  simp only [hω, map_neg, map_smul, map_add, J.apply_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at hinv' ⊢
  rw [hinv', hinv', ← hB.neg (L e) (L (j e)), ← hB.neg (L e) (J (L e)),
    ← hB.neg (L (j e)) (J (L (j e)))]
  ring

end AlternatingMap

end
