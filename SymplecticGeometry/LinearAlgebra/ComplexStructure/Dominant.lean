/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Geometry.Symplectic.Orientation
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Maps with dominant complex-linear part

Let `A : V ≃L[ℝ] W` be an isomorphism of normed spaces and `B : V →L[ℝ] W` a perturbation with
`‖B‖ * ‖A⁻¹‖ < 1`. Then `A + B = A ∘ (1 + A⁻¹ B)` is again an isomorphism, and when `V` is
finite-dimensional it induces the same map on orientations as `A`: along the segment
`t ↦ A + t B`, `t ∈ [0, 1]`, every map is invertible, so the determinant of `1 + t A⁻¹ B` never
vanishes and stays positive.

Applied to a real-linear map `A + B` between spaces with almost complex structures `J`, `J'`,
whose complex-linear part `A` is invertible and dominates `B`, this shows that `A + B` is invertible
and carries the complex orientation of `J` to that of `J'`. No hypothesis on `B` beyond its norm is
needed; in the applications `B` is the antilinear part.

## Main definitions and results

* `ContinuousLinearMap.det_one_sub_pos_of_norm_lt_one`: on a finite-dimensional real normed
  space, `‖C‖ < 1` gives `0 < det (1 - C)`.
* `ContinuousLinearEquiv.addOfNormLt`: the isomorphism `A + B`, for `‖B‖ * ‖A⁻¹‖ < 1`.
* `Orientation.map_addOfNormLt`: `A + B` and `A` carry each orientation to the same one.
* `TauCeti.AlmostComplexStructure.orientation_map_add_of_norm_lt`: if `A` is complex-linear, then
  `A + B` carries the complex orientation of `J` to that of `J'`.

The invertibility of `A + B` is Mathlib's `Units.oneSub` applied to `-A⁻¹ B`; the orientation is
compared with Tau Ceti's `TauCeti.AlmostComplexStructure.map_orientation`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Lefschetz pencils on symplectic manifolds*][Donaldson1999].
-/

public section

noncomputable section

open Module

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a finite-dimensional real normed space, a perturbation `1 - C` of the identity with
`‖C‖ < 1` has positive determinant. -/
theorem det_one_sub_pos_of_norm_lt_one {C : E →L[ℝ] E} (hC : ‖C‖ < 1) : 0 < (1 - C).det := by
  set f : ℝ → ℝ := fun t ↦ (1 - t • C).det with hf
  have hcont : Continuous f := continuous_det.comp (by fun_prop)
  -- For `t ∈ [0, 1]`, the map `1 - t • C` is invertible, so its determinant does not vanish.
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0 := fun t ht ↦ by
    have hnorm : ‖t • C‖ < 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      nlinarith [norm_nonneg C, ht.2]
    have hu := isUnit_one_sub_of_norm_lt_one hnorm
    exact (LinearMap.isUnit_det _ (hu.map toLinearMapRingHom)).ne_zero
  by_contra hneg
  obtain ⟨t, ht, h0⟩ : (0 : ℝ) ∈ f '' Set.Icc 0 1 :=
    intermediate_value_Icc' zero_le_one hcont.continuousOn
      ⟨by simpa [hf] using not_lt.1 hneg, by simp [hf, ContinuousLinearMap.det]⟩
  exact hne t ht h0

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The bound `‖-(A⁻¹ ∘ B)‖ < 1` that makes `1 + A⁻¹ ∘ B` a unit. -/
theorem norm_neg_symm_comp_lt_one {A : E ≃L[𝕜] F} {B : E →L[𝕜] F}
    (h : ‖B‖ * ‖(A.symm : F →L[𝕜] E)‖ < 1) : ‖-((A.symm : F →L[𝕜] E).comp B)‖ < 1 := by
  rw [norm_neg]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt (by rwa [mul_comm])

/-- **A small perturbation of an isomorphism is an isomorphism.** If `A : E ≃L[𝕜] F` and
`B : E →L[𝕜] F` satisfy `‖B‖ * ‖A⁻¹‖ < 1`, then `A + B` is an isomorphism; this is it
(`ContinuousLinearEquiv.coe_addOfNormLt`). -/
def addOfNormLt [CompleteSpace E] (A : E ≃L[𝕜] F) (B : E →L[𝕜] F)
    (h : ‖B‖ * ‖(A.symm : F →L[𝕜] E)‖ < 1) :
    E ≃L[𝕜] F :=
  (unitsEquiv 𝕜 E (Units.oneSub _ (norm_neg_symm_comp_lt_one h))).trans A

variable [CompleteSpace E] {A : E ≃L[𝕜] F} {B : E →L[𝕜] F}
  (h : ‖B‖ * ‖(A.symm : F →L[𝕜] E)‖ < 1)

@[simp]
theorem addOfNormLt_apply (x : E) : A.addOfNormLt B h x = A x + B x := by
  simp [addOfNormLt]

@[simp]
theorem coe_addOfNormLt : (A.addOfNormLt B h : E →L[𝕜] F) = A + B := by
  ext x
  simp

end ContinuousLinearEquiv

namespace Orientation

variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype ι]

/-- **A dominated perturbation does not change the induced orientation.** If
`‖B‖ * ‖A⁻¹‖ < 1`, then `A + B` and `A` carry each orientation of `V`, indexed by a type of
cardinality `finrank ℝ V`, to the same orientation of `W`. -/
theorem map_addOfNormLt (x : Orientation ℝ V ι) (hι : Fintype.card ι = finrank ℝ V)
    {A : V ≃L[ℝ] W} {B : V →L[ℝ] W} (h : ‖B‖ * ‖(A.symm : W →L[ℝ] V)‖ < 1) :
    Orientation.map ι (A.addOfNormLt B h).toLinearEquiv x =
      Orientation.map ι A.toLinearEquiv x := by
  set C : V →L[ℝ] V := -(A.symm : W →L[ℝ] V).comp B
  have hC : ‖C‖ < 1 := ContinuousLinearEquiv.norm_neg_symm_comp_lt_one h
  -- `A + B = A ∘ (1 - C)`.
  have he : (A.addOfNormLt B h).toLinearEquiv =
      (ContinuousLinearEquiv.unitsEquiv ℝ V (Units.oneSub C hC)).toLinearEquiv.trans
        A.toLinearEquiv := by
    ext v
    simp [C]
  rw [he, map_trans, (map_eq_iff_det_pos x _ hι).2]
  exact ContinuousLinearMap.det_one_sub_pos_of_norm_lt_one hC

end Orientation

namespace TauCeti.AlmostComplexStructure

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {k : ℕ}

/-- **Maps with dominant complex-linear part preserve the complex orientation.** Let `J`, `J'` be
almost complex structures on `V`, `W`, let `A : V ≃L[ℝ] W` be complex-linear, and let
`B : V →L[ℝ] W` satisfy `‖B‖ * ‖A⁻¹‖ < 1`. Then the isomorphism `A + B`
(`ContinuousLinearEquiv.addOfNormLt`) carries the complex orientation of `J` to that of `J'`. -/
theorem orientation_map_add_of_norm_lt {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} {A : V ≃L[ℝ] W}
    (hA : IsComplexLinear J.toLinearMap J'.toLinearMap (A : V →ₗ[ℝ] W)) {B : V →L[ℝ] W}
    (h : ‖B‖ * ‖(A.symm : W →L[ℝ] V)‖ < 1) (hk : finrank ℝ V = k) (hk' : finrank ℝ W = k) :
    Orientation.map (Fin k) (A.addOfNormLt B h).toLinearEquiv (J.orientation hk) =
      J'.orientation hk' := by
  rw [Orientation.map_addOfNormLt _ ((Fintype.card_fin k).trans hk.symm),
    map_orientation ((isComplexLinearMap_iff_isComplexLinear _ _ _).2 hA) hk]

end TauCeti.AlmostComplexStructure
