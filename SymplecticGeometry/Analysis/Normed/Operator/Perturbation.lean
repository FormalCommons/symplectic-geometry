/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Orientation
import TauCeti.LinearAlgebra.Matrix.Charpoly.DetSign
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Small perturbations of isomorphisms

Let `A : E ≃L[𝕜] F` be an isomorphism of normed spaces, with `E` complete, and `B : E →L[𝕜] F`
with `‖B‖ * ‖A⁻¹‖ < 1`. Then `A + B = A ∘ (1 + A⁻¹ B)` is again an isomorphism. Over `ℝ`, with a
finite-dimensional source, it induces the same map on orientations as `A`, since
`1 + A⁻¹ B = 1 - C` with `‖C‖ < 1` has positive determinant.

That positivity is a corollary of Tau Ceti's `LinearMap.det_one_sub_pos_of_not_hasEigenvalue`:
a real eigenvalue `μ` of `C` satisfies `|μ| ≤ ‖C‖ < 1`.

## Main definitions and results

* `ContinuousLinearMap.det_one_sub_pos_of_norm_lt_one`: on a finite-dimensional real normed
  space, `‖C‖ < 1` gives `0 < det (1 - C)`.
* `ContinuousLinearEquiv.addOfNormLt`: the isomorphism `A + B`, for `‖B‖ * ‖A⁻¹‖ < 1`.
* `Orientation.map_addOfNormLt`: `A + B` and `A` carry each orientation to the same one.

The invertibility of `A + B` is Mathlib's `Units.oneSub` applied to `-A⁻¹ B`; the two orientations
are compared with Tau Ceti's `Orientation.map_eq_map_iff_det_pos`. Tau Ceti's
`ContinuousLinearMap.IsInvertible.of_mul_norm_sub_lt` gives the invertibility of `A + B` as a
proposition; `addOfNormLt` is the equivalence itself, which the orientation statement needs.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
-/

public section

noncomputable section

open Module

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a finite-dimensional real normed space, a perturbation `1 - C` of the identity with
`‖C‖ < 1` has positive determinant. -/
theorem det_one_sub_pos_of_norm_lt_one {C : E →L[ℝ] E} (hC : ‖C‖ < 1) : 0 < (1 - C).det := by
  refine LinearMap.det_one_sub_pos_of_not_hasEigenvalue fun μ hμ h ↦ ?_
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hCv : C v = μ • v := hv.apply_eq_smul
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv.2
  have : μ * ‖v‖ ≤ ‖C‖ * ‖v‖ := by
    simpa [hCv, norm_smul, abs_of_pos (by linarith : (0 : ℝ) < μ)] using C.le_opNorm v
  nlinarith

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `‖B‖ * ‖A⁻¹‖ < 1`, then `-(A⁻¹ ∘ B)` has norm less than `1`. -/
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

/-- `A.addOfNormLt B h` is `A ∘ (1 - C)` for `C = -(A⁻¹ ∘ B)`, where `1 - C` is the unit given by
Mathlib's `Units.oneSub`. -/
theorem addOfNormLt_def :
    A.addOfNormLt B h =
      (unitsEquiv 𝕜 E (Units.oneSub _ (norm_neg_symm_comp_lt_one h))).trans A :=
  (rfl)

@[simp]
theorem addOfNormLt_apply (x : E) : A.addOfNormLt B h x = A x + B x := by
  simp [addOfNormLt_def]

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
  rw [map_eq_map_iff_det_pos x _ _ hι]
  convert ContinuousLinearMap.det_one_sub_pos_of_norm_lt_one
    (ContinuousLinearEquiv.norm_neg_symm_comp_lt_one h) using 2
  ext v
  simp

end Orientation
