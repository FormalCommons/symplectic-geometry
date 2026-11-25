/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.LeftInvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff

/-!
# The left Maurer–Cartan form

For a real Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G`, the left Maurer–Cartan form
`θ` is the `𝔤`-valued one-form that translates a tangent vector at `g` back to the identity:
`θ_g v = d(L_{g⁻¹})_g v`. Tau Ceti has it evaluated on a vector field
(`TauCeti.leftMaurerCartanEval`); this file names it as a smooth form, Tau Ceti's left-invariant
extension `TauCeti.leftInvariantSmoothForm` of the identity of `𝔤`.

## Main definitions

* `SymplecticGeometry.leftMaurerCartanForm I G : SmoothForm I G (GroupLieAlgebra I G) 1`.

## Main results

* `SymplecticGeometry.leftMaurerCartanForm_apply`: its value at `g` on `v` is
  `mfderiv I I (g⁻¹ * ·) g v`.
* `SymplecticGeometry.leftMaurerCartanForm_apply_mulInvariantVectorField`: it takes the value `ξ`
  on the left-invariant vector field of `ξ`.
* `SymplecticGeometry.mpullback_mul_left_leftMaurerCartanForm`: it is left-invariant.
* `SymplecticGeometry.mpullback_mul_right_leftMaurerCartanForm`: right translation by `h` pulls
  it back to its image under `Ad(h⁻¹)`.

## Implementation notes

Smoothness and left-invariance come from Tau Ceti's `TauCeti.leftInvariantSmoothForm` and
`TauCeti.mpullback_mul_left_leftInvariantSmoothForm`. The proof of
`mpullback_mul_right_leftMaurerCartanForm` follows that of Tau Ceti's
`Module.Dual.mpullback_mul_right_leftInvariantForm`.

The norm on `𝔤` that `SmoothForm` needs is the scoped one of
`SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`; statements about this form need
`open scoped GroupLieAlgebra`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §4 (the canonical one-form of a Lie group).
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- The **left Maurer–Cartan form** of a Lie group `G`: the smooth one-form with values in the
Lie algebra `𝔤 = GroupLieAlgebra I G` whose value at `g` on a tangent vector `v` is
`d(L_{g⁻¹})_g v`. It is the left-invariant extension of the identity of `𝔤`, read as a
one-form on `𝔤`. -/
def leftMaurerCartanForm : SmoothForm I G (GroupLieAlgebra I G) 1 :=
  leftInvariantSmoothForm I G (GroupLieAlgebra I G) 1
    (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) 0
      (ContinuousLinearMap.id ℝ (GroupLieAlgebra I G)))

theorem leftMaurerCartanForm_def :
    leftMaurerCartanForm I G = leftInvariantSmoothForm I G (GroupLieAlgebra I G) 1
      (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) 0
        (ContinuousLinearMap.id ℝ (GroupLieAlgebra I G))) :=
  (rfl)

variable {I G}

/-- The left Maurer–Cartan form at `g` translates a tangent vector at `g` to the identity by the
differential of left multiplication by `g⁻¹`. -/
theorem leftMaurerCartanForm_apply (g : G) (v : Fin 1 → TangentSpace I g) :
    (leftMaurerCartanForm I G).val g v = mfderiv I I (g⁻¹ * ·) g (v 0) := by
  rw [leftMaurerCartanForm_def, leftInvariantSmoothForm_val, leftInvariantForm_apply]
  -- `ofSubsingleton_apply_apply` does not rewrite here: the form is on `𝔤` with the scoped norm,
  -- the vectors are in tangent spaces, and the two topologies agree only by unfolding.
  exact ContinuousAlternatingMap.ofSubsingleton_apply_apply _ _ _ _ _ _

/-- The left Maurer–Cartan form takes the constant value `ξ` on the left-invariant vector field of
`ξ`. -/
@[simp]
theorem leftMaurerCartanForm_apply_mulInvariantVectorField (ξ : GroupLieAlgebra I G) (g : G) :
    (leftMaurerCartanForm I G).val g ![mulInvariantVectorField ξ g] = ξ := by
  rw [leftMaurerCartanForm_apply, Matrix.cons_val_zero, mfderiv_inv_mul_mulInvariantVectorField]

/-- The left Maurer–Cartan form is left-invariant: `L_h^* θ = θ`. -/
@[simp]
theorem mpullback_mul_left_leftMaurerCartanForm (h : G) :
    SmoothForm.mpullback (h * ·) contMDiff_mul_left (leftMaurerCartanForm I G) =
      leftMaurerCartanForm I G :=
  mpullback_mul_left_leftInvariantSmoothForm _ h

/-- Right translation by `h` pulls the left Maurer–Cartan form back to its image under the
adjoint action of `h⁻¹`: `R_h^* θ = Ad(h⁻¹) θ`. -/
@[simp]
theorem mpullback_mul_right_leftMaurerCartanForm (h : G) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right (leftMaurerCartanForm I G) =
      SmoothForm.mapCoeff (adjointContinuousLinearMap h⁻¹) (leftMaurerCartanForm I G) := by
  apply Subtype.ext
  funext g
  ext v
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (v 0)
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, SmoothForm.coe_mapCoeff,
    RoughForm.mapCoeff_apply, leftMaurerCartanForm_apply, leftMaurerCartanForm_apply, ← hξ,
    mfderiv_mul_right_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField]

end SymplecticGeometry

end
