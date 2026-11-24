/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup

/-!
# The left Maurer–Cartan form

For a real Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G`, the left Maurer–Cartan form
`θ` is the `𝔤`-valued one-form that translates a tangent vector at `g` back to the identity:
`θ_g v = d(L_{g⁻¹})_g v`. Tau Ceti has it only evaluated on a vector field
(`TauCeti.leftMaurerCartanEval`); this file makes it a smooth form.

## Main definitions

* `SymplecticGeometry.leftMaurerCartanForm I G : SmoothForm I G (GroupLieAlgebra I G) 1`.

## Main results

* `SymplecticGeometry.leftMaurerCartanForm_apply`: its value at `g` on `v` is
  `mfderiv I I (g⁻¹ * ·) g v`.
* `SymplecticGeometry.leftMaurerCartanForm_apply_mulInvariantVectorField`: it takes the value `ξ`
  on the left-invariant vector field of `ξ`.
* `SymplecticGeometry.mpullback_mul_right_leftMaurerCartanForm`: right translation by `h` pulls
  it back to its image under `Ad(h⁻¹)`.

## Implementation notes

Smoothness is not proved in charts: in a basis of `𝔤`, the components of `θ` are Tau Ceti's
left-invariant one-forms `Module.Dual.leftInvariantForm` of the coordinate functionals, which are
smooth, so `θ` is a finite sum of smooth forms. The proof of
`mpullback_mul_right_leftMaurerCartanForm` follows that of Tau Ceti's
`Module.Dual.mpullback_mul_right_leftInvariantForm`.

The norm on `𝔤` that `SmoothForm` needs is the one of
`SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §4 (the canonical one-form of a Lie group).
-/

public section

noncomputable section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-- In a basis `b` of the Lie algebra, the value of the left Maurer–Cartan form is the sum over
`i` of the values of the left-invariant one-form of the `i`-th coordinate functional of `b`, along
`b i`. -/
private theorem mfderiv_inv_mul_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (GroupLieAlgebra I G)) :
    (fun g ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I g) (GroupLieAlgebra I G) 0
      (mfderiv I I (g⁻¹ * ·) g)) =
      ∑ i, RoughForm.mapCoeff (ContinuousLinearMap.toSpanSingleton ℝ (b i))
        (Module.Dual.leftInvariantForm (b.coord i)).val := by
  funext g
  ext v
  simp only [Finset.sum_apply, ContinuousAlternatingMap.sum_apply, RoughForm.mapCoeff_apply,
    Module.Dual.leftInvariantForm_apply, ContinuousLinearMap.toSpanSingleton_apply]
  exact (ContinuousAlternatingMap.ofSubsingleton_apply_apply _ _ _ _ _ _).trans (b.sum_repr _).symm

/-- The **left Maurer–Cartan form** of a Lie group `G`: the smooth one-form with values in the
Lie algebra `𝔤 = GroupLieAlgebra I G` whose value at `g` on a tangent vector `v` is
`d(L_{g⁻¹})_g v`. -/
def leftMaurerCartanForm : SmoothForm I G (GroupLieAlgebra I G) 1 :=
  ⟨fun g ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I g) (GroupLieAlgebra I G) 0
      (mfderiv I I (g⁻¹ * ·) g), by
    rw [mfderiv_inv_mul_eq_sum I G (Module.finBasis ℝ (GroupLieAlgebra I G))]
    exact (IsSmoothForm.sum _ _ fun i _ ↦
      (SmoothForm.isSmoothForm _).mapCoeff _).mem_smoothBundleForms⟩

variable {I G}

/-- The left Maurer–Cartan form at `g` translates a tangent vector at `g` to the identity by the
differential of left multiplication by `g⁻¹`. -/
theorem leftMaurerCartanForm_apply (g : G) (v : Fin 1 → TangentSpace I g) :
    (leftMaurerCartanForm I G).val g v = mfderiv I I (g⁻¹ * ·) g (v 0) :=
  (rfl)

/-- The left Maurer–Cartan form takes the constant value `ξ` on the left-invariant vector field of
`ξ`. -/
@[simp]
theorem leftMaurerCartanForm_apply_mulInvariantVectorField (ξ : GroupLieAlgebra I G) (g : G) :
    (leftMaurerCartanForm I G).val g ![mulInvariantVectorField ξ g] = ξ := by
  rw [leftMaurerCartanForm_apply, Matrix.cons_val_zero, mfderiv_inv_mul_mulInvariantVectorField]

/-- Right translation by `h` pulls the left Maurer–Cartan form back to its image under the
adjoint action of `h⁻¹`: `R_h^* θ = Ad(h⁻¹) θ`. -/
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
