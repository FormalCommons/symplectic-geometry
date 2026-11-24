/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic

/-!
# The one-form of a family of weights on the standard model

For integer weights `k : ι → ℤ`, this file defines the smooth one-form
`θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` on `StdSpace ι`, `SymplecticGeometry.weightOneForm k`, in the
coordinates `z.x j`, `z.y j` of the standard model. Near a fixed point of a circle action with
weights `k`, read through the weight chart `SymplecticGeometry.exists_weightChart`, it is the
model of the one-form that localizes the Duistermaat–Heckman integral.

Its properties are read through `EuclideanSpace.sumEquivProd`, which identifies `StdSpace ι`
with Tau Ceti's model `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` of `ℂ^ι`:

* `weightOneForm_apply`: its value at `z` on `v` is `∑ⱼ kⱼ (xⱼ(z) yⱼ(v) - yⱼ(z) xⱼ(v))`;
* `mpullback_weightRotation_weightOneForm`: it is invariant under every rotation
  `TauCeti.weightRotation θ`, which in complex coordinates is `uⱼ ↦ exp (i θⱼ) uⱼ`
  (`TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean`); with `θ = 2π t k` these are
  the rotations of the circle action with weights `k`;
* `weightOneForm_apply_weightGenerator`: on the generator `TauCeti.weightGenerator θ` of those
  rotations, the vector field `∑ⱼ θⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})`, it takes the value
  `∑ⱼ kⱼ θⱼ (xⱼ² + yⱼ²)`; for `θ = 2π k` this is `2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)`, which is nonnegative
  (`weightOneForm_apply_weightGenerator_nonneg`) and, when no weight is zero, vanishes only at
  `0` (`weightOneForm_apply_weightGenerator_eq_zero_iff`);
* `mextDerivₗ_weightOneForm_apply`: its exterior derivative is `2 ∑ⱼ kⱼ dxⱼ ∧ dyⱼ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6
* N. Berline, E. Getzler and M. Vergne, *Heat Kernels and Dirac Operators*, Grundlehren der
  mathematischen Wissenschaften 298, Springer, 1992, §7.2
-/

public section

noncomputable section

open Real
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {ι : Type*} [Fintype ι]

/-- The form `∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` as a continuous linear map from points to one-forms:
each `xⱼ dyⱼ` is the product of the linear function `xⱼ` with the constant form `dyⱼ`. -/
private def weightOneFormCLM (k : ι → ℤ) : StdSpace ι →L[ℝ] StdSpace ι [⋀^Fin 1]→L[ℝ] ℝ :=
  ∑ j, (k j : ℝ) •
    ((EuclideanSpace.proj (Sum.inl j)).smulRight
        (ContinuousAlternatingMap.ofSubsingleton ℝ (StdSpace ι) ℝ 0
          (EuclideanSpace.proj (Sum.inr j))) -
      (EuclideanSpace.proj (Sum.inr j)).smulRight
        (ContinuousAlternatingMap.ofSubsingleton ℝ (StdSpace ι) ℝ 0
          (EuclideanSpace.proj (Sum.inl j))))

private theorem weightOneFormCLM_apply (k : ι → ℤ) (z : StdSpace ι) (v : Fin 1 → StdSpace ι) :
    weightOneFormCLM k z v = ∑ j, (k j : ℝ) * (z.x j * (v 0).y j - z.y j * (v 0).x j) := by
  simp [weightOneFormCLM, mul_sub]

/-- The one-form `θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` of a family of integer weights `k` on the
standard model `StdSpace ι`. -/
def weightOneForm (k : ι → ℤ) : SmoothForm 𝓘(ℝ, StdSpace ι) (StdSpace ι) ℝ 1 :=
  ⟨weightOneFormCLM k,
    (isSmoothForm_modelSpace_iff.2 (weightOneFormCLM k).contDiff).mem_smoothBundleForms⟩

/-- The value of `θₖ` at `z` on a tangent vector `v 0` is
`∑ⱼ kⱼ (xⱼ(z) yⱼ(v 0) - yⱼ(z) xⱼ(v 0))`. -/
theorem weightOneForm_apply (k : ι → ℤ) (z : StdSpace ι)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (weightOneForm k).val z v =
      ∑ j, (k j : ℝ) * (z.x j * (v 0 : StdSpace ι).y j - z.y j * (v 0 : StdSpace ι).x j) :=
  weightOneFormCLM_apply k z v

/-- `θₖ` is invariant under each rotation `weightRotation θ` of `ℂ^ι`, read on `StdSpace ι`
through `EuclideanSpace.sumEquivProd`: in complex coordinates the rotation is
`uⱼ ↦ exp (i θⱼ) uⱼ`, and with `θ = 2π t k` these are the rotations of the circle action of
weights `k`. -/
theorem mpullback_weightRotation_weightOneForm (k : ι → ℤ) (θ : ι → ℝ) :
    SmoothForm.mpullback
      (fun z : StdSpace ι ↦
        EuclideanSpace.sumEquivProd.symm (weightRotation θ (EuclideanSpace.sumEquivProd z)))
      (contMDiff_iff_contDiff.2 (by fun_prop))
      (weightOneForm k) = weightOneForm k := by
  set R : StdSpace ι →L[ℝ] StdSpace ι :=
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := ι)).symm.toContinuousLinearMap.comp
      ((weightRotation θ).comp EuclideanSpace.sumEquivProd.toContinuousLinearMap)
  have hx (z : StdSpace ι) (j : ι) :
      (R z).x j = Real.cos (θ j) * z.x j - Real.sin (θ j) * z.y j := by
    simp [R]
  have hy (z : StdSpace ι) (j : ι) :
      (R z).y j = Real.sin (θ j) * z.x j + Real.cos (θ j) * z.y j := by
    simp [R]
  refine Subtype.ext (funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [SmoothForm.mpullback_apply, weightOneForm_apply, weightOneForm_apply, mfderiv_eq_fderiv]
  -- The pulled-back map is `R` written as a function, so its derivative is `R`.
  change ∑ j, (k j : ℝ) * ((R z).x j * (fderiv ℝ R z (v 0)).y j -
    (R z).y j * (fderiv ℝ R z (v 0)).x j) = _
  rw [R.fderiv]
  suffices ∀ w : StdSpace ι, ∑ j, (k j : ℝ) * ((R z).x j * (R w).y j - (R z).y j * (R w).x j) =
      ∑ j, (k j : ℝ) * (z.x j * w.y j - z.y j * w.x j) from this (v 0)
  intro w
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hx, hy, hx, hy]
  linear_combination (k j : ℝ) * (z.x j * w.y j - z.y j * w.x j) * sin_sq_add_cos_sq (θ j)

/-- On the generator `weightGenerator θ` of the rotations, the vector field
`∑ⱼ θⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})` read on `StdSpace ι` through `EuclideanSpace.sumEquivProd`, the
form `θₖ` takes the value `∑ⱼ kⱼ θⱼ (xⱼ² + yⱼ²)`. -/
theorem weightOneForm_apply_weightGenerator (k : ι → ℤ) (θ : ι → ℝ) (z : StdSpace ι) :
    (weightOneForm k).val z
        ![EuclideanSpace.sumEquivProd.symm (weightGenerator θ (EuclideanSpace.sumEquivProd z))] =
      ∑ j, (k j : ℝ) * θ j * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [weightOneForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [StdSpace.x_apply, StdSpace.y_apply]
  simp
  ring

/-- On the generator of the circle action of weights `k`, the vector field
`X = ∑ⱼ 2π kⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})`, the form `θₖ` takes the value
`2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)`. -/
theorem weightOneForm_apply_weightGenerator_two_pi_mul (k : ι → ℤ) (z : StdSpace ι) :
    (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator (fun j ↦ 2 * π * k j) (EuclideanSpace.sumEquivProd z))] =
      2 * π * ∑ j, (k j : ℝ) ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [weightOneForm_apply_weightGenerator, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The value of `θₖ` on the generator of the circle action of weights `k` is nonnegative. -/
theorem weightOneForm_apply_weightGenerator_nonneg (k : ι → ℤ) (z : StdSpace ι) :
    0 ≤ (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator (fun j ↦ 2 * π * k j) (EuclideanSpace.sumEquivProd z))] := by
  rw [weightOneForm_apply_weightGenerator_two_pi_mul]
  have := Real.pi_pos
  positivity

/-- When no weight is zero, the value of `θₖ` on the generator of the circle action of weights
`k` vanishes only at `0`. -/
theorem weightOneForm_apply_weightGenerator_eq_zero_iff {k : ι → ℤ} (hk : ∀ j, k j ≠ 0)
    {z : StdSpace ι} :
    (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator (fun j ↦ 2 * π * k j) (EuclideanSpace.sumEquivProd z))] = 0 ↔
      z = 0 := by
  rw [weightOneForm_apply_weightGenerator_two_pi_mul, mul_eq_zero, or_iff_right (by positivity),
    Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by positivity]
  refine ⟨fun h ↦ StdSpace.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_), fun h j _ ↦ by simp [h]⟩
  all_goals
    have hj := (mul_eq_zero.1 (h j (Finset.mem_univ j))).resolve_left (by simpa using hk j)
    simp only [map_zero, Pi.zero_apply]
    nlinarith [sq_nonneg (z.x j), sq_nonneg (z.y j)]

/-- The exterior derivative of `θₖ` is `2 ∑ⱼ kⱼ dxⱼ ∧ dyⱼ`: its value at `z` on two tangent
vectors `v 0`, `v 1` is `2 ∑ⱼ kⱼ (xⱼ(v 0) yⱼ(v 1) - yⱼ(v 0) xⱼ(v 1))`. -/
theorem mextDerivₗ_weightOneForm_apply (k : ι → ℤ) (z : StdSpace ι)
    (v : Fin 2 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm k)).val z v =
      2 * ∑ j, (k j : ℝ) * ((v 0 : StdSpace ι).x j * (v 1 : StdSpace ι).y j -
        (v 0 : StdSpace ι).y j * (v 1 : StdSpace ι).x j) := by
  rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv]
  -- On the model space the form is the continuous linear map `weightOneFormCLM k` of the point,
  -- which is its own derivative; tangent vectors are points of the model.
  suffices ∀ w : Fin 2 → StdSpace ι, ContinuousAlternatingMap.alternatizeUncurryFin
      (fderiv ℝ (weightOneFormCLM k) z) w =
        2 * ∑ j, (k j : ℝ) * ((w 0).x j * (w 1).y j - (w 0).y j * (w 1).x j) from this v
  intro w
  rw [ContinuousLinearMap.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, weightOneFormCLM_apply, weightOneFormCLM_apply, Finset.mul_sum]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Fin.removeNth_apply]
  ring

end SymplecticGeometry

end
