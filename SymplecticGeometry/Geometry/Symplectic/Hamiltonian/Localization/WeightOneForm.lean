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
public import TauCeti.Geometry.Symplectic.Liouville.Linear
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Volume

/-!
# The one-form of a family of weights on the standard model

For real weights `k : ι → ℝ`, this file defines the smooth one-form
`θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` on `StdSpace ι`, `SymplecticGeometry.weightOneForm k`, in the
coordinates `z.x j`, `z.y j` of the standard model. Near a fixed point of a circle action with
integer weights `k`, read through the weight chart `SymplecticGeometry.exists_weightChart`, it is
the model of the one-form that localizes the Duistermaat–Heckman integral.

The form is the radial one-form `z ↦ Bₖ(z, ·)` of the skew bilinear form
`Bₖ(z, w) = ∑ⱼ kⱼ (xⱼ(z) yⱼ(w) - yⱼ(z) xⱼ(w))` (`SymplecticGeometry.weightBilin k`), built with
Tau Ceti's `ContinuousLinearMap.liouvilleFormCLM`, in the same way as Tau Ceti's
`TauCeti.SymplecticForm.radialPrimitive`; its exterior derivative comes from Tau Ceti's
`ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew`.

Its properties are read through `EuclideanSpace.sumEquivProd`, which identifies `StdSpace ι`
with Tau Ceti's model `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` of `ℂ^ι`:

* `weightOneForm_apply`: its value at `z` on `v` is `∑ⱼ kⱼ (xⱼ(z) yⱼ(v) - yⱼ(z) xⱼ(v))`;
* `weightOneForm_apply_eq_inner`: it is the Euclidean dual of the generator
  `TauCeti.weightGenerator k`, `θₖ(z)(v) = ⟪Xₖ(z), v⟫`;
* `mpullback_weightRotation_weightOneForm`: it is invariant under every rotation
  `TauCeti.weightRotation θ`, which in complex coordinates is `uⱼ ↦ exp (i θⱼ) uⱼ` (the lemma
  `TauCeti.weightRotation_sumEquivProd_complexToRealEuclidean` of the library's
  `Hamiltonian/WeightModel/Basic.lean`); with `θ = 2π t k` these are the rotations of the circle
  action with weights `k`;
* `weightOneForm_apply_weightGenerator`: on the generator `TauCeti.weightGenerator θ` of those
  rotations, the vector field `∑ⱼ θⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})`, it takes the value
  `∑ⱼ kⱼ θⱼ (xⱼ² + yⱼ²)`; on `Xₖ` itself this is `‖Xₖ(z)‖²`
  (`weightOneForm_apply_weightGenerator_self`), and for `θ = 2π k` it is
  `2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)`, which is nonnegative (`weightOneForm_apply_weightGenerator_nonneg`)
  and, when no weight is zero, vanishes only at `0`
  (`weightOneForm_apply_weightGenerator_eq_zero_iff`);
* `mextDerivₗ_weightOneForm_apply`: its exterior derivative is `2 ∑ⱼ kⱼ dxⱼ ∧ dyⱼ`; for the
  weights `kⱼ = 1/2` this is the standard form `ω₀` (`mextDerivₗ_weightOneForm_half_apply`);
* `wedgePow_mextDerivₗ_weightOneForm_apply`: with `n = Fintype.card ι`, its top wedge power
  `(dθₖ)ⁿ` is `2ⁿ ∏ⱼ kⱼ · ω₀ⁿ`, by `SymplecticGeometry.wedgePow_card_eq_prod_smul`.

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

/-- The skew bilinear form `Bₖ(z, w) = ∑ⱼ kⱼ (xⱼ(z) yⱼ(w) - yⱼ(z) xⱼ(w))` of a family of weights
`k` on the standard model `StdSpace ι`. -/
def weightBilin (k : ι → ℝ) : StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ :=
  ∑ j, k j •
    ((EuclideanSpace.proj (Sum.inl j)).smulRight (EuclideanSpace.proj (Sum.inr j)) -
      (EuclideanSpace.proj (Sum.inr j)).smulRight (EuclideanSpace.proj (Sum.inl j)))

@[simp]
theorem weightBilin_apply (k : ι → ℝ) (z w : StdSpace ι) :
    weightBilin k z w = ∑ j, k j * (z.x j * w.y j - z.y j * w.x j) := by
  simp [weightBilin]

/-- The bilinear form `Bₖ` is skew-symmetric. -/
theorem weightBilin_apply_swap (k : ι → ℝ) (z w : StdSpace ι) :
    weightBilin k w z = -weightBilin k z w := by
  simp only [weightBilin_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The one-form `θₖ = ∑ⱼ kⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` of a family of weights `k` on the standard model
`StdSpace ι`: the radial one-form `z ↦ Bₖ(z, ·)` of `weightBilin k`. -/
def weightOneForm (k : ι → ℝ) : SmoothForm 𝓘(ℝ, StdSpace ι) (StdSpace ι) ℝ 1 :=
  ⟨fun z ↦ ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • weightBilin k) z,
    (isSmoothForm_modelSpace_iff.2
      (ContinuousLinearMap.liouvilleFormCLM _).contDiff).mem_smoothBundleForms⟩

theorem weightOneForm_val (k : ι → ℝ) :
    (weightOneForm k).val = ⇑(ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • weightBilin k)) :=
  (rfl)

/-- The value of `θₖ` at `z` on a tangent vector `v 0` is
`∑ⱼ kⱼ (xⱼ(z) yⱼ(v 0) - yⱼ(z) xⱼ(v 0))`. -/
@[simp]
theorem weightOneForm_apply (k : ι → ℝ) (z : StdSpace ι)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (weightOneForm k).val z v =
      ∑ j, k j * (z.x j * (v 0 : StdSpace ι).y j - z.y j * (v 0 : StdSpace ι).x j) := by
  rw [weightOneForm_val]
  -- Tangent vectors at `z` are points of `StdSpace ι`, where `liouvilleFormCLM_apply` is stated.
  suffices ∀ w : Fin 1 → StdSpace ι,
      ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • weightBilin k) z w =
        ∑ j, k j * (z.x j * (w 0).y j - z.y j * (w 0).x j) from this v
  intro w
  simp

/-- `θₖ` is the Euclidean dual of the generator `weightGenerator k`, read on `StdSpace ι` through
`EuclideanSpace.sumEquivProd`: `θₖ(z)(v 0) = ⟪Xₖ(z), v 0⟫`. -/
theorem weightOneForm_apply_eq_inner (k : ι → ℝ) (z : StdSpace ι)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (weightOneForm k).val z v = inner ℝ
      (EuclideanSpace.sumEquivProd.symm (weightGenerator k (EuclideanSpace.sumEquivProd z)))
      (v 0 : StdSpace ι) := by
  rw [weightOneForm_apply]
  -- The tangent vector `v 0` is a point of `StdSpace ι`, where `StdSpace.inner_eq_sum` is stated.
  suffices ∀ w : StdSpace ι, ∑ j, k j * (z.x j * w.y j - z.y j * w.x j) = inner ℝ
      (EuclideanSpace.sumEquivProd.symm (weightGenerator k (EuclideanSpace.sumEquivProd z))) w
    from this (v 0)
  intro w
  rw [StdSpace.inner_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [StdSpace.x_apply, StdSpace.y_apply]
  simp
  ring

/-- `θₖ` is invariant under each rotation `weightRotation θ` of `ℂ^ι`, read on `StdSpace ι`
through `EuclideanSpace.sumEquivProd`: in complex coordinates the rotation is
`uⱼ ↦ exp (i θⱼ) uⱼ`, and with `θ = 2π t k` these are the rotations of the circle action of
weights `k`. -/
theorem mpullback_weightRotation_weightOneForm (k θ : ι → ℝ) :
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
  refine SmoothBundleForm.ext fun z v ↦ ?_
  rw [SmoothForm.mpullback_apply, weightOneForm_apply, weightOneForm_apply, mfderiv_eq_fderiv]
  -- The pulled-back map is `R` written as a function, so its derivative is `R`.
  change ∑ j, k j * ((R z).x j * (fderiv ℝ R z (v 0)).y j -
    (R z).y j * (fderiv ℝ R z (v 0)).x j) = _
  rw [R.fderiv]
  suffices ∀ w : StdSpace ι, ∑ j, k j * ((R z).x j * (R w).y j - (R z).y j * (R w).x j) =
      ∑ j, k j * (z.x j * w.y j - z.y j * w.x j) from this (v 0)
  intro w
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hx, hy, hx, hy]
  linear_combination k j * (z.x j * w.y j - z.y j * w.x j) * sin_sq_add_cos_sq (θ j)

/-- On the generator `weightGenerator θ` of the rotations, the vector field
`∑ⱼ θⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})` read on `StdSpace ι` through `EuclideanSpace.sumEquivProd`, the
form `θₖ` takes the value `∑ⱼ kⱼ θⱼ (xⱼ² + yⱼ²)`. -/
theorem weightOneForm_apply_weightGenerator (k θ : ι → ℝ) (z : StdSpace ι) :
    (weightOneForm k).val z
        ![EuclideanSpace.sumEquivProd.symm (weightGenerator θ (EuclideanSpace.sumEquivProd z))] =
      ∑ j, k j * θ j * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [weightOneForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [StdSpace.x_apply, StdSpace.y_apply]
  simp
  ring

/-- On its own generator `Xₖ = weightGenerator k`, the form `θₖ` takes the value `‖Xₖ(z)‖²`. -/
theorem weightOneForm_apply_weightGenerator_self (k : ι → ℝ) (z : StdSpace ι) :
    (weightOneForm k).val z
        ![EuclideanSpace.sumEquivProd.symm (weightGenerator k (EuclideanSpace.sumEquivProd z))] =
      ‖EuclideanSpace.sumEquivProd.symm (weightGenerator k (EuclideanSpace.sumEquivProd z))‖ ^ 2 :=
  (weightOneForm_apply_eq_inner k z _).trans (real_inner_self_eq_norm_sq _)

/-- The value of `θₖ` on the generator `weightGenerator θ` is linear in the angles `θ`:
scaling them by `c` scales it by `c`. -/
theorem weightOneForm_apply_weightGenerator_smul (k θ : ι → ℝ) (c : ℝ) (z : StdSpace ι) :
    (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator (c • θ) (EuclideanSpace.sumEquivProd z))] =
      c * (weightOneForm k).val z
        ![EuclideanSpace.sumEquivProd.symm
          (weightGenerator θ (EuclideanSpace.sumEquivProd z))] := by
  rw [weightOneForm_apply_weightGenerator, weightOneForm_apply_weightGenerator, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- On the generator of the circle action of weights `k`, the vector field
`X = ∑ⱼ 2π kⱼ (xⱼ ∂_{yⱼ} - yⱼ ∂_{xⱼ})`, the form `θₖ` takes the value
`2π ∑ⱼ kⱼ² (xⱼ² + yⱼ²)`. -/
theorem weightOneForm_apply_weightGenerator_two_pi_mul (k : ι → ℝ) (z : StdSpace ι) :
    (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))] =
      2 * π * ∑ j, k j ^ 2 * (z.x j ^ 2 + z.y j ^ 2) := by
  rw [weightOneForm_apply_weightGenerator_smul, weightOneForm_apply_weightGenerator]
  simp only [sq]

/-- The value of `θₖ` on the generator of the circle action of weights `k` is nonnegative. -/
theorem weightOneForm_apply_weightGenerator_nonneg (k : ι → ℝ) (z : StdSpace ι) :
    0 ≤ (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))] := by
  rw [weightOneForm_apply_weightGenerator_smul, weightOneForm_apply_weightGenerator_self]
  positivity

/-- When no weight is zero, the value of `θₖ` on the generator of the circle action of weights
`k` vanishes only at `0`. -/
theorem weightOneForm_apply_weightGenerator_eq_zero_iff {k : ι → ℝ} (hk : ∀ j, k j ≠ 0)
    {z : StdSpace ι} :
    (weightOneForm k).val z ![EuclideanSpace.sumEquivProd.symm
        (weightGenerator ((2 * π) • k) (EuclideanSpace.sumEquivProd z))] = 0 ↔
      z = 0 := by
  rw [weightOneForm_apply_weightGenerator_smul, weightOneForm_apply_weightGenerator_self,
    mul_eq_zero, or_iff_right (by positivity), sq_eq_zero_iff, norm_eq_zero,
    EmbeddingLike.map_eq_zero_iff, weightGenerator_apply_eq_zero_iff]
  constructor
  · intro h
    apply EuclideanSpace.sumEquivProd.injective
    rw [map_zero]
    refine Prod.ext (PiLp.ext fun i ↦ ?_) (PiLp.ext fun i ↦ ?_) <;> by_contra hi
    · exact hk i (h i (Or.inl hi))
    · exact hk i (h i (Or.inr hi))
  · rintro rfl i hi
    simp at hi

/-- The exterior derivative of `θₖ` is `2 ∑ⱼ kⱼ dxⱼ ∧ dyⱼ`: its value at `z` on two tangent
vectors `v 0`, `v 1` is `2 ∑ⱼ kⱼ (xⱼ(v 0) yⱼ(v 1) - yⱼ(v 0) xⱼ(v 1))`. -/
theorem mextDerivₗ_weightOneForm_apply (k : ι → ℝ) (z : StdSpace ι)
    (v : Fin 2 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm k)).val z v =
      2 * ∑ j, k j * ((v 0 : StdSpace ι).x j * (v 1 : StdSpace ι).y j -
        (v 0 : StdSpace ι).y j * (v 1 : StdSpace ι).x j) := by
  rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv, weightOneForm_val]
  -- Tangent vectors at `z` are points of `StdSpace ι`, where Tau Ceti's lemma is stated.
  suffices ∀ w : Fin 2 → StdSpace ι,
      extDeriv (⇑(ContinuousLinearMap.liouvilleFormCLM ((2 : ℝ) • weightBilin k))) z w =
        2 * ∑ j, k j * ((w 0).x j * (w 1).y j - (w 0).y j * (w 1).x j) from this v
  intro v
  rw [ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero
      (fun w w' ↦ by
        simp only [FunLike.coe_smul, Pi.smul_apply, weightBilin_apply_swap k w' w,
          smul_neg])]
  simp

/-- For the weights `kⱼ = 1/2`, the exterior derivative of the model one-form is the standard
symplectic form: `d θ_{1/2} = ω₀`. -/
theorem mextDerivₗ_weightOneForm_half_apply (z : StdSpace ι)
    (v : Fin 2 → TangentSpace 𝓘(ℝ, StdSpace ι) z) :
    (mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm fun _ ↦ 1 / 2)).val z v =
      stdForm ι (v 0) (v 1) := by
  rw [mextDerivₗ_weightOneForm_apply]
  refine Eq.trans ?_ (stdForm_apply (v 0) (v 1)).symm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The top wedge power of `dθₖ`.** With `n = Fintype.card ι`, the `n`-th wedge power of the
exterior derivative `dθₖ = 2 ∑ⱼ kⱼ dxⱼ ∧ dyⱼ` at any point is `2ⁿ ∏ⱼ kⱼ` times the `n`-th wedge
power `ω₀ⁿ` of the standard form `ω₀ = ∑ⱼ dxⱼ ∧ dyⱼ`, given as a continuous alternating map. -/
theorem wedgePow_mextDerivₗ_weightOneForm_apply (k : ι → ℝ) (z : StdSpace ι)
    {ω₀ : StdSpace ι [⋀^Fin 2]→L[ℝ] ℝ} (hω₀ : ∀ v w, ω₀ ![v, w] = stdForm ι v w) :
    ((mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm k)).val z).wedgePow (Fintype.card ι) =
      (2 ^ Fintype.card ι * ∏ j, k j) • ω₀.wedgePow (Fintype.card ι) := by
  have hω (v w : StdSpace ι) :
      (mextDerivₗ 𝓘(ℝ, StdSpace ι) 1 (weightOneForm k)).val z ![v, w] =
        ∑ j, 2 * k j * (v.x j * w.y j - v.y j * w.x j) :=
    (mextDerivₗ_weightOneForm_apply k z ![v, w]).trans (by simp [Finset.mul_sum, mul_assoc])
  have h := wedgePow_card_eq_prod_smul hω₀ hω
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at h
  -- `h` is stated on `StdSpace ι`, the goal on the tangent space at `z`, which is `StdSpace ι`.
  exact h

end SymplecticGeometry

end
