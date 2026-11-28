/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The model connection and the `∂̄` operators on `StdSpace ι`

For a complex function `f` on `StdSpace ι`, this file defines the formula by which the rescaled
unitary charts read the connection on the powers of a prequantum line bundle, and the two `∂̄`
operators built from it and from `df`, for a field `J` of real-linear endomorphisms of `StdSpace ι`:

* `SymplecticGeometry.modelConnection f z`: the real-linear map
  `v ↦ df_z v - (ω₀(z, v) / 2) • (i f(z))`, with `ω₀ = stdForm ι`;
* `SymplecticGeometry.flatDbarWith J f z`: Tau Ceti's complex-antilinear part
  `TauCeti.complexAntilinearPart` of `df_z`, for `J z` on `StdSpace ι` and multiplication by `i`
  on `ℂ`, that is `v ↦ ½ (df_z v + i df_z (J z v))`;
* `SymplecticGeometry.modelDbarWith J f z`: the complex-antilinear part of `modelConnection f z`
  for the same structures.

The readings of `RescaledUnitaryCharts` are these at the structure `J` pushed forward by the
chart, and the model operators of the peak functions are these at the constant structure
`J₀ = stdComplexStructure ι`.

## Main results

* `SymplecticGeometry.modelConnection_add`, `SymplecticGeometry.modelDbarWith_add`,
  `SymplecticGeometry.flatDbarWith_add` and their companions `_neg`, `_smul` and `_zero` for
  negation, complex scalars and zero: the three operators are additive on functions
  differentiable at `z`, and commute with complex scalars.
* `SymplecticGeometry.modelConnection_mul`, `SymplecticGeometry.flatDbarWith_mul`,
  `SymplecticGeometry.modelDbarWith_mul`: the Leibniz rules,
  `∂̄ (f g) = f ∂̄ g + g ∂̄_flat f` for the model `∂̄`.
* `SymplecticGeometry.contDiffAt_modelConnection`, `SymplecticGeometry.contDiffAt_flatDbarWith`,
  `SymplecticGeometry.contDiffAt_modelDbarWith`: where `f` is `C^(n + 1)` and `J` is `C^n`, all
  three are `C^n`.
* `SymplecticGeometry.modelConnection_congr_of_eventuallyEq`,
  `SymplecticGeometry.flatDbarWith_congr_of_eventuallyEq`,
  `SymplecticGeometry.modelDbarWith_congr_of_eventuallyEq`: their values at `z` depend only on the
  germ of `f` at `z`; `SymplecticGeometry.modelConnection_eventuallyEq`,
  `SymplecticGeometry.flatDbarWith_eventuallyEq` and `SymplecticGeometry.modelDbarWith_eventuallyEq`
  say the same of their germs.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002]
-/

public section

open TauCeti ContinuousLinearMap
open scoped Topology

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-! ### The model connection -/

/-- The **model connection** of a complex function `f` on `StdSpace ι` at `z`: the real-linear map
`v ↦ df_z v - (ω₀(z, v) / 2) • (i f(z))`, with `ω₀ = stdForm ι`. It is `df_z + i A₀(z) f(z)`, for
`A₀(z) v = -ω₀(z, v) / 2`. -/
noncomputable def modelConnection (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  fderiv ℝ f z -
    ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap ((stdForm ι).toBilinForm z)).smulRight
      (Complex.I * f z)

theorem modelConnection_def (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelConnection f z = fderiv ℝ f z -
      ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap ((stdForm ι).toBilinForm z)).smulRight
        (Complex.I * f z) :=
  (rfl)

theorem modelConnection_apply (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    modelConnection f z v = fderiv ℝ f z v - (2⁻¹ * stdForm ι z v : ℝ) • (Complex.I * f z) := by
  rw [modelConnection_def, sub_apply, smulRight_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', smul_eq_mul]

/-- The model connection is additive on functions differentiable at `z`. -/
theorem modelConnection_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    modelConnection (f + g) z = modelConnection f z + modelConnection g z := by
  ext v
  simp only [modelConnection_apply, fderiv_add hf hg, Pi.add_apply, add_apply, mul_add, smul_add]
  abel

@[simp]
theorem modelConnection_neg (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelConnection (-f) z = -modelConnection f z := by
  ext v
  simp only [modelConnection_apply, fderiv_neg, Pi.neg_apply, neg_apply, mul_neg, smul_neg]
  abel

@[simp]
theorem modelConnection_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelConnection (c • f) z = c • modelConnection f z := by
  ext v
  simp only [modelConnection_apply, fderiv_const_smul_field, Pi.smul_apply, smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

@[simp]
theorem modelConnection_zero (z : StdSpace ι) :
    modelConnection (0 : StdSpace ι → ℂ) z = 0 := by
  ext v
  simp [modelConnection_apply]

/-- The **Leibniz rule for the model connection**: for `f` and `g` differentiable at `z`, the
model connection of `f * g` at `z` is `f z` times that of `g` plus `g z • df_z`. -/
theorem modelConnection_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    modelConnection (fun y ↦ f y * g y) z = f z • modelConnection g z + g z • fderiv ℝ f z := by
  ext v
  simp only [modelConnection_apply, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

/-- The model connection at `z` depends only on the germ of `f` at `z`. -/
theorem modelConnection_congr_of_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : modelConnection f z = modelConnection g z := by
  rw [modelConnection_def, modelConnection_def, h.fderiv_eq, h.eq_of_nhds]

/-- Functions with the same germ at `z` have model connections with the same germ at `z`. -/
theorem modelConnection_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : modelConnection f =ᶠ[𝓝 z] modelConnection g :=
  h.eventually_nhds.mono fun _ hw ↦ modelConnection_congr_of_eventuallyEq hw

/-- The model connection of `f` is `C^n` at a point where `f` is `C^(n + 1)`. -/
theorem contDiffAt_modelConnection {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hf : ContDiffAt ℝ (n + 1) f z) : ContDiffAt ℝ n (modelConnection f) z := by
  -- The connection term is linear in the point, through `ω₀`, times `i f`.
  have hω : ContDiff ℝ n fun y : StdSpace ι ↦
      (2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap ((stdForm ι).toBilinForm y) :=
    (stdForm ι).toBilinForm.toContinuousBilinearMap.contDiff.const_smul _
  have h := (hf.fderiv_right le_rfl).sub
    (hω.contDiffAt.smulRight ((contDiffAt_const (c := Complex.I)).mul (hf.of_le le_self_add)))
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦ modelConnection_def ..)

/-! ### The flat `∂̄` for a field of structures -/

/-- The **flat `∂̄`** of a complex function `f` on `StdSpace ι` at `z`, for a field `J` of
real-linear endomorphisms of `StdSpace ι`: Tau Ceti's complex-antilinear part of `df_z`, for `J z`
and multiplication by `i` on `ℂ`, that is `v ↦ ½ (df_z v + i df_z (J z v))`. -/
noncomputable def flatDbarWith (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι)
    (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  complexAntilinearPartContinuousLinearMap (J z : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ f z)

theorem flatDbarWith_def (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z : StdSpace ι) :
    flatDbarWith J f z = complexAntilinearPartContinuousLinearMap
      (J z : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ f z) :=
  (rfl)

theorem flatDbarWith_apply (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z v : StdSpace ι) :
    flatDbarWith J f z v = (2⁻¹ : ℝ) • (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (J z v)) := by
  simp only [flatDbarWith_def, complexAntilinearPartContinuousLinearMap_apply_apply,
    TauCeti.complexAntilinearPart_apply, coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    smul_eq_mul]

variable {J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι}

/-- The flat `∂̄` is additive on functions differentiable at `z`. -/
theorem flatDbarWith_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDbarWith J (f + g) z = flatDbarWith J f z + flatDbarWith J g z := by
  simp [flatDbarWith_def, fderiv_add hf hg]

@[simp]
theorem flatDbarWith_neg (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbarWith J (-f) z = -flatDbarWith J f z := by
  rw [flatDbarWith_def, flatDbarWith_def, fderiv_neg, map_neg]

/-- The flat `∂̄` commutes with complex scalars. -/
@[simp]
theorem flatDbarWith_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbarWith J (c • f) z = c • flatDbarWith J f z := by
  ext v
  simp only [flatDbarWith_apply, fderiv_const_smul_field, Pi.smul_apply, smul_apply,
    smul_eq_mul, Complex.real_smul]
  ring

@[simp]
theorem flatDbarWith_zero (z : StdSpace ι) : flatDbarWith J (0 : StdSpace ι → ℂ) z = 0 := by
  simp [flatDbarWith_def]

/-- The **Leibniz rule for the flat `∂̄`**: for `f` and `g` differentiable at `z`, the flat `∂̄`
of `f * g` at `z` is `f z` times the flat `∂̄` of `g` plus `g z` times the flat `∂̄` of `f`. -/
theorem flatDbarWith_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDbarWith J (fun y ↦ f y * g y) z = f z • flatDbarWith J g z + g z • flatDbarWith J f z := by
  ext v
  simp only [add_apply, smul_apply, flatDbarWith_apply, fderiv_fun_mul hf hg, smul_eq_mul,
    Complex.real_smul]
  push_cast
  ring

/-- The flat `∂̄` at `z` depends only on the germ of `f` at `z`. -/
theorem flatDbarWith_congr_of_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : flatDbarWith J f z = flatDbarWith J g z := by
  rw [flatDbarWith_def, flatDbarWith_def, h.fderiv_eq]

/-- Functions with the same germ at `z` have flat `∂̄` with the same germ at `z`. -/
theorem flatDbarWith_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : flatDbarWith J f =ᶠ[𝓝 z] flatDbarWith J g :=
  h.eventually_nhds.mono fun _ hw ↦ flatDbarWith_congr_of_eventuallyEq hw

/-- The flat `∂̄` of `f` is `C^n` at a point where `f` is `C^(n + 1)` and `J` is `C^n`. -/
theorem contDiffAt_flatDbarWith {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hJ : ContDiffAt ℝ n J z) (hf : ContDiffAt ℝ (n + 1) f z) :
    ContDiffAt ℝ n (flatDbarWith J f) z :=
  hJ.complexAntilinearPartContinuousLinearMap _ (hf.fderiv_right le_rfl)

/-! ### The model `∂̄` for a field of structures -/

/-- The **model `∂̄`** of a complex function `f` on `StdSpace ι` at `z`, for a field `J` of
real-linear endomorphisms of `StdSpace ι`: Tau Ceti's complex-antilinear part of the model
connection `SymplecticGeometry.modelConnection f z`, for `J z` and multiplication by `i` on `ℂ`. -/
noncomputable def modelDbarWith (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι)
    (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  complexAntilinearPartContinuousLinearMap (J z : StdSpace ι →ₗ[ℝ] StdSpace ι)
    (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (modelConnection f z)

theorem modelDbarWith_def (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z : StdSpace ι) :
    modelDbarWith J f z = complexAntilinearPartContinuousLinearMap
      (J z : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (modelConnection f z) :=
  (rfl)

theorem modelDbarWith_apply (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z v : StdSpace ι) :
    modelDbarWith J f z v =
      (2⁻¹ : ℝ) • (modelConnection f z v + Complex.I * modelConnection f z (J z v)) := by
  simp only [modelDbarWith_def, complexAntilinearPartContinuousLinearMap_apply_apply,
    TauCeti.complexAntilinearPart_apply, coe_coe, AlmostComplexStructure.ofComplexModule_apply,
    smul_eq_mul]

/-- The model `∂̄` is additive on functions differentiable at `z`. -/
theorem modelDbarWith_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    modelDbarWith J (f + g) z = modelDbarWith J f z + modelDbarWith J g z := by
  rw [modelDbarWith_def, modelConnection_add hf hg, map_add, modelDbarWith_def, modelDbarWith_def]

@[simp]
theorem modelDbarWith_neg (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelDbarWith J (-f) z = -modelDbarWith J f z := by
  rw [modelDbarWith_def, modelConnection_neg, map_neg, modelDbarWith_def]

/-- The model `∂̄` commutes with complex scalars. -/
@[simp]
theorem modelDbarWith_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelDbarWith J (c • f) z = c • modelDbarWith J f z := by
  ext v
  simp only [modelDbarWith_apply, modelConnection_smul, smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

@[simp]
theorem modelDbarWith_zero (z : StdSpace ι) : modelDbarWith J (0 : StdSpace ι → ℂ) z = 0 := by
  rw [modelDbarWith_def, modelConnection_zero, map_zero]

/-- The **Leibniz rule for the model `∂̄`**: for `f` and `g` differentiable at `z`, the model
`∂̄` of `f * g` at `z` is `f z` times the model `∂̄` of `g` plus `g z` times the flat `∂̄` of
`f`. -/
theorem modelDbarWith_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    modelDbarWith J (fun y ↦ f y * g y) z =
      f z • modelDbarWith J g z + g z • flatDbarWith J f z := by
  ext v
  simp only [modelDbarWith_apply, flatDbarWith_apply, modelConnection_mul hf hg, add_apply,
    smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- The model `∂̄` at `z` depends only on the germ of `f` at `z`. -/
theorem modelDbarWith_congr_of_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : modelDbarWith J f z = modelDbarWith J g z := by
  rw [modelDbarWith_def, modelDbarWith_def, modelConnection_congr_of_eventuallyEq h]

/-- Functions with the same germ at `z` have model `∂̄` with the same germ at `z`. -/
theorem modelDbarWith_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : modelDbarWith J f =ᶠ[𝓝 z] modelDbarWith J g :=
  h.eventually_nhds.mono fun _ hw ↦ modelDbarWith_congr_of_eventuallyEq hw

/-- The model `∂̄` of `f` is `C^n` at a point where `f` is `C^(n + 1)` and `J` is `C^n`. -/
theorem contDiffAt_modelDbarWith {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hJ : ContDiffAt ℝ n J z) (hf : ContDiffAt ℝ (n + 1) f z) :
    ContDiffAt ℝ n (modelDbarWith J f) z :=
  hJ.complexAntilinearPartContinuousLinearMap _ (contDiffAt_modelConnection hf)

end SymplecticGeometry

end
