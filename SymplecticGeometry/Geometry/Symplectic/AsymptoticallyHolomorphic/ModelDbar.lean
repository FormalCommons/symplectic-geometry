/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
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
* `SymplecticGeometry.exists_jetNormAt_modelConnection_le`: since `ω₀(z, ·)` is linear in `z`,
  the `r`-jet norm of `modelConnection f` at `z` is at most a constant, depending only on `r`,
  times `1 + ‖z‖` and the `(r + 1)`-jet norm of `f` at `z`
  (from `SymplecticGeometry.jetNormAt_bilinear_le`).
* `SymplecticGeometry.modelDbarWith_eq_add`: changing the field of structures from `J'` to `J`
  adds `(i / 2) L ∘ (J z - J' z)` to the model `∂̄`, for `L = modelConnection f z`; so the
  `r`-jet norm of the difference is at most a constant times `1 + ‖z‖`, the `r`-jet norm of
  `J - J'` and the `(r + 1)`-jet norm of `f`
  (`SymplecticGeometry.exists_jetNormAt_modelDbarWith_sub_le`).
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

/-- The model connection as a function of the point:
`w ↦ df_w - R (ω₀(w, ·) / 2) (i f(w))`, for `R = ContinuousLinearMap.smulRightL`, a continuous
bilinear map. -/
theorem modelConnection_eq (f : StdSpace ι → ℂ) :
    modelConnection f = fun w ↦ fderiv ℝ f w -
      smulRightL ℝ ℝ ℝ (StdSpace ι) ℂ
        ((2⁻¹ : ℝ) • (stdForm ι).toBilinForm.toContinuousBilinearMap w) (Complex.I * f w) := by
  funext w
  ext v
  rw [modelConnection_apply]
  simp only [sub_apply, smulRightL_apply_apply, smulRight_apply, smul_apply,
    LinearMap.toContinuousBilinearMap_apply, smul_eq_mul]

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

/-- **Jets of the model connection.** For every order `r` there is a constant `C ≥ 0` such that,
for every `f` and at every point `z` where `f` is `C^(r + 1)`, the `r`-jet norm at `z` of the model
connection of `f` is at most `C * (1 + ‖z‖)` times the `(r + 1)`-jet norm of `f` at `z`. -/
theorem exists_jetNormAt_modelConnection_le (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : StdSpace ι → ℂ) {z : StdSpace ι}, ContDiffAt ℝ (r + 1 : ℕ) f z →
      jetNormAt ℝ r (modelConnection f) z ≤ C * (1 + ‖z‖) * jetNormAt ℝ (r + 1) f z := by
  set Ω : StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ :=
    (2⁻¹ : ℝ) • (stdForm ι).toBilinForm.toContinuousBilinearMap
  -- Instance search does not find the operator norm on this space of bilinear maps unaided.
  let : NormedAddCommGroup (ℂ →L[ℝ] StdSpace ι →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (ℂ →L[ℝ] StdSpace ι →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
  set R := smulRightL ℝ ℝ ℝ (StdSpace ι) ℂ
  refine ⟨1 + 2 ^ r * ‖R‖ * ‖Ω‖, by positivity, fun g z hs ↦ ?_⟩
  set J1 := jetNormAt ℝ (r + 1) g z
  have hJ1 : 0 ≤ J1 := jetNormAt_nonneg _ _ _
  have hs' : ContDiffAt ℝ (r + 1) g z := by exact_mod_cast hs
  have hΩ : jetNormAt ℝ r Ω z ≤ ‖Ω‖ * (1 + ‖z‖) := by
    have := jetNormAt_continuousLinearMap_le Ω r z
    have := Ω.le_opNorm z
    nlinarith [norm_nonneg Ω]
  have hIg : jetNormAt ℝ r (fun w ↦ Complex.I * g w) z ≤ J1 := by
    have : jetNormAt ℝ r (Complex.I • g) z = jetNormAt ℝ r g z := by simp
    exact this.le.trans (jetNormAt_mono g z (Nat.le_succ r))
  have hIc : ContDiffAt ℝ r (fun w ↦ Complex.I * g w) z :=
    (contDiffAt_const (c := Complex.I)).mul (hs.of_le (by exact_mod_cast Nat.le_succ r))
  have hRjet := jetNormAt_bilinear_le R Ω.contDiff.contDiffAt hIc
  have hd : jetNormAt ℝ r (fderiv ℝ g) z ≤ J1 :=
    (le_add_of_nonneg_left (norm_nonneg (g z))).trans_eq (jetNormAt_succ r g z).symm
  have hadd := jetNormAt_add_le (hs'.fderiv_right le_rfl)
    ((R.contDiff.contDiffAt.comp z Ω.contDiff.contDiffAt).clm_apply hIc).neg
  have hL : modelConnection g = fderiv ℝ g + -fun w ↦ R (Ω w) (Complex.I * g w) := by
    funext w
    simp only [modelConnection_eq, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, Ω, R, smul_apply]
  rw [hL]
  refine (hadd.trans_eq (congrArg _
    (jetNormAt_neg r (fun w ↦ R (Ω w) (Complex.I * g w)) z))).trans ?_
  have : 0 ≤ ‖R‖ := ContinuousLinearMap.opNorm_nonneg R
  have : 0 ≤ ‖Ω‖ := Ω.opNorm_nonneg
  have : 0 ≤ jetNormAt ℝ r Ω z := jetNormAt_nonneg _ _ _
  have : 0 ≤ jetNormAt ℝ r (fun w ↦ Complex.I * g w) z := jetNormAt_nonneg _ _ _
  calc _ ≤ J1 + 2 ^ r * ‖R‖ * (‖Ω‖ * (1 + ‖z‖)) * J1 := by
        refine add_le_add hd (hRjet.trans ?_)
        gcongr
    _ ≤ (1 + 2 ^ r * ‖R‖ * ‖Ω‖) * (1 + ‖z‖) * J1 := by
        nlinarith [mul_nonneg hJ1 (norm_nonneg z)]

/-! ### The flat `∂̄` for a field of structures -/

/-- The **flat `∂̄`** of a complex function `f` on `StdSpace ι` at `z`, for a field `J` of
real-linear endomorphisms of `StdSpace ι`: Tau Ceti's complex-antilinear part of `df_z`, for `J z`
and multiplication by `i` on `ℂ`, that is `v ↦ ½ (df_z v + i df_z (J z v))`. -/
noncomputable def flatDbarWith (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι)
    (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  complexAntilinearPartContinuousLinearMap (J z)
    (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (fderiv ℝ f z)

theorem flatDbarWith_def (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z : StdSpace ι) :
    flatDbarWith J f z = complexAntilinearPartContinuousLinearMap (J z)
      (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (fderiv ℝ f z) :=
  (rfl)

theorem flatDbarWith_apply (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z v : StdSpace ι) :
    flatDbarWith J f z v = (2⁻¹ : ℝ) • (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (J z v)) := by
  simp only [flatDbarWith_def, complexAntilinearPartContinuousLinearMap_apply_apply,
    TauCeti.complexAntilinearPart_apply, coe_coe, ContinuousLinearEquiv.coe_coe,
    Complex.smulIEquiv_apply, smul_eq_mul]

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
  complexAntilinearPartContinuousLinearMap (J z)
    (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (modelConnection f z)

theorem modelDbarWith_def (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z : StdSpace ι) :
    modelDbarWith J f z = complexAntilinearPartContinuousLinearMap (J z)
      (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (modelConnection f z) :=
  (rfl)

theorem modelDbarWith_apply (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
    (z v : StdSpace ι) :
    modelDbarWith J f z v =
      (2⁻¹ : ℝ) • (modelConnection f z v + Complex.I * modelConnection f z (J z v)) := by
  simp only [modelDbarWith_def, complexAntilinearPartContinuousLinearMap_apply_apply,
    TauCeti.complexAntilinearPart_apply, coe_coe, ContinuousLinearEquiv.coe_coe,
    Complex.smulIEquiv_apply, smul_eq_mul]

/-- **Change of structure in the model `∂̄`.** For two fields `J` and `J'` of real-linear
endomorphisms of `StdSpace ι`, the model `∂̄` of `f` for `J` at `z` is that for `J'` plus
`(i / 2) L ∘ (J z - J' z)`, for `L` the model connection of `f` at `z`. -/
theorem modelDbarWith_eq_add (J J' : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι)
    (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelDbarWith J f z = modelDbarWith J' f z +
      (((2⁻¹ : ℂ) * Complex.I) • modelConnection f z).comp (J z - J' z) := by
  ext v
  rw [add_apply, modelDbarWith_apply, modelDbarWith_apply, comp_apply, sub_apply, map_sub,
    smul_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

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

/-- **Jets of a change of structure in the model `∂̄`.** For every order `r` there is a constant
`C ≥ 0` such that, for all fields `J` and `J'` of real-linear endomorphisms of `StdSpace ι`, every
`f` and every point `z` where `f` is `C^(r + 1)` and `J` and `J'` are `C^r`, the `r`-jet norm at
`z` of the difference of the model `∂̄` of `f` for `J` and for `J'` is at most `C * (1 + ‖z‖)`
times the `r`-jet norm of `J - J'` and the `(r + 1)`-jet norm of `f`. -/
theorem exists_jetNormAt_modelDbarWith_sub_le (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J J' : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
      {z : StdSpace ι}, ContDiffAt ℝ (r + 1 : ℕ) f z → ContDiffAt ℝ r J z → ContDiffAt ℝ r J' z →
      jetNormAt ℝ r (fun w ↦ modelDbarWith J f w - modelDbarWith J' f w) z ≤
        C * (1 + ‖z‖) * jetNormAt ℝ r (fun w ↦ J w - J' w) z * jetNormAt ℝ (r + 1) f z := by
  set c : ℂ := (2⁻¹ : ℂ) * Complex.I
  -- Instance search does not find the operator norm on this space of bilinear maps unaided.
  let : NormedAddCommGroup ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  set B := compL ℝ (StdSpace ι) (StdSpace ι) ℂ
  obtain ⟨A, hA0, hA⟩ := exists_jetNormAt_modelConnection_le (ι := ι) r
  refine ⟨2 ^ r * ‖B‖ * ‖c‖ * A, by positivity, fun J J' f z hf hJ hJ' ↦ ?_⟩
  -- The difference is bilinear in `c • L` and `J - J'`, for `L` the model connection of `f`.
  have heq : (fun w ↦ modelDbarWith J f w - modelDbarWith J' f w) =
      fun w ↦ B ((c • modelConnection f) w) (J w - J' w) := by
    funext w
    rw [modelDbarWith_eq_add J J', add_sub_cancel_left, compL_apply, Pi.smul_apply]
  have hf' : ContDiffAt ℝ (r + 1) f z := by exact_mod_cast hf
  have hT := jetNormAt_bilinear_le B (f := c • modelConnection f)
    ((contDiffAt_modelConnection hf').const_smul c) (hJ.sub hJ')
  rw [jetNormAt_smul] at hT
  rw [heq]
  refine hT.trans ?_
  have : 0 ≤ ‖B‖ := opNorm_nonneg B
  have : 0 ≤ jetNormAt ℝ r (fun w ↦ J w - J' w) z := jetNormAt_nonneg _ _ _
  have : 0 ≤ jetNormAt ℝ (r + 1) f z := jetNormAt_nonneg _ _ _
  calc 2 ^ r * ‖B‖ * (‖c‖ * jetNormAt ℝ r (modelConnection f) z) *
        jetNormAt ℝ r (fun w ↦ J w - J' w) z
      ≤ 2 ^ r * ‖B‖ * (‖c‖ * (A * (1 + ‖z‖) * jetNormAt ℝ (r + 1) f z)) *
          jetNormAt ℝ r (fun w ↦ J w - J' w) z := by
        gcongr
        exact hA f hf
    _ = _ := by ring

end SymplecticGeometry

end
