/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Complex-linear and complex-antilinear parts of an operator: bounds, scalars, smoothness

For a continuous real-linear operator `Ψ` between complex normed spaces, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms. Seen as a
real-linear operator by Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, the
complex-antilinear part keeps its operator norm
(`ContinuousLinearMap.norm_complexAntilinearPartL_apply`), and `complexAntilinearPartL` itself has
operator norm at most `1` (`ContinuousLinearMap.norm_complexAntilinearPartL_le`), also for real
structures on `E` and `F` given separately and compatible with the complex ones. The bound on the
complex-antilinear part makes it a continuous real-linear map into the complex-antilinear
operators, `ContinuousLinearMap.complexAntilinearPartCLM`, again of operator norm at most `1`
(`ContinuousLinearMap.norm_complexAntilinearPartCLM_le`).

A continuous complex-antilinear operator is also a continuous real-linear one, by Mathlib's
`AddMonoidHom.toRealLinearMap`, with the same operator norm. This gives a real-linear isometry
`ContinuousLinearMap.restrictScalarsₛₗLI` from the complex-antilinear operators into the
real-linear ones. Tau Ceti's
`ContinuousLinearMap.complexAntilinearPartL` is `ContinuousLinearMap.complexAntilinearPartCLM`
followed by this isometry
(`ContinuousLinearMap.restrictScalarsₛₗLI_comp_complexAntilinearPartCLM`), and a
complex-antilinear operator is its own complex-antilinear part
(`ContinuousLinearMap.complexAntilinearPart_restrictScalarsₛₗLI`).

The Wirtinger derivatives of a map are the complex-linear and complex-antilinear parts of its
real derivative, and the derivative of `Ψ` is `Ψ`. So the bounds are Tau Ceti's
`TauCeti.norm_wirtingerDeriv_apply_le` and `TauCeti.norm_conjWirtingerDeriv_apply_le` for the
map `Ψ` itself.

Both parts commute with complex scalars (`ContinuousLinearMap.complexLinearPart_complex_smul`,
`ContinuousLinearMap.complexAntilinearPart_complex_smul`), next to Tau Ceti's versions for real
scalars, and their values at a fixed vector are as smooth as the operator
(`ContDiffOn.complexLinearPart_apply`, `ContDiffOn.complexAntilinearPart_apply`).
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem norm_complexLinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ by
    simpa [TauCeti.wirtingerDeriv_eq_complexLinearPart] using
      TauCeti.norm_wirtingerDeriv_apply_le (⇑Ψ) 0 v

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ by
    simpa [TauCeti.conjWirtingerDeriv_eq_complexAntilinearPart] using
      TauCeti.norm_conjWirtingerDeriv_apply_le (⇑Ψ) 0 v

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, which sees the complex-antilinear part
of an operator as a real-linear operator, preserves its operator norm. -/
theorem norm_complexAntilinearPartL_apply (Ψ : E →L[ℝ] F) :
    ‖complexAntilinearPartL Ψ‖ = ‖Ψ.complexAntilinearPart‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_)
  · rw [complexAntilinearPartL_apply_apply, ← complexAntilinearPart_apply]
    exact le_opNorm _ v
  · rw [complexAntilinearPart_apply, ← complexAntilinearPartL_apply_apply]
    exact le_opNorm _ v

/-- Pointwise form of `ContinuousLinearMap.norm_complexLinearPart_le`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexLinearPart.le_of_opNorm_le Ψ.norm_complexLinearPart_le v

/-- Pointwise form of `ContinuousLinearMap.norm_complexAntilinearPart_le`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexAntilinearPart.le_of_opNorm_le Ψ.norm_complexAntilinearPart_le v

/-- The complex-antilinear part, as a continuous real-linear map from the real-linear operators
to the complex-antilinear ones. Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` is the
same map, with values seen as real-linear operators. -/
noncomputable def complexAntilinearPartCLM : (E →L[ℝ] F) →L[ℝ] E →L⋆[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := complexAntilinearPart
      map_add' := complexAntilinearPart_add
      map_smul' := complexAntilinearPart_smul }
    1 fun Ψ ↦ by simpa using norm_complexAntilinearPart_le Ψ

@[simp]
theorem complexAntilinearPartCLM_apply (Ψ : E →L[ℝ] F) :
    complexAntilinearPartCLM Ψ = Ψ.complexAntilinearPart :=
  (rfl)

/-- The complex-antilinear part, as a continuous real-linear map into the complex-antilinear
operators, has operator norm at most `1`. -/
theorem norm_complexAntilinearPartCLM_le :
    ‖(complexAntilinearPartCLM : (E →L[ℝ] F) →L[ℝ] E →L⋆[ℂ] F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The inclusion of the continuous complex-antilinear operators into the continuous real-linear
ones, as a real-linear isometry: a complex-antilinear operator, being additive and continuous, is
real-linear (`AddMonoidHom.toRealLinearMap`), with the same operator norm. -/
noncomputable def restrictScalarsₛₗLI : (E →L⋆[ℂ] F) →ₗᵢ[ℝ] E →L[ℝ] F where
  toFun f := (f : E →+ F).toRealLinearMap f.continuous
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp]
theorem coe_restrictScalarsₛₗLI (f : E →L⋆[ℂ] F) : ⇑(restrictScalarsₛₗLI f) = f :=
  (rfl)

theorem restrictScalarsₛₗLI_apply (f : E →L⋆[ℂ] F) (v : E) : restrictScalarsₛₗLI f v = f v :=
  (rfl)

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` is
`ContinuousLinearMap.complexAntilinearPartCLM` followed by the inclusion of the
complex-antilinear operators into the real-linear ones. -/
theorem restrictScalarsₛₗLI_comp_complexAntilinearPartCLM :
    (restrictScalarsₛₗLI.toContinuousLinearMap.comp complexAntilinearPartCLM :
      (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F) = complexAntilinearPartL := by
  ext Ψ v
  simp

/-- A complex-antilinear operator is its own complex-antilinear part. -/
@[simp]
theorem complexAntilinearPart_restrictScalarsₛₗLI (f : E →L⋆[ℂ] F) :
    (restrictScalarsₛₗLI f).complexAntilinearPart = f := by
  ext v
  simp only [complexAntilinearPart_apply, coe_restrictScalarsₛₗLI, map_smulₛₗ, Complex.conj_I,
    neg_smul, smul_neg, smul_smul, Complex.I_mul_I, neg_neg]
  module


/-- The complex-linear part commutes with complex scalar multiplication. -/
@[simp]
theorem complexLinearPart_complex_smul (c : ℂ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexLinearPart = c • Ψ.complexLinearPart := by
  ext v
  simp only [complexLinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

/-- The complex-antilinear part commutes with complex scalar multiplication. -/
@[simp]
theorem complexAntilinearPart_complex_smul (c : ℂ) (Ψ : E →L[ℝ] F) :
    (c • Ψ).complexAntilinearPart = c • Ψ.complexAntilinearPart := by
  ext v
  simp only [complexAntilinearPart_apply, smul_apply]
  rw [smul_comm Complex.I c]
  module

section CompatibleReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, for real structures on `E` and `F`
compatible with the complex ones, has operator norm at most `1`. -/
theorem norm_complexAntilinearPartL_le :
    ‖(complexAntilinearPartL : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun Ψ ↦ ?_
  rw [one_mul]
  refine opNorm_le_bound _ (norm_nonneg Ψ) fun v ↦ ?_
  -- Multiplication by `I` preserves norms, so each of the two terms is at most `‖Ψ‖ * ‖v‖`.
  have h : ‖Ψ v + Complex.I • Ψ (Complex.I • v)‖ ≤ 2 * (‖Ψ‖ * ‖v‖) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul Complex.I, Complex.norm_I, one_mul, two_mul]
    gcongr
    · exact Ψ.le_opNorm v
    · simpa [norm_smul Complex.I] using Ψ.le_opNorm (Complex.I • v)
  rw [complexAntilinearPartL_apply_apply, norm_smul, norm_inv, Real.norm_two]
  linarith

end CompatibleReal

end ContinuousLinearMap

variable {G E F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : G → E →L[ℝ] F} {s : Set G} {n : WithTop ℕ∞}

/-- If a family of real-linear operators is `C^n` on `s`, so is the value of its complex-linear
part at any vector. -/
theorem ContDiffOn.complexLinearPart_apply (hf : ContDiffOn ℝ n f s) (v : E) :
    ContDiffOn ℝ n (fun x ↦ (f x).complexLinearPart v) s := by
  simp only [ContinuousLinearMap.complexLinearPart_apply]
  exact ((hf.clm_apply contDiffOn_const).sub
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

/-- If a family of real-linear operators is `C^n` on `s`, so is the value of its
complex-antilinear part at any vector. -/
theorem ContDiffOn.complexAntilinearPart_apply (hf : ContDiffOn ℝ n f s) (v : E) :
    ContDiffOn ℝ n (fun x ↦ (f x).complexAntilinearPart v) s := by
  simp only [ContinuousLinearMap.complexAntilinearPart_apply]
  exact ((hf.clm_apply contDiffOn_const).add
    ((hf.clm_apply contDiffOn_const).const_smul Complex.I)).const_smul _

end
