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
import TauCeti.Analysis.Normed.Module.RCLike.Basic

/-!
# Complex-linear and complex-antilinear parts of an operator: bounds, scalars, smoothness

For a continuous real-linear operator `Ψ` between complex normed spaces, whose real structures may
be given separately from the complex ones as long as they are compatible with them, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms. Seen as a
real-linear operator by Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL`, the
complex-antilinear part keeps its operator norm
(`ContinuousLinearMap.norm_complexAntilinearPartL_apply`), so `complexAntilinearPartL` itself has
operator norm at most `1` (`ContinuousLinearMap.norm_complexAntilinearPartL_le`). The bound on
the complex-antilinear part also makes it a continuous real-linear map into the
complex-antilinear operators, `ContinuousLinearMap.complexAntilinearPartCLM`, again of operator
norm at most `1` (`ContinuousLinearMap.norm_complexAntilinearPartCLM_le`).

For complex normed spaces with the real structure they restrict to, a continuous
complex-antilinear operator is also a continuous real-linear one, by Mathlib's
`AddMonoidHom.toRealLinearMap`, with the same operator norm. This gives a real-linear isometry
`ContinuousLinearMap.restrictScalarsₛₗLI` from the complex-antilinear operators into the
real-linear ones. Tau Ceti's
`ContinuousLinearMap.complexAntilinearPartL` is `ContinuousLinearMap.complexAntilinearPartCLM`
followed by this isometry
(`ContinuousLinearMap.restrictScalarsₛₗLI_comp_complexAntilinearPartCLM`), and a
complex-antilinear operator is its own complex-antilinear part
(`ContinuousLinearMap.complexAntilinearPart_restrictScalarsₛₗLI`).

Each value of either part is half the sum of two vectors of norm at most `‖Ψ‖ * ‖v‖`, so the
pointwise bounds follow from Tau Ceti's `TauCeti.norm_two_inv_smul_add_le`.

Both parts commute with complex scalars (`ContinuousLinearMap.complexLinearPart_complex_smul`,
`ContinuousLinearMap.complexAntilinearPart_complex_smul`), next to Tau Ceti's versions for real
scalars, and their values at a fixed vector are as smooth as the operator
(`ContDiffOn.complexLinearPart_apply`, `ContDiffOn.complexAntilinearPart_apply`).
-/

public section

namespace ContinuousLinearMap

section CompatibleReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- The value of the complex-linear part of a real-linear operator `Ψ` at `v` has norm at most
`‖Ψ‖ * ‖v‖`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  rw [complexLinearPart_apply, sub_eq_add_neg]
  exact TauCeti.norm_two_inv_smul_add_le (Ψ.le_opNorm v)
    (by simpa [norm_smul] using Ψ.le_opNorm (Complex.I • v))

/-- The value of the complex-antilinear part of a real-linear operator `Ψ` at `v` has norm at
most `‖Ψ‖ * ‖v‖`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  rw [complexAntilinearPart_apply]
  exact TauCeti.norm_two_inv_smul_add_le (Ψ.le_opNorm v)
    (by simpa [norm_smul] using Ψ.le_opNorm (Complex.I • v))

/-- The complex-linear part of a real-linear operator has norm at most that of the operator. -/
theorem norm_complexLinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexLinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) Ψ.norm_complexLinearPart_apply_le

/-- The complex-antilinear part of a real-linear operator has norm at most that of the
operator. -/
theorem norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) :
    ‖Ψ.complexAntilinearPart‖ ≤ ‖Ψ‖ :=
  opNorm_le_bound _ (norm_nonneg Ψ) Ψ.norm_complexAntilinearPart_apply_le

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

/-- Tau Ceti's `ContinuousLinearMap.complexAntilinearPartL` has operator norm at most `1`. -/
theorem norm_complexAntilinearPartL_le :
    ‖(complexAntilinearPartL : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F)‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun Ψ ↦ by
    rw [one_mul, norm_complexAntilinearPartL_apply]
    exact norm_complexAntilinearPart_le Ψ

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

end CompatibleReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

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
