/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Complex-linear and complex-antilinear parts of an operator: bounds, scalars, smoothness

For a continuous real-linear operator `Ψ` between complex normed spaces, Tau Ceti's
`ContinuousLinearMap.complexLinearPart` and `ContinuousLinearMap.complexAntilinearPart` both have
operator norm at most `‖Ψ‖` (`ContinuousLinearMap.norm_complexLinearPart_le`,
`ContinuousLinearMap.norm_complexAntilinearPart_le`), with pointwise forms.

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

/-- Pointwise form of `ContinuousLinearMap.norm_complexLinearPart_le`. -/
theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexLinearPart.le_of_opNorm_le Ψ.norm_complexLinearPart_le v

/-- Pointwise form of `ContinuousLinearMap.norm_complexAntilinearPart_le`. -/
theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ :=
  Ψ.complexAntilinearPart.le_of_opNorm_le Ψ.norm_complexAntilinearPart_le v


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
