/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.RCLike.OperatorNorm

/-!
# Iterated derivatives of partial derivatives

Write `∂ₐf = fun y ↦ fderiv ℝ f y a` for the partial derivative of `f` along `a`. This file
compares the derivatives of `f` with those of its partial derivatives.

## Main results

* `ContDiffAt.fderiv_comp_fderiv_apply`: for `f` of class `C²` at `x` and a continuous linear
  map `L`, the derivative along `a` of `y ↦ L (Df(y))` at `x` is `L (D(∂ₐf)(x))`. It follows from
  Tau Ceti's `TauCeti.fderiv_fderiv_apply_comm` (symmetry of the second derivative).
* `ContDiff.eLpNorm_iteratedFDeriv_fderiv_apply_le`: the `Lᵖ` norm of `Dⁿ(∂ₐf)` is at most
  `‖a‖` times that of `D^{n+1} f`, from Tau Ceti's pointwise
  `ContDiff.norm_iteratedFDeriv_fderiv_apply_le`.
* `ContDiff.norm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I` and
  `ContDiff.eLpNorm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I`: on the plane, pointwise and in
  `Lᵖ` for `1 ≤ p`, the derivative of order `n + 1` of `f` is at most the sum of the derivatives of
  order `n` of `∂₁f` and `∂_I f`. The pointwise bound comes from Tau Ceti's
  `ContDiff.iteratedFDeriv_fderiv_apply` and
  `ContinuousLinearMap.norm_apply_le_norm_one_add_norm_I`.
-/

public section

open MeasureTheory Complex ContinuousLinearMap
open scoped ENNReal

/-- The derivative at `x` of `y ↦ L (Df(y))`, for a continuous linear map `L` and `f` of class
`C²` at `x`, evaluated at `a`, is `L` applied to the derivative of the partial derivative `∂ₐf`. -/
theorem ContDiffAt.fderiv_comp_fderiv_apply {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (L : (E →L[ℝ] F) →L[ℝ] G)
    (a : E) :
    fderiv ℝ (fun y ↦ L (fderiv ℝ f y)) x a = L (fderiv ℝ (fun y ↦ fderiv ℝ f y a) x) := by
  -- By the symmetry of the second derivative, `D²f(x) a = D(∂ₐf)(x)`.
  have hsymm : fderiv ℝ (fderiv ℝ f) x a = fderiv ℝ (fun y ↦ fderiv ℝ f y a) x := by
    ext b
    rw [TauCeti.fderiv_fderiv_apply_comm hf (by simp) a b,
      (hf.hasFDerivAt_fderiv_apply le_rfl b).fderiv, flip_apply]
  rw [← hsymm, show (fun y ↦ L (fderiv ℝ f y)) = L ∘ fderiv ℝ f from rfl,
    (L.hasFDerivAt.comp x (hf.hasFDerivAt_fderiv le_rfl)).fderiv, comp_apply]

namespace ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- The `Lᵖ` norm of the derivative of order `n` of `∂ₐf` is at most `‖a‖` times that of the
derivative of order `n + 1` of `f`. -/
theorem eLpNorm_iteratedFDeriv_fderiv_apply_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {f : E → F}
    (hf : ContDiff ℝ (n + 1) f) (ν : Measure E) (a : E) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y a)) p ν ≤
      ENNReal.ofReal ‖a‖ * eLpNorm (iteratedFDeriv ℝ (n + 1) f) p ν :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((((hf.fderiv_right (m := n) le_rfl).clm_apply
      contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦
      (hf.norm_iteratedFDeriv_fderiv_apply_le (by simp) a x).trans_eq (mul_comm _ _)) p

variable {f : ℂ → F}

/-- Pointwise, the derivative of order `n + 1` of `f` on the plane is at most the sum of the
derivatives of order `n` of the partial derivatives `∂₁f` and `∂_I f`. -/
theorem norm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I (hf : ContDiff ℝ (n + 1) f) (x : ℂ) :
    ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z 1) x‖ +
      ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z I) x‖ := by
  rw [← norm_fderiv_iteratedFDeriv, hf.iteratedFDeriv_fderiv_apply (by simp),
    hf.iteratedFDeriv_fderiv_apply (by simp)]
  exact opNorm_le_bound _ (by positivity) fun w ↦ by
    simpa [RCLike.I_to_complex] using
      (fderiv ℝ (iteratedFDeriv ℝ n f) x).norm_apply_le_norm_one_add_norm_I (K := ℂ) w

/-- For `1 ≤ p`, the `Lᵖ` norm of the derivative of order `n + 1` of `f` on the plane is at most
the sum of the `Lᵖ` norms of the derivatives of order `n` of `∂₁f` and `∂_I f`. -/
theorem eLpNorm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I (hf : ContDiff ℝ (n + 1) f)
    (ν : Measure ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedFDeriv ℝ (n + 1) f) p ν ≤
      eLpNorm (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z 1)) p ν +
        eLpNorm (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z I)) p ν := by
  have hc (a : ℂ) : Continuous (iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z a)) :=
    ((hf.fderiv_right (m := n) le_rfl).clm_apply
      contDiff_const).continuous_iteratedFDeriv le_rfl
  calc eLpNorm (iteratedFDeriv ℝ (n + 1) f) p ν
      ≤ eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z 1) x‖ +
          ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z I) x‖) p ν :=
        eLpNorm_mono_real ((hf.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable)
          (hf.norm_iteratedFDeriv_succ_le_add_fderiv_apply_one_I)
    _ ≤ _ := by
        refine (eLpNorm_add_le (f := fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z 1) x‖)
          (g := fun x ↦ ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z I) x‖) hp).trans ?_
        rw [eLpNorm_norm, eLpNorm_norm]
        all_goals exact (hc _).aestronglyMeasurable

end ContDiff

end
