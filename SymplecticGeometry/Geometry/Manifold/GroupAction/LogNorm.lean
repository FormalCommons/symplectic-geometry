/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Lie.FundamentalVectorField
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField

/-!
# The logarithm of the norm along an orbit

Let a Lie group `K` act smoothly on a real normed space `V` by additive maps, let
`T : V →L[ℝ] F` be an injective continuous real-linear map into an inner product space `F` over
`𝕜 = ℝ` or `ℂ`, and let `v ≠ 0`. This file studies the function

`f g = log ‖T (g⁻¹ • v)‖²`

on `K`. The map `T` only supplies the norm: for `V = Fin (n + 1) → ℂ` it is the identification
`(PiLp.continuousLinearEquiv 2 ℝ _).symm` with `EuclideanSpace ℂ (Fin (n + 1))`, whose
coercion is `WithLp.toLp 2`, so that `‖T w‖` is the Hermitian norm of `w`.

## Main results

* `SymplecticGeometry.contMDiff_log_norm_sq_inv_smul`: `f` is `Cⁿ` when the group and the action
  are.
* `SymplecticGeometry.mfderiv_log_norm_sq_inv_smul_apply`: the differential of `f` at `g` sends
  `ĝ` to `-2 re ⟪T w, T (X_Z w)⟫ / ‖T w‖²`, where `w = g⁻¹ • v`, `Z` is the left trivialization
  of `ĝ` and `X_Z` is the fundamental vector field of `Z`.

The differential is that of `y ↦ log ‖T y‖²` at `w`, which is `y ↦ 2 re ⟪T w, T y⟫ / ‖T w‖²`,
composed with that of the inverse orbit map `g ↦ g⁻¹ • v`, which is
`TauCeti.mfderiv_inv_smul_apply`.
-/

public section

open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H K] [Group K]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [DistribMulAction K V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {T : V →L[ℝ] F}

/-- **Smoothness of the log-norm along an orbit.** For a `Cⁿ` action of a Lie group `K` on a
normed space `V` by additive maps, an injective continuous linear map `T` from `V` into an inner
product space over `𝕜`, and `v ≠ 0`, the function `g ↦ log ‖T (g⁻¹ • v)‖²` on `K` is `Cⁿ`. -/
theorem contMDiff_log_norm_sq_inv_smul (𝕜 : Type*) [RCLike 𝕜] [InnerProductSpace 𝕜 F]
    {n : WithTop ℕ∞} [LieGroup I n K] [ContMDiffSMul I 𝓘(ℝ, V) n K V] (hT : Function.Injective T)
    {v : V} (hv : v ≠ 0) :
    ContMDiff I 𝓘(ℝ) n fun g : K ↦ Real.log (‖T (g⁻¹ • v)‖ ^ 2) := by
  intro g
  have hw : T (g⁻¹ • v) ≠ 0 := fun h ↦
    (smul_ne_zero_iff_ne g⁻¹).2 hv (hT (h.trans (map_zero T).symm))
  have hlog : ContDiffAt ℝ n (fun y : V ↦ Real.log (‖T y‖ ^ 2)) (g⁻¹ • v) :=
    ((T.contDiff.norm_sq 𝕜).contDiffAt).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hw))
  exact hlog.contMDiffAt.comp g ((contMDiff_inv I n).smul contMDiff_const g)

/-- **The differential of the log-norm along an orbit.** For a `C¹` action of a Lie group `K` on
a normed space `V` by additive maps, an injective continuous linear map `T` from `V` into an
inner product space over `𝕜`, and `v ≠ 0`, the differential at `g` of
`g ↦ log ‖T (g⁻¹ • v)‖²` sends `ĝ` to `-2 re ⟪T w, T (X_Z w)⟫ / ‖T w‖²`, where `w = g⁻¹ • v`,
`Z` is the left trivialization of `ĝ` (its image under the differential at `g` of
`h ↦ g⁻¹ * h`) and `X_Z` is the fundamental vector field of `Z` on `V`. -/
theorem mfderiv_log_norm_sq_inv_smul_apply {𝕜 : Type*} [RCLike 𝕜] [InnerProductSpace 𝕜 F]
    [LieGroup I 1 K] [ContMDiffSMul I 𝓘(ℝ, V) 1 K V]
    (hT : Function.Injective T) {v : V} (hv : v ≠ 0) (g : K) (ĝ : TangentSpace I g) :
    mfderiv I 𝓘(ℝ) (fun h : K ↦ Real.log (‖T (h⁻¹ • v)‖ ^ 2)) g ĝ =
      (-2 * RCLike.re (inner 𝕜 (T (g⁻¹ • v))
          (T (TauCeti.fundamentalVectorField (I := I) (G := K) 𝓘(ℝ, V)
            (mfderiv I I (g⁻¹ * ·) g ĝ) (g⁻¹ • v)))) /
        ‖T (g⁻¹ • v)‖ ^ 2 : ℝ) := by
  have hw : ‖T (g⁻¹ • v)‖ ^ 2 ≠ 0 := pow_ne_zero 2 <| norm_ne_zero_iff.2 fun h ↦
    (smul_ne_zero_iff_ne g⁻¹).2 hv (hT (h.trans (map_zero T).symm))
  -- The derivative of `y ↦ log ‖T y‖² = log (re ⟪T y, T y⟫)` at `g⁻¹ • v`.
  have hlog := (RCLike.reCLM.hasFDerivAt.comp (g⁻¹ • v)
    (T.hasFDerivAt.inner 𝕜 T.hasFDerivAt)).log (by rwa [Function.comp_apply,
      RCLike.reCLM_apply, inner_self_eq_norm_sq])
  simp only [Function.comp_def, RCLike.reCLM_apply, inner_self_eq_norm_sq] at hlog
  have horbit : MDifferentiableAt I 𝓘(ℝ, V) (fun h : K ↦ h⁻¹ • v) g :=
    ((contMDiff_inv I 1).smul contMDiff_const g).mdifferentiableAt one_ne_zero
  have hcomp : (fun h : K ↦ Real.log (‖T (h⁻¹ • v)‖ ^ 2)) =
      (fun y : V ↦ Real.log (‖T y‖ ^ 2)) ∘ fun h : K ↦ h⁻¹ • v := rfl
  -- The identifications of the tangent spaces of `V` and `ℝ` with `V` and `ℝ` are the identity.
  have hV (u : TangentSpace 𝓘(ℝ, V) (g⁻¹ • v)) :
      NormedSpace.fromTangentSpace (𝕜 := ℝ) (g⁻¹ • v) u = (u : V) := rfl
  have hN (u : TangentSpace 𝓘(ℝ, V) (g⁻¹ • v)) : T (-u) = -T u := map_neg T u
  have hR (x u : ℝ) : (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm u = u := rfl
  have hL (y : V) : ((‖T (g⁻¹ • v)‖ ^ 2)⁻¹ • (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).comp
      ((fderivInnerCLM 𝕜 (T (g⁻¹ • v), T (g⁻¹ • v))).comp (T.prod T))) y =
        2 * RCLike.re (inner 𝕜 (T (g⁻¹ • v)) (T y)) / ‖T (g⁻¹ • v)‖ ^ 2 := by
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, RCLike.reCLM_apply, smul_eq_mul,
      map_add]
    rw [← inner_conj_symm (T (g⁻¹ • v)) (T y), RCLike.conj_re]
    ring
  rw [hcomp, mfderiv_comp_apply g hlog.differentiableAt.mdifferentiableAt horbit,
    mfderiv_eq_fderiv, hlog.fderiv, TauCeti.mfderiv_inv_smul_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hR]
  rw [hL, hV, hN, inner_neg_right, map_neg, mul_neg, neg_mul, neg_div]

end SymplecticGeometry

end
