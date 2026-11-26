/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Profile
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars
import TauCeti.Analysis.Complex.LeviForm.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The area potential of the symplectic blowup

For `0 < l` and `0 < ε`, the area of a holomorphic curve `u` in `E = ℂⁿ⁺¹` for the standard form
`ω₀` and that of its lift to the model blowup for the form `ω̃_{l,ε}` (`profileForm`) differ, off
the zeros of `u`, by a quarter of the Laplacian of `φ ∘ u`, with
`φ(z) = -(l² log |z|² + q(|z|²))` for `q = blowupCorrection l ε` and the Euclidean norm `|z|`.
In the variable `s = |z|²` this is `s - g(s)`, where `g(s) = s + l² log s + q(s)` is the radial
potential of `ω̃_{l,ε}` off the divisor and `s` that of `ω₀`.

This file defines that potential and proves the two facts about `φ ∘ u` that the area formula
uses, before any form enters:

* `SymplecticGeometry.BlowupModel.areaPotential l ε`: the function `φ`.
* `SymplecticGeometry.BlowupModel.areaPotential_of_ge`: `φ` is constant on `|z|² ≥ (l + ε)²`,
  by `sq_mul_log_add_blowupCorrection_of_ge`; so `φ ∘ u` is locally constant near every point
  where `u` is continuous with `|u| > l + ε` (`areaPotential_comp_eventuallyEq`).
* `SymplecticGeometry.BlowupModel.exists_areaPotential_comp_eq_log_add`: at a zero `t₀` of order
  `k` of a curve `u`, written `u t = (t - t₀)ᵏ • g t` near `t₀` with `g` analytic and
  `g t₀ ≠ 0`, as Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` gives it, the function
  `φ ∘ u` is `-l² k log |t - t₀|²` plus a function smooth at `t₀`, off `t₀`.

It then proves the pointwise identity between the two densities at a point `t` with `u t ≠ 0`,
each density being the value of the form on the derivatives of the curve along `1` and `i`:

* `SymplecticGeometry.BlowupModel.laplacian_comp_sum_norm_sq_div_four`: for `u` complex `C²`
  at `t` and `ψ` of class `C²` at `s = |u t|²`, `Δ (ψ |u|²) (t) / 4` is
  `ψ'(s) |v|² + ψ''(s) |star (u t) ⬝ᵥ v|²`, with `v = u'(t)`. The orthonormal basis `{1}` of `ℂ`
  turns the Laplacian into four times the Levi form on `1` (Tau Ceti's
  `TauCeti.sum_re_leviForm_apply_self`), which the chain rules `TauCeti.leviForm_comp_apply`
  (along the holomorphic `u`) and `TauCeti.leviForm_scalar_comp_apply` (after `ψ`) compute from
  the Levi form and the differential of `|·|²` (`leviForm_norm_sq_complexToRealEuclidean`,
  `extendRCLike_fderiv_norm_sq_complexToRealEuclidean`).
* `SymplecticGeometry.BlowupModel.eval₂_ω₀E_mfderiv`: the density of `u^* ω₀` is `|v|²`.
* `SymplecticGeometry.BlowupModel.eval₂_profileForm_mfderiv_curveLift`: the density of the
  pull-back of `ω̃_{l,ε}` along `curveLift u` is `g'(s) |v|² + g''(s) |star (u t) ⬝ᵥ v|²`. Near
  `t` the lift is `u`, read in `E ∖ 0`, followed by the inverse of the blowdown off the divisor,
  along which `ω̃_{l,ε}` pulls back to the radial potential form of `g`
  (`mpullback_blowdownDiffeomorph_symm_profileForm`); its value on `(v, i v)` is
  `radialPotentialForm_apply_I_smul`. Only the derivative of the lift at `t` enters, so no form
  is pulled back along the lift itself, which is smooth only near `t`.
* `SymplecticGeometry.BlowupModel.eval₂_ω₀E_sub_eval₂_profileForm_curveLift`: for `u` analytic
  at `t`, the density of `u^* ω₀` minus that of the lift is `Δ (φ ∘ u) (t) / 4`, by the three
  results above for `ψ(s) = s - g(s)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], (7.1.7) and
  the proof of Proposition 7.1.13.
-/

public section

noncomputable section

open Filter Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry.BlowupModel

variable {n : ℕ} {l ε : ℝ}

/-- The area potential `φ(z) = -(l² log |z|² + q(|z|²))` on `ℂⁿ⁺¹`, for
`q = blowupCorrection l ε` and `|z|` the Euclidean norm. In the variable `s = |z|²` it is
`s - g(s)`, for `g(s) = s + l² log s + q(s)` the radial potential of `profileForm n l ε` off the
exceptional divisor; for `z = 0` the logarithm is Lean's `Real.log 0 = 0`. -/
def areaPotential (l ε : ℝ) (z : Fin (n + 1) → ℂ) : ℝ :=
  -(l ^ 2 * Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) +
    blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2))

theorem areaPotential_def (l ε : ℝ) (z : Fin (n + 1) → ℂ) :
    areaPotential l ε z =
      -(l ^ 2 * Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) +
        blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2)) :=
  (rfl)

/-- Far from the origin the area potential is constant: for `|z|² ≥ (l + ε)²` it takes the value
`-(l² log (l + ε)² + q((l + ε)²))`. -/
theorem areaPotential_of_ge (hl : 0 < l) (hε : 0 < ε) {z : Fin (n + 1) → ℂ}
    (hz : (l + ε) ^ 2 ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) :
    areaPotential l ε z =
      -(l ^ 2 * Real.log ((l + ε) ^ 2) + blowupCorrection l ε ((l + ε) ^ 2)) := by
  rw [areaPotential_def, sq_mul_log_add_blowupCorrection_of_ge hl hε hz]

/-- Along a map `u` continuous at `t` with `|u t| > l + ε`, the area potential is constant near
`t`. -/
theorem areaPotential_comp_eventuallyEq {X : Type*} [TopologicalSpace X]
    {u : X → Fin (n + 1) → ℂ} {t : X} (hl : 0 < l) (hε : 0 < ε) (hu : ContinuousAt u t)
    (ht : l + ε < ‖complexToRealEuclidean (Fin (n + 1)) (u t)‖) :
    areaPotential l ε ∘ u =ᶠ[𝓝 t] fun _ ↦ areaPotential l ε (u t) := by
  have hc : ContinuousAt (fun s ↦ ‖complexToRealEuclidean (Fin (n + 1)) (u s)‖) t :=
    ((complexToRealEuclidean (Fin (n + 1))).continuous.norm).continuousAt.comp hu
  have hge : ∀ {z : Fin (n + 1) → ℂ}, l + ε < ‖complexToRealEuclidean (Fin (n + 1)) z‖ →
      (l + ε) ^ 2 ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 :=
    fun h ↦ pow_le_pow_left₀ (by positivity) h.le 2
  filter_upwards [hc.eventually (lt_mem_nhds ht)] with s hs
  rw [Function.comp_apply, areaPotential_of_ge hl hε (hge hs), areaPotential_of_ge hl hε (hge ht)]

/-- At a zero of finite order: if `u t = (t - t₀) ^ k • g t` near `t₀`, with `g` analytic at `t₀`
and `g t₀ ≠ 0`, then off `t₀` and near it the area potential along `u` is
`-l² k log |t - t₀|²` plus a function that is smooth at `t₀`. -/
theorem exists_areaPotential_comp_eq_log_add {u g : ℂ → Fin (n + 1) → ℂ} {t₀ : ℂ} {k : ℕ}
    (hl : 0 < l) (hε : 0 < ε) (hg : AnalyticAt ℂ g t₀) (hg0 : g t₀ ≠ 0)
    (hug : ∀ᶠ t in 𝓝 t₀, u t = (t - t₀) ^ k • g t) :
    ∃ h : ℂ → ℝ, ContDiffAt ℝ ∞ h t₀ ∧ ∀ᶠ t in 𝓝[≠] t₀,
      areaPotential l ε (u t) = -(l ^ 2 * k * Real.log (‖t - t₀‖ ^ 2)) + h t := by
  set N : (Fin (n + 1) → ℂ) → ℝ := fun z ↦ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2
  have hN : ContDiff ℝ ∞ N := contDiff_norm_sq_complexToRealEuclidean
  have hN0 : ∀ {z}, z ≠ 0 → N z ≠ 0 := fun hz ↦
    pow_ne_zero 2 (norm_ne_zero_iff.2 ((complexToRealEuclidean _).map_ne_zero_iff.2 hz))
  have hua : AnalyticAt ℂ u t₀ :=
    (((analyticAt_id.sub analyticAt_const).pow k).smul hg).congr (hug.mono fun _ h ↦ h.symm)
  have hsmooth : ContDiffAt ℝ ∞
      (fun t ↦ -(l ^ 2 * Real.log (N (g t)) + blowupCorrection l ε (N (u t)))) t₀ :=
    ((contDiffAt_const.mul ((hN.contDiffAt.comp t₀ (hg.contDiffAt.restrict_scalars ℝ)).log
      (hN0 hg0))).add ((contDiff_blowupCorrection hl hε).contDiffAt.comp t₀
        (hN.contDiffAt.comp t₀ (hua.contDiffAt.restrict_scalars ℝ)))).neg
  refine ⟨_, hsmooth, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hug, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0)] with t ht htne hgt
  have hN_smul : N (u t) = (‖t - t₀‖ ^ 2) ^ k * N (g t) := by
    simp only [N, ht, norm_complexToRealEuclidean_smul, norm_pow, mul_pow, ← pow_mul]
    ring
  have ht0 : ‖t - t₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 htne))
  have hlog : Real.log (N (u t)) = k * Real.log (‖t - t₀‖ ^ 2) + Real.log (N (g t)) := by
    rw [hN_smul, Real.log_mul (pow_ne_zero k ht0) (hN0 hgt), Real.log_pow]
  calc areaPotential l ε (u t)
      = -(l ^ 2 * Real.log (N (u t)) + blowupCorrection l ε (N (u t))) :=
        areaPotential_def l ε (u t)
    _ = _ := by rw [hlog]; ring


/-! ### The two area densities along a curve -/

section Density

open scoped Laplacian ComplexConjugate Manifold TauCeti.ComplexManifold
open TauCeti.Manifold

/-- The Laplacian of a radial function along a holomorphic curve. For `u : ℂ → ℂⁿ⁺¹` complex `C²`
at `t` and `ψ : ℝ → ℝ` of class `C²` at `s = |u t|²`, a quarter of the Laplacian of
`t ↦ ψ |u t|²` at `t` is `ψ'(s) |v|² + ψ''(s) |star (u t) ⬝ᵥ v|²`, for `v = u'(t)`. -/
theorem laplacian_comp_sum_norm_sq_div_four {ψ : ℝ → ℝ} {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (∑ i, ‖u t i‖ ^ 2)) (hu : ContDiffAt ℂ 2 u t) :
    Δ (fun s ↦ ψ (∑ i, ‖u s i‖ ^ 2)) t / 4 =
      deriv ψ (∑ i, ‖u t i‖ ^ 2) * ∑ i, ‖deriv u t i‖ ^ 2 +
        deriv (deriv ψ) (∑ i, ‖u t i‖ ^ 2) * Complex.normSq (star (u t) ⬝ᵥ deriv u t) := by
  set N : (Fin (n + 1) → ℂ) → ℝ := fun y ↦ ‖complexToRealEuclidean (Fin (n + 1)) y‖ ^ 2
  have hN : ContDiffAt ℝ 2 N (u t) := contDiff_norm_sq_complexToRealEuclidean.contDiffAt
  have hs : N (u t) = ∑ i, ‖u t i‖ ^ 2 := norm_sq_complexToRealEuclidean _
  have hcomp : (fun s ↦ ψ (∑ i, ‖u s i‖ ^ 2)) = (ψ ∘ N) ∘ u :=
    funext fun s ↦ by simp only [Function.comp_apply, N, norm_sq_complexToRealEuclidean]
  have h2 : iteratedDeriv 2 ψ = deriv (deriv ψ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [← hs] at hψ
  -- `{1}` is an orthonormal basis of `ℂ`, so the Laplacian is four times the Levi form on `1`.
  rw [← sum_re_leviForm_apply_self (OrthonormalBasis.singleton (Fin 1) ℂ), hcomp]
  simp only [Finset.univ_unique, Finset.sum_singleton, OrthonormalBasis.singleton_apply]
  rw [leviForm_comp_apply (hψ.comp _ hN) hu, leviForm_scalar_comp_apply hψ hN,
    leviForm_norm_sq_complexToRealEuclidean, extendRCLike_fderiv_norm_sq_complexToRealEuclidean,
    h2, hs]
  simp only [fderiv_apply_one_eq_deriv]
  have h4 : conj (2 * star (u t) ⬝ᵥ deriv u t) * (2 * star (u t) ⬝ᵥ deriv u t) =
      4 * (Complex.normSq (star (u t) ⬝ᵥ deriv u t) : ℂ) := by
    rw [map_mul, Complex.conj_ofNat, Complex.normSq_eq_conj_mul_self]
    ring
  rw [h4, inv_mul_cancel_left₀ (by norm_num), Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Matrix.re_star_dotProduct_self, Complex.ofReal_re]

/-- The density of `u^* ω₀` at `t` for a curve `u : ℂ → ℂⁿ⁺¹` complex differentiable at `t`: the
value of `ω₀` on the derivatives of `u` along `1` and `i` is `|u'(t)|²`. -/
theorem eval₂_ω₀E_mfderiv {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ} (hu : DifferentiableAt ℂ u t) :
    (ω₀E n).eval₂ (u t) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t Complex.I) = ∑ i, ‖deriv u t i‖ ^ 2 := by
  have hm (c : TangentSpace 𝓘(ℝ, ℂ) t) : mvfderiv 𝓘(ℝ, ℂ) u t c = fderiv ℝ u t c := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact DFunLike.congr_fun (hu.restrictScalars ℝ).hasFDerivAt.hasMFDerivAt.mfderiv c
  rw [ω₀E_def]
  refine (SymplecticForm.eval₂_constSmooth_mfderiv_eq _ u t (1 : ℂ) Complex.I).trans ?_
  rw [hm (1 : ℂ), hm Complex.I, hu.fderiv_restrictScalars_eq_smul_deriv ℝ,
    hu.fderiv_restrictScalars_eq_smul_deriv ℝ, one_smul]
  simp [Complex.sq_norm, Complex.normSq_apply]

/-- The density of `(curveLift u)^* ω̃_{l,ε}` at a point `t` off the zeros of `u`, for `0 < l`,
`0 < ε` and `u : ℂ → ℂⁿ⁺¹` complex differentiable at `t` with `u t ≠ 0`: the value of
`profileForm n l ε` on the derivatives of the lift along `1` and `i` is
`g'(s) |v|² + g''(s) |star (u t) ⬝ᵥ v|²`, for `v = u'(t)`, `s = |u t|²` and the radial potential
`g(s) = s + l² log s + q(s)` of `ω̃_{l,ε}` off the exceptional divisor. -/
theorem eval₂_profileForm_mfderiv_curveLift (hl : 0 < l) (hε : 0 < ε)
    {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ} (hu : DifferentiableAt ℂ u t) (h0 : u t ≠ 0) :
    (profileForm n l ε).eval₂ (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t Complex.I) =
      deriv (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s) (∑ i, ‖u t i‖ ^ 2) *
          ∑ i, ‖deriv u t i‖ ^ 2 +
        deriv (deriv fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s)
            (∑ i, ‖u t i‖ ^ 2) * Complex.normSq (star (u t) ⬝ᵥ deriv u t) := by
  -- Near `t`, the curve `u` as a curve `ũ` in `E ∖ 0`.
  set ũ : ℂ → puncturedSpace (Fin (n + 1) → ℂ) := fun s ↦
    if h : u s = 0 then ⟨u t, mem_puncturedSpace.2 h0⟩ else ⟨u s, mem_puncturedSpace.2 h⟩
  have hne : ∀ᶠ s in 𝓝 t, u s ≠ 0 := hu.continuousAt.eventually_ne h0
  have hev : Subtype.val ∘ ũ =ᶠ[𝓝 t] u := by
    filter_upwards [hne] with s hs
    simp [ũ, hs]
  have hũt : (ũ t : Fin (n + 1) → ℂ) = u t := hev.self_of_nhds
  have hũd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t :=
    mdifferentiableAt_subtype_val_comp_iff.1
      ((hu.restrictScalars ℝ).mdifferentiableAt.congr_of_eventuallyEq hev)
  -- Near `t`, the lift is `ũ` followed by the inverse of the blowdown off the divisor.
  set Ψ : puncturedSpace (Fin (n + 1) → ℂ) → BlowupModel n :=
    Subtype.val ∘ (blowdownPuncturedDiffeomorph n).symm
  have hΨ : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ Ψ :=
    contMDiff_subtypeVal.comp (blowdownPuncturedDiffeomorph n).symm.contMDiff
  have hlift : curveLift u =ᶠ[𝓝 t] Ψ ∘ ũ := by
    filter_upwards [hne] with s hs
    simp [Ψ, ũ, hs, curveLift_of_ne_zero hs]
  have hd (c : ℂ) :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t c =
        mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Ψ (ũ t) (c • deriv u t) := by
    have h₁ := (((hΨ.mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      hũd.hasMFDerivAt).congr_of_eventuallyEq_abuse hlift).mfderiv
    have h₂ : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t c = c • deriv u t :=
      ((mfderiv_subtype_val_comp_apply c).symm.trans (DFunLike.congr_fun
        ((hu.restrictScalars ℝ).hasFDerivAt.hasMFDerivAt
          |>.congr_of_eventuallyEq_abuse hev).mfderiv c)).trans
        (hu.fderiv_restrictScalars_eq_smul_deriv ℝ c)
    -- The tangent spaces at `curveLift u t` and at `Ψ (ũ t)` are both `E`.
    exact (DFunLike.congr_fun h₁ c).trans ((ContinuousLinearMap.comp_apply
      (mfderiv 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) Ψ (ũ t))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ũ t) c).trans (congrArg _ h₂))
  -- Off the divisor, read `ω̃_{l,ε}` through the blowdown as a radial potential form.
  have key := SmoothForm.eval₂_mpullback Ψ hΨ (profileForm n l ε) (ũ t)
    (deriv u t : Fin (n + 1) → ℂ) (Complex.I • deriv u t : Fin (n + 1) → ℂ)
  rw [← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).symm.contMDiff
    contMDiff_subtypeVal, mpullback_blowdownDiffeomorph_symm_profileForm n hl hε,
    radialPotentialForm_apply_I_smul, hũt] at key
  rw [hd (1 : ℂ), hd Complex.I, one_smul, hlift.self_of_nhds]
  exact key.symm

/-- **The two area densities along a curve differ by a quarter Laplacian.** For `0 < l`, `0 < ε`
and `u : ℂ → ℂⁿ⁺¹` analytic at `t` with `u t ≠ 0`, the density at `t` of `u^* ω₀` minus that of
`(curveLift u)^* ω̃_{l,ε}`, each read on the derivatives along `1` and `i`, is
`Δ (φ ∘ u) (t) / 4`, for the area potential `φ = areaPotential l ε` and Mathlib's Laplacian `Δ`. -/
theorem eval₂_ω₀E_sub_eval₂_profileForm_curveLift (hl : 0 < l) (hε : 0 < ε)
    {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ} (hu : AnalyticAt ℂ u t) (h0 : u t ≠ 0) :
    (ω₀E n).eval₂ (u t) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t Complex.I) -
      (profileForm n l ε).eval₂ (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t Complex.I) =
      Δ (areaPotential l ε ∘ u) t / 4 := by
  set g : ℝ → ℝ := fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s
  set x := ∑ i, ‖u t i‖ ^ 2
  have hx : 0 < x := by
    simpa only [x, norm_sq_complexToRealEuclidean] using
      norm_sq_complexToRealEuclidean_pos (⟨u t, mem_puncturedSpace.2 h0⟩ :
        puncturedSpace (Fin (n + 1) → ℂ))
  -- In the variable `s = |z|²` the area potential is `s - g(s)`.
  have hφ : areaPotential l ε ∘ u = fun s ↦ (fun r ↦ r - g r) (∑ i, ‖u s i‖ ^ 2) :=
    funext fun s ↦ by
      simp only [Function.comp_apply, areaPotential_def, norm_sq_complexToRealEuclidean, g]
      ring
  have hg : ContDiffOn ℝ ∞ g (Set.Ioi 0) := contDiffOn_add_mul_log_add_blowupCorrection hl hε
  have hgd : ∀ r ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ g r ∧ DifferentiableAt ℝ (deriv g) r :=
    fun r hr ↦ ⟨(hg.contDiffAt (Ioi_mem_nhds hr)).differentiableAt (by simp),
      ((hg.deriv_of_isOpen isOpen_Ioi (m := 1) (by simp)).contDiffAt
        (Ioi_mem_nhds hr)).differentiableAt (by simp)⟩
  have h1 : deriv (fun r ↦ r - g r) =ᶠ[𝓝 x] fun r ↦ 1 - deriv g r :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun r hr ↦ by
      rw [deriv_fun_sub differentiableAt_fun_id (hgd r hr).1, deriv_id'']
  rw [eval₂_ω₀E_mfderiv hu.differentiableAt,
    eval₂_profileForm_mfderiv_curveLift hl hε hu.differentiableAt h0, hφ,
    laplacian_comp_sum_norm_sq_div_four (ψ := fun r ↦ r - g r)
      (contDiffAt_id.sub ((hg.contDiffAt (Ioi_mem_nhds hx)).of_le (by simp))) hu.contDiffAt,
    h1.deriv_eq, h1.eq_of_nhds, deriv_fun_sub (differentiableAt_const _) (hgd x hx).2,
    deriv_const]
  ring

end Density
end SymplecticGeometry.BlowupModel

end
