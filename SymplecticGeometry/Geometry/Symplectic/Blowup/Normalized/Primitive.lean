/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Profile
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import SymplecticGeometry.Geometry.Symplectic.Complex.Radial

/-!
# Smooth compactly supported primitives of the model forms `ω̃_{l,ε t}`

Fix a weight `0 < l` and a radius `0 < c`. This file builds one two-form `θ` on the model
blowup `BlowupModel n` that is `π^* ω₀` off `L(c) = closedNbhd n c`, for `π` the blowdown, and
shows that, along any smooth family of collars `ε t` with `c < l + ε t`, the forms
`ω̃_{l,ε t} - θ = profileForm n l (ε t) - θ` have primitives `α t` that form a smooth family in
`t` and vanish off `L(l + ε t)`.

The form is `θ = ω̃_l - π^* ω_k`, for `ω̃_l = blowupForm n l` and `ω_k` the form of the potential
`k(|z|²)` on `E = ℂⁿ⁺¹`, where `k(s) = (1 - ρ(s)) l² log s` and `ρ` is a smooth bump function
(`ContDiffBump`) that is `1` near `0` and `0` on `[c², ∞)`. As `k` vanishes near `0`, it is smooth
on `ℝ`. Off the divisor, `θ - π^* ω₀` is the radial potential form of `ρ(s) l² log s`, which
vanishes for `|z| > c`.

The primitive `α t` is the pull-back by the blowdown of `(1/4) J^* d (g_t(|z|²))`, for
`g_t = k + q_t` and `q_t = profileCorrection l (blowupProfile l (ε t))`. Written as
`g_t'(|z|²) (1/4) J^* d |z|²`, its coefficient is jointly smooth in `(t, z)`, and it vanishes
for `|z| > l + ε t`, where `g_t' = 0`. This follows the proofs of `isSmoothFamily_profileForm`
and `exists_mextDeriv_eq_correctionForm_sub` in `Blowup/Profile.lean`.

## Main results

* `SymplecticGeometry.BlowupModel.exists_isSmoothFamily_mextDeriv_eq_profileForm_sub`: the form
  `θ` and, for every smooth family of collars, the primitives `α t`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1,
  proofs of Theorem 7.1.21 (v) and Theorem 7.1.23.
-/

public section

open Set TauCeti SmoothAlmostComplexStructure
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace SymplecticGeometry.BlowupModel

variable (n : ℕ)

section Potential

variable (l : ℝ) (ρ : ContDiffBump (0 : ℝ))

/-- The potential `k(s) = (1 - ρ(s)) l² log s`, for a bump function `ρ` around `0`: it vanishes
near `0`, and is `l² log s` for `s ≥ ρ.rOut`. -/
private noncomputable def logPotential (s : ℝ) : ℝ := (1 - ρ s) * (l ^ 2 * Real.log s)

private theorem contDiff_logPotential : ContDiff ℝ ∞ (logPotential l ρ) := by
  refine contDiff_iff_contDiffAt.2 fun s ↦ ?_
  rcases eq_or_ne s 0 with rfl | hs
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) ρ.rIn_pos] with x hx
    simp [logPotential, ρ.one_of_mem_closedBall hx]
  · exact (contDiffAt_const.sub ρ.contDiffAt).mul
      (contDiffAt_const.mul (Real.contDiffAt_log.2 hs))

variable {l ρ}

/-- For `s > ρ.rOut`, `k = l² log` near `s`, so `k'(s) = l² / s`. -/
private theorem deriv_logPotential_of_lt {s : ℝ} (hs : ρ.rOut < s) :
    deriv (logPotential l ρ) s = l ^ 2 / s := by
  have hs0 : 0 < s := ρ.rOut_pos.trans hs
  have he : logPotential l ρ =ᶠ[nhds s] fun x ↦ l ^ 2 * Real.log x := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 (by
      rw [ρ.tsupport_eq, Metric.mem_closedBall, Real.dist_0_eq_abs, not_le]
      exact hs.trans_le (le_abs_self _))] with x hx
    simp [logPotential, hx]
  rw [he.deriv_eq, deriv_const_mul _ (Real.differentiableAt_log hs0.ne'), Real.deriv_log,
    div_eq_mul_inv]

end Potential

/-- The form `ω_k` on `E` of the potential `k(|z|²)`, for `k = logPotential l ρ`. -/
private noncomputable def logForm (l : ℝ) (ρ : ContDiffBump (0 : ℝ)) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ) :=
  (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
    (SmoothForm.ofFunction (radialFunction (contDiff_logPotential l ρ)))

private theorem logForm_def (l : ℝ) (ρ : ContDiffBump (0 : ℝ)) :
    logForm n l ρ = (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
      (SmoothForm.ofFunction (radialFunction (contDiff_logPotential l ρ))) :=
  (rfl)

/-- Off `L(c)`, for `ρ.rOut ≤ c²`, the form `ω̃_l - π^* ω_k` is `π^* ω₀`: off the divisor, the
difference is the radial potential form of `ρ(s) l² log s`, which vanishes for `s > c²`. -/
private theorem blowupForm_sub_logForm_apply_eq {l c : ℝ} {ρ : ContDiffBump (0 : ℝ)}
    (hc : 0 < c) (hρ : ρ.rOut ≤ c ^ 2) {y : BlowupModel n} (hy : y ∉ closedNbhd n c) :
    (blowupForm n l - SmoothForm.mpullback blowdown
        ((contMDiff_blowdown ∞).restrictScalars' ℝ) (logForm n l ρ)).val y =
      (SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
        (ω₀E n)).val y := by
  have hk := contDiff_logPotential l ρ
  have hρl : ContDiffOn ℝ ∞ (fun s ↦ ρ s * (l ^ 2 * Real.log s)) (Ioi 0) :=
    ρ.contDiff.contDiffOn.mul
      (contDiffOn_const.mul (Real.contDiffOn_log.mono fun _ hs ↦ ne_of_gt hs))
  have hU : y ∈ offDivisorOpens n := mem_offDivisorOpens.2 fun h0 ↦
    hy (exceptionalDivisor_subset_closedNbhd hc h0)
  rw [← sub_eq_zero, ← Pi.sub_apply, ← Submodule.coe_sub]
  refine SmoothForm.apply_eq_of_mpullback_symm_mpullback_subtypeVal_apply_eq (τ := 0)
    (blowdownPuncturedDiffeomorph n) ⟨y, hU⟩ ?_
  have hθ : SmoothForm.mpullback (blowdownPuncturedDiffeomorph n).symm
      (blowdownPuncturedDiffeomorph n).symm.contMDiff
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (blowupForm n l - SmoothForm.mpullback blowdown
            ((contMDiff_blowdown ∞).restrictScalars' ℝ) (logForm n l ρ) -
          SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
            (ω₀E n))) =
      radialPotentialForm (Fin (n + 1)) _ hρl := by
    rw [map_sub, map_sub, map_sub, map_sub, mpullback_blowdownDiffeomorph_symm_blowupForm,
      SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_congr _ contMDiff_subtypeVal
        blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
      SmoothForm.mpullback_congr _ contMDiff_subtypeVal
        blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
      logForm_def, mpullback_subtypeVal_potentialForm_radialFunction, ω₀E_def,
      ← radialPotentialForm_id contDiffOn_id,
      radialPotentialForm_congr (contDiffOn_add_mul_log l)
        (contDiffOn_id.add (hρl.add hk.contDiffOn)) fun s _ ↦ by
          simp only [logPotential, id]; ring,
      radialPotentialForm_add contDiffOn_id (hρl.add hk.contDiffOn),
      radialPotentialForm_add hρl hk.contDiffOn]
    abel
  have hy' : c < ‖complexToRealEuclidean (Fin (n + 1)) y.blowdown‖ :=
    not_le.1 (mt mem_closedNbhd_iff.2 hy)
  have hx : ρ.rOut < ∑ i, ‖((blowdownPuncturedDiffeomorph n ⟨y, hU⟩ : puncturedSpace _) :
      Fin (n + 1) → ℂ) i‖ ^ 2 := by
    simp only [coe_blowdownPuncturedDiffeomorph_apply, ← norm_sq_complexToRealEuclidean]
    exact hρ.trans_lt (pow_lt_pow_left₀ hy' hc.le two_ne_zero)
  rw [hθ, map_zero, map_zero, radialPotentialForm_apply_eq_zero _ (c := 0) <| by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 (by
      rw [ρ.tsupport_eq, Metric.mem_closedBall, Real.dist_0_eq_abs, not_le]
      exact hx.trans_le (le_abs_self _))] with s hs
    simp [hs]]
  rw [Submodule.coe_zero, Pi.zero_apply]

/-- For a smooth family of collars `ε t` with `ρ.rOut < (l + ε t)²`, the forms
`ω̃_{l,ε t} - (ω̃_l - π^* ω_k)` are `d α t` for a smooth family `α t` of one-forms that vanish
off `L(l + ε t)`: the pull-back by the blowdown of `(1/4) J^* d (g_t(|z|²))`, for
`g_t = k + profileCorrection l (blowupProfile l (ε t))`, whose derivative vanishes on
`[(l + ε t)², ∞)`. -/
private theorem exists_isSmoothFamily_mextDeriv_eq_profileForm_sub_logForm {l : ℝ}
    {ρ : ContDiffBump (0 : ℝ)} (hl : 0 < l) {ε : unitInterval → ℝ}
    (hε : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ε) (hε0 : ∀ t, 0 < ε t) (hρε : ∀ t, ρ.rOut < (l + ε t) ^ 2) :
    ∃ α : unitInterval → SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) ℝ 1,
      IsSmoothFamily (𝓡∂ 1) α ∧
      (∀ t, mextDeriv (α t).val = (profileForm n l (ε t) - (blowupForm n l -
        SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
          (logForm n l ρ))).val) ∧
      ∀ t, ∀ y ∉ closedNbhd n (l + ε t), (α t).val y = 0 := by
  set J := ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)
  have hπ := (contMDiff_blowdown (n := n) ∞).restrictScalars' ℝ
  have hk := contDiff_logPotential l ρ
  have hb (t : unitInterval) := isBlowupProfile_blowupProfile hl (hε0 t)
  set s := radialFunction (ι := Fin (n + 1)) contDiff_id
  have hk' : ContDiff ℝ ∞ (deriv (logPotential l ρ)) := (contDiff_infty_iff_deriv.1 hk).2
  -- The coefficient `g_t'(|z|²)`, jointly smooth in the parameter and the point.
  have hV : IsOpen (({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε}) ×ˢ (univ : Set ℝ)) :=
    ((isOpen_lt continuous_const continuous_id).prod
      (isOpen_lt continuous_const continuous_id)).prod isOpen_univ
  have ha : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) 𝓘(ℝ) ∞
      fun p : unitInterval × (Fin (n + 1) → ℂ) ↦ deriv (logPotential l ρ) (s p.2) +
        (blowupProfile l (ε p.1) (s p.2) - s p.2 - l ^ 2) / s p.2 := by
    refine ((hk'.contMDiff.comp s.contMDiff).comp contMDiff_snd).add fun p ↦ ?_
    exact ((contDiffOn_blowupProfile_sub_sub_div.contDiffAt
      (hV.mem_nhds ⟨⟨hl, hε0 p.1⟩, mem_univ _⟩)).contMDiffAt).comp p
      (((contMDiff_const.prodMk_space (hε.comp contMDiff_fst)).prodMk_space
        (s.contMDiff.comp contMDiff_snd)) p)
  let a : unitInterval → C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := fun t ↦
    ⟨_, ha.comp (f := fun z ↦ (t, z)) (contMDiff_const.prodMk contMDiff_id)⟩
  have ha_apply (t : unitInterval) (z : Fin (n + 1) → ℂ) : a t z =
      deriv (logPotential l ρ) (s z) +
        (blowupProfile l (ε t) (s z) - s z - l ^ 2) / s z := (rfl)
  set ds := J.covectorComplexStructure (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0
    (SmoothForm.ofFunction s))
  refine ⟨fun t ↦ SmoothForm.mpullback blowdown hπ ((4 : ℝ)⁻¹ • SmoothForm.funSMulₗ (a t) ds),
    (((isSmoothFamily_const ds).funSMul_family a ha).smul _).mpullback _ _, fun t ↦ ?_,
    fun t y hy ↦ ?_⟩
  · -- The potential `g_t(|z|²)`, for `g_t = k + q_t`.
    have hg := hk.add (contDiff_profileCorrection (hb t))
    have hG : radialFunction hg = radialFunction hk + correctionPotential n l (ε t) :=
      ContMDiffMap.ext fun z ↦ by
        rw [ContMDiffMap.coe_add, Pi.add_apply, correctionPotential_apply n (hb t),
          radialFunction_apply, radialFunction_apply]
    have hd : J.covectorComplexStructure (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0
        (SmoothForm.ofFunction (radialFunction hg))) = SmoothForm.funSMulₗ (a t) ds :=
      covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt
        (g := fun x ↦ logPotential l ρ x + profileCorrection l (blowupProfile l (ε t)) x)
        (fun z ↦ by rw [radialFunction_apply, radialFunction_apply, id_eq]) fun z ↦ by
          rw [ha_apply]
          exact (hk.differentiable (by simp) _).hasDerivAt.add
            (hasDerivAt_profileCorrection (hb t) _)
    have h : mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (SmoothForm.mpullback blowdown hπ
        ((4 : ℝ)⁻¹ • SmoothForm.funSMulₗ (a t) ds)) =
        profileForm n l (ε t) - (blowupForm n l - SmoothForm.mpullback blowdown hπ
          (logForm n l ρ)) := by
      rw [SmoothForm.mextDerivₗ_mpullback, ← hd, map_smul, ← potentialForm_def, hG,
        SmoothForm.ofFunction_add, map_add, profileForm_def, correctionForm_def, logForm_def,
        map_add]
      abel
    exact (mextDerivₗ_apply _ _ _).symm.trans (congrArg Subtype.val h)
  · -- Off `L(l + ε t)`, the coefficient `g_t'(|z|²)` vanishes.
    have hy' : l + ε t < ‖complexToRealEuclidean (Fin (n + 1)) y.blowdown‖ :=
      not_le.1 (mt mem_closedNbhd_iff.2 hy)
    have hlε : 0 < l + ε t := add_pos hl (hε0 t)
    have hs : (l + ε t) ^ 2 < s y.blowdown := by
      rw [radialFunction_apply, id_eq]
      exact pow_lt_pow_left₀ hy' hlε.le two_ne_zero
    have hs0 : 0 < s y.blowdown := (by positivity : 0 < (l + ε t) ^ 2).trans hs
    have h0 : a t y.blowdown = 0 := by
      rw [ha_apply, deriv_logPotential_of_lt ((hρε t).trans hs),
        blowupProfile_of_ge hl (hε0 t) hs.le]
      field_simp
      ring
    ext v
    have h0y : ((a t).comp ⟨blowdown, hπ⟩) y = 0 := (ContMDiffMap.comp_apply _ _ _).trans h0
    simp [h0y]

/-- **Smooth compactly supported primitives of the model forms `ω̃_{l,ε t}`.** Fix `0 < l` and
`0 < c`. There is a two-form `θ` on the model blowup that is `π^* ω₀` off `L(c)`, for `π` the
blowdown, such that for every smooth family of collars `ε : unitInterval → ℝ` with `0 < ε t` and
`c < l + ε t`, the differences `ω̃_{l,ε t} - θ` are the exterior derivatives of a smooth family of
one-forms `α t`, each vanishing off `L(l + ε t)`. -/
theorem exists_isSmoothFamily_mextDeriv_eq_profileForm_sub {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    ∃ θ : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n),
      (∀ y ∉ closedNbhd n c, θ.val y =
        (SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
          (ω₀E n)).val y) ∧
      ∀ ε : unitInterval → ℝ, ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ε → (∀ t, 0 < ε t) →
        (∀ t, c < l + ε t) →
        ∃ α : unitInterval → SmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) ℝ 1,
          IsSmoothFamily (𝓡∂ 1) α ∧
          (∀ t, mextDeriv (α t).val = (profileForm n l (ε t) - θ).val) ∧
          ∀ t, ∀ y ∉ closedNbhd n (l + ε t), (α t).val y = 0 := by
  have hc2 : 0 < c ^ 2 := by positivity
  let ρ : ContDiffBump (0 : ℝ) := ⟨c ^ 2 / 2, c ^ 2, by positivity, by linarith⟩
  refine ⟨_, fun y hy ↦ blowupForm_sub_logForm_apply_eq n (ρ := ρ) hc le_rfl hy,
    fun ε hε hε0 hcε ↦ exists_isSmoothFamily_mextDeriv_eq_profileForm_sub_logForm n hl hε hε0
      fun t ↦ pow_lt_pow_left₀ (hcε t) hc.le two_ne_zero⟩

end SymplecticGeometry.BlowupModel

end
