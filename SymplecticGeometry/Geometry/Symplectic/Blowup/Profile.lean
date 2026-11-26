/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.SmoothFamily.Basic
public import SymplecticGeometry.Geometry.Symplectic.Blowup.Model
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive

/-!
# The profiles `h_{λ,ε}` of the symplectic blowup

For `0 < l` and `0 < ε`, the blowup of weight `l` with gluing collar `ε` is read through a radial
profile in the variable `s = |z|²`: a smooth function `h : ℝ → ℝ` with positive derivative that is
`l² + s` for `s ≤ ε²` (the profile of the radial map `F_l` of the model) and `s` for
`s ≥ (l + ε)²` (the identity). This file fixes such a profile, `blowupProfile l ε`, which depends
smoothly on `(l, ε)` as well.

The construction follows McDuff–Salamon, Lemma A.3.1: the derivative of `h` is `1 - β` for a
smoothed step `β` of height `l / (l + ε) < 1`, supported in `[ε², (l + ε)²]` and of integral
`l²`. The step is the difference of two translates of the smooth ramp `t ↦ smoothedMax 1 t 0`,
rescaled by `w = l ε / 2`, which is `0` for `t ≤ -1` and `t` for `t ≥ 1`; so `h` is given by an
explicit formula, without an integral, and its smoothness in `(l, ε, s)` is that of
`smoothedMax`.

## Main definitions and results

* `SymplecticGeometry.BlowupModel.blowupProfile l ε s`: the profile `h_{l,ε}(s)`.
* `SymplecticGeometry.BlowupModel.contDiffOn_blowupProfile`: it is smooth in `(l, ε, s)` on
  `{0 < l} ×ˢ {0 < ε} ×ˢ univ`.
* `SymplecticGeometry.BlowupModel.blowupProfile_of_le`: `h s = l ^ 2 + s` for `s ≤ ε ^ 2`, and
  `SymplecticGeometry.BlowupModel.blowupProfile_of_ge`: `h s = s` for `(l + ε) ^ 2 ≤ s`.
* `SymplecticGeometry.BlowupModel.hasDerivAt_blowupProfile`: the derivative in `s`, which lies
  in `[ε / (l + ε), 1]` (`deriv_blowupProfile_mem`, `deriv_blowupProfile_pos`,
  `deriv_blowupProfile_le_one`); so `h` is
  strictly increasing, `s ≤ h s ≤ s + l ^ 2`, and `h` is positive on `[0, ∞)`
  (`blowupProfile_pos`), as `radialMap` asks on `Ioi 0`.
* `SymplecticGeometry.BlowupModel.blowupCorrection l ε s`: the correction
  `q(s) = ∫₀ˢ (h(u) - u - l²) / u du`, smooth in `(l, ε, s)` (`contDiffOn_blowupCorrection`), zero
  for `s ≤ ε ^ 2` (`blowupCorrection_of_le`), equal to `-l² log s` plus a constant for
  `s ≥ (l + ε) ^ 2` (`sq_mul_log_add_blowupCorrection_of_ge`), with
  `s q'(s) = h(s) - s - l²` (`mul_deriv_blowupCorrection`).

The smoothness of `q` in the parameters is that of a parametric primitive, Tau Ceti's
`Convex.contDiffOn_parametric_primitive`: the integrand is smooth
(`contDiffOn_blowupProfile_sub_sub_div`) since it vanishes for
`u ≤ ε ^ 2`, so near `u = 0`.

The second half of the file defines the forms `ω̃_{l,ε}` on the model blowup `L = BlowupModel n`,
with blowdown `π : L → E = ℂⁿ⁺¹`, the exceptional divisor `Z` and the neighbourhoods
`L(ε) = closedNbhd n ε` of `Model.lean`:

* `SymplecticGeometry.BlowupModel.correctionPotential n l ε`: the smooth function `z ↦ q(|z|²)`
  on `E`, for the Euclidean norm `|z|` (`correctionPotential_apply`; it is `0` unless `0 < l`
  and `0 < ε`), and `SymplecticGeometry.BlowupModel.correctionForm n l ε`: its form
  `ω_q = (1/4) d (J* d (q(|z|²)))` on all of `E`, the `potentialForm` of that function. It vanishes
  on the closed ball of radius `ε` (`correctionForm_apply_eq_zero`), since there the form of a
  composite, `mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`, only
  involves `q'(|z|²)` and `q''(|z|²)` (`deriv_blowupCorrection_of_le`,
  `deriv_deriv_blowupCorrection_of_le`); on `E ∖ 0` it is `radialPotentialForm` of `q`
  (`mpullback_subtypeVal_correctionForm`, by `mpullback_potentialForm` along the
  holomorphic inclusion).
* `SymplecticGeometry.BlowupModel.profileForm n l ε`: the form `ω̃_{l,ε} = ω̃_l + π^* ω_q`, defined
  on all of `L` at once, so that no form is glued across `Z`.
* `SymplecticGeometry.BlowupModel.profileForm_eq_blowupForm_on`: it is `ω̃_l` at the points of
  `L(ε)`.
* `SymplecticGeometry.BlowupModel.profileForm_eq_on_compl`: for `0 < l` and `0 < ε` it is
  `π^* ω₀` at the points off `L(l + ε)`. Off `Z`, read on `E ∖ 0` through the blowdown, `ω̃_l` is
  `radialPotentialForm` of `s + l² log s` (`mpullback_blowdownDiffeomorph_symm_blowupForm`), so
  `ω̃_{l,ε}` is that of `s + l² log s + q(s)`, whose derivatives are those of `s` for
  `s > (l + ε)²` (`sq_mul_log_add_blowupCorrection_of_ge`); and `π^* ω₀` is that of `s`
  (`radialPotentialForm_id`). That reading of `ω̃_{l,ε}` off `Z` is
  `mpullback_blowdownDiffeomorph_symm_profileForm`.
* `SymplecticGeometry.BlowupModel.mpullback_radialMap_profileForm`: for `0 < l` and `0 < ε`,
  off `Z` the form `ω̃_{l,ε}` is the pull-back of `ω₀` along `F_{l,ε} ∘ π`, where `F_{l,ε}` is
  `radialMap` of the profile `h = blowupProfile l ε`: by `mpullback_radialMap_stdForm`, since
  `s + l² log s + q(s)` has derivative `h(s) / s` (`deriv_add_mul_log_add_blowupCorrection`).
  This follows `mpullback_radialMap_blowdown` of `Model.lean`, the case `h(s) = s + l²`.
* `SymplecticGeometry.BlowupModel.isKahler_profileForm`: for `0 < l` and `0 < ε`, `ω̃_{l,ε}` is
  Kähler for the complex structure of `L`. It is closed (`isClosed_profileForm`), and its
  compatibility is checked on two open sets that cover `L`
  (`TauCeti.SmoothTwoForm.compatible_of_compatible_restrictOpen`): on `openNbhd n ε` it is `ω̃_l`,
  compatible by `isKahler_blowupForm`, and off `Z` it is the pull-back along the holomorphic
  blowdown (`isPseudoholomorphic_blowdownPuncturedDiffeomorph`) of `F_{l,ε}^* ω₀`, which
  `isKahler_mpullback_radialMap` makes Kähler, as `h > 0` and `h' > 0`.
* `SymplecticGeometry.BlowupModel.isSmoothFamily_profileForm`: for smooth positive `l ε` on
  `unitInterval`, `t ↦ ω̃_{l t, ε t}` is a smooth family of forms. Here `ω̃_l` is affine in `l²`,
  and for positive parameters the correction form is `(1/4) d (q'(|z|²) J* d|z|²)`
  (`covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`), with `q'(s)` the
  integrand of `q`, smooth in `(l, ε, s)`; the coefficient is jointly smooth in the parameter
  and the point (`IsSmoothFamily.funSMul_family`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1 and
  Lemma A.3.1.
-/

public section

noncomputable section

open Set

namespace SymplecticGeometry.BlowupModel

/-- The profile `h_{l,ε}` of the blowup of weight `l` with collar `ε`, in the variable
`s = |z|²`:
`s + l² - (l / (l + ε)) w (ρ((s - ε²) / w - 1) - ρ((s - (l + ε)²) / w + 1))`, where
`w = l ε / 2` and `ρ t = smoothedMax 1 t 0` is a smooth ramp, `0` for `t ≤ -1` and `t` for
`t ≥ 1`. For `0 < l` and `0 < ε` it is `l² + s` for `s ≤ ε²` (`blowupProfile_of_le`), `s` for
`s ≥ (l + ε)²` (`blowupProfile_of_ge`), and has positive derivative (`deriv_blowupProfile_pos`). -/
def blowupProfile (l ε s : ℝ) : ℝ :=
  s + l ^ 2 - l / (l + ε) * (l * ε / 2) *
    (smoothedMax 1 ((s - ε ^ 2) / (l * ε / 2) - 1) 0 -
      smoothedMax 1 ((s - (l + ε) ^ 2) / (l * ε / 2) + 1) 0)

theorem blowupProfile_def (l ε s : ℝ) :
    blowupProfile l ε s = s + l ^ 2 - l / (l + ε) * (l * ε / 2) *
      (smoothedMax 1 ((s - ε ^ 2) / (l * ε / 2) - 1) 0 -
        smoothedMax 1 ((s - (l + ε) ^ 2) / (l * ε / 2) + 1) 0) :=
  (rfl)

variable {l ε : ℝ}

/-- The profile `blowupProfile l ε s` is a smooth function of `(l, ε, s)` for `0 < l`,
`0 < ε`. -/
theorem contDiffOn_blowupProfile {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ × ℝ ↦ blowupProfile p.1 p.2.1 p.2.2)
      ({l | 0 < l} ×ˢ {ε | 0 < ε} ×ˢ univ) := by
  have hρ : ContDiff ℝ n fun t : ℝ ↦ smoothedMax 1 t 0 :=
    (contDiff_smoothedMax 1).comp (contDiff_id.prodMk contDiff_const)
  rintro p ⟨hl, hε, -⟩
  simp only [mem_ofPred_eq] at hl hε
  have hw : p.1 * p.2.1 / 2 ≠ 0 := by positivity
  have hle : p.1 + p.2.1 ≠ 0 := by positivity
  simp only [blowupProfile_def]
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ ↦ p.1) p := contDiffAt_fst
  have h2 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ ↦ p.2.1) p := contDiffAt_snd.fst
  have h3 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ ↦ p.2.2) p := contDiffAt_snd.snd
  have hw' : ContDiffAt ℝ n (fun p : ℝ × ℝ × ℝ ↦ p.1 * p.2.1 / 2) p := (h1.mul h2).div_const _
  refine (h3.add (h1.pow 2)).sub (((h1.div (h1.add h2) hle).mul hw').mul
    ((hρ.contDiffAt.comp _ (((h3.sub (h2.pow 2)).div hw' hw).sub contDiffAt_const)).sub
      (hρ.contDiffAt.comp _ (((h3.sub ((h1.add h2).pow 2)).div hw' hw).add contDiffAt_const))))

/-- For `0 < l` and `0 < ε`, the profile `blowupProfile l ε` is smooth in `s`. -/
theorem contDiff_blowupProfile {n : ℕ∞} (hl : 0 < l) (hε : 0 < ε) :
    ContDiff ℝ n (blowupProfile l ε) := by
  rw [← contDiffOn_univ]
  have := (contDiffOn_blowupProfile (n := n)).comp
    ((contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn (s := univ))
    (fun s _ ↦ ⟨hl, hε, mem_univ s⟩)
  exact this

/-- Near the exceptional divisor, `blowupProfile l ε` is the profile `l² + s` of the radial map
of the model. -/
theorem blowupProfile_of_le (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε ^ 2) :
    blowupProfile l ε s = l ^ 2 + s := by
  have hw : 0 < l * ε / 2 := by positivity
  have h₁ : (s - ε ^ 2) / (l * ε / 2) - 1 + 1 ≤ 0 := by
    rw [sub_add_cancel]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  have h₂ : (s - (l + ε) ^ 2) / (l * ε / 2) + 1 + 1 ≤ 0 := by
    rw [div_add_one hw.ne', div_add_one hw.ne']
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hw.le
  rw [blowupProfile_def, smoothedMax_eq_right one_pos h₁, smoothedMax_eq_right one_pos h₂]
  ring

/-- Far from the exceptional divisor, `blowupProfile l ε` is the identity. -/
theorem blowupProfile_of_ge (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : (l + ε) ^ 2 ≤ s) :
    blowupProfile l ε s = s := by
  have hw : 0 < l * ε / 2 := by positivity
  have h₁ : 0 + 1 ≤ (s - ε ^ 2) / (l * ε / 2) - 1 := by
    rw [le_sub_iff_add_le, zero_add, one_add_one_eq_two, le_div_iff₀ hw]; nlinarith
  have h₂ : 0 + 1 ≤ (s - (l + ε) ^ 2) / (l * ε / 2) + 1 := by
    rw [zero_add, le_add_iff_nonneg_left]; exact div_nonneg (by linarith) hw.le
  rw [blowupProfile_def, smoothedMax_eq_left one_pos h₁, smoothedMax_eq_left one_pos h₂]
  field_simp
  ring

/-- The derivative of `blowupProfile l ε` at `s`, for `0 < l` and `0 < ε`: `1` minus
`l / (l + ε)` times the half-difference of the steps `smoothedSign 1` at the two rescaled
arguments of the definition. -/
theorem hasDerivAt_blowupProfile (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (blowupProfile l ε)
      (1 - l / (l + ε) * ((smoothedSign 1 ((s - ε ^ 2) / (l * ε / 2) - 1) -
        smoothedSign 1 ((s - (l + ε) ^ 2) / (l * ε / 2) + 1)) / 2)) s := by
  have hx : HasDerivAt (fun s ↦ (s - ε ^ 2) / (l * ε / 2) - 1) (1 / (l * ε / 2)) s :=
    (((hasDerivAt_id s).sub_const _).div_const _).sub_const _
  have hy : HasDerivAt (fun s ↦ (s - (l + ε) ^ 2) / (l * ε / 2) + 1) (1 / (l * ε / 2)) s :=
    (((hasDerivAt_id s).sub_const _).div_const _).add_const _
  have h := ((hasDerivAt_id s).add_const (l ^ 2)).sub
    ((((hasDerivAt_smoothedMax_left 1 0 _).comp s hx).sub
      ((hasDerivAt_smoothedMax_left 1 0 _).comp s hy)).const_mul (l / (l + ε) * (l * ε / 2)))
  convert h using 1
  · exact funext fun s ↦ blowupProfile_def l ε s
  · rw [sub_zero, sub_zero]
    field_simp
    ring

/-- The derivative of `blowupProfile l ε` lies in `[ε / (l + ε), 1]`: the step it subtracts
from `1` takes its values in `[0, l / (l + ε)]`. -/
theorem deriv_blowupProfile_mem (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    deriv (blowupProfile l ε) s ∈ Icc (ε / (l + ε)) 1 := by
  rw [(hasDerivAt_blowupProfile hl hε s).deriv]
  set x := (s - ε ^ 2) / (l * ε / 2) - 1
  set y := (s - (l + ε) ^ 2) / (l * ε / 2) + 1
  have hxy : y ≤ x := by
    rw [← sub_nonneg]
    have : x - y = 2 * (l + ε) / ε := by simp only [x, y]; field_simp; ring
    rw [this]; positivity
  have hm := monotone_smoothedSign zero_le_one hxy
  have h₁ := abs_le.1 (abs_smoothedSign_le_one 1 x)
  have h₂ := abs_le.1 (abs_smoothedSign_le_one 1 y)
  have hc : 0 ≤ l / (l + ε) := by positivity
  have hle : (smoothedSign 1 x - smoothedSign 1 y) / 2 ≤ 1 := by linarith
  have h := mul_le_of_le_one_right hc hle
  have h0 : 0 ≤ l / (l + ε) * ((smoothedSign 1 x - smoothedSign 1 y) / 2) :=
    mul_nonneg hc (by linarith)
  have h1 : ε / (l + ε) = 1 - l / (l + ε) := by field_simp; ring
  constructor <;> linarith

/-- The derivative of `blowupProfile l ε` is positive. -/
theorem deriv_blowupProfile_pos (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    0 < deriv (blowupProfile l ε) s :=
  (by positivity : 0 < ε / (l + ε)).trans_le (deriv_blowupProfile_mem hl hε s).1

/-- The derivative of `blowupProfile l ε` is at most `1`. -/
theorem deriv_blowupProfile_le_one (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    deriv (blowupProfile l ε) s ≤ 1 :=
  (deriv_blowupProfile_mem hl hε s).2

/-- For `0 < l` and `0 < ε`, `blowupProfile l ε` is differentiable. -/
theorem differentiable_blowupProfile (hl : 0 < l) (hε : 0 < ε) :
    Differentiable ℝ (blowupProfile l ε) :=
  fun s ↦ (hasDerivAt_blowupProfile hl hε s).differentiableAt

/-- `blowupProfile l ε` is strictly increasing. -/
theorem strictMono_blowupProfile (hl : 0 < l) (hε : 0 < ε) : StrictMono (blowupProfile l ε) :=
  strictMono_of_deriv_pos (deriv_blowupProfile_pos hl hε)

/-- `s ↦ blowupProfile l ε s - s` is nonincreasing, since the slope of the profile is at
most `1`. -/
theorem antitone_blowupProfile_sub_id (hl : 0 < l) (hε : 0 < ε) :
    Antitone fun s ↦ blowupProfile l ε s - s :=
  antitone_of_deriv_nonpos ((differentiable_blowupProfile hl hε).sub differentiable_id)
    fun s ↦ by
      have h := hasDerivAt_blowupProfile hl hε s
      have h1 := deriv_blowupProfile_le_one hl hε s
      rw [h.deriv] at h1
      rw [(h.fun_sub (hasDerivAt_id' s)).deriv]
      linarith

/-- `blowupProfile l ε` lies above the identity. -/
theorem le_blowupProfile (hl : 0 < l) (hε : 0 < ε) (s : ℝ) : s ≤ blowupProfile l ε s := by
  rcases le_total s ((l + ε) ^ 2) with h | h
  · have := antitone_blowupProfile_sub_id hl hε h
    simp only [blowupProfile_of_ge hl hε le_rfl, sub_self] at this
    linarith
  · exact (blowupProfile_of_ge hl hε h).ge

/-- `blowupProfile l ε` lies below `s + l²`. -/
theorem blowupProfile_le (hl : 0 < l) (hε : 0 < ε) (s : ℝ) : blowupProfile l ε s ≤ s + l ^ 2 := by
  rcases le_total s (ε ^ 2) with h | h
  · exact (blowupProfile_of_le hl hε h).trans_le (add_comm _ _).le
  · have := antitone_blowupProfile_sub_id hl hε h
    simp only [blowupProfile_of_le hl hε le_rfl, add_sub_cancel_right] at this
    linarith

/-- `blowupProfile l ε` is positive on `[0, ∞)`. -/
theorem blowupProfile_pos (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) :
    0 < blowupProfile l ε s := by
  have := (strictMono_blowupProfile hl hε).monotone hs
  rw [blowupProfile_of_le hl hε (by positivity)] at this
  linarith [pow_pos hl 2]

/-- The correction `q = blowupCorrection l ε` of the blowup of weight `l` with collar `ε`:
`q(s) = ∫₀ˢ (h(u) - u - l²) / u du` with `h = blowupProfile l ε`. For `0 < l` and `0 < ε` the
integrand vanishes for `u ≤ ε²`, so `q` is smooth (`contDiff_blowupCorrection`) and zero on
`Iic (ε ^ 2)`; it satisfies `s q'(s) = h(s) - s - l²` (`mul_deriv_blowupCorrection`), and
`l² log s + q s` is constant for `s ≥ (l + ε)²`. -/
def blowupCorrection (l ε s : ℝ) : ℝ :=
  ∫ u in 0..s, (blowupProfile l ε u - u - l ^ 2) / u

theorem blowupCorrection_def (l ε s : ℝ) :
    blowupCorrection l ε s = ∫ u in 0..s, (blowupProfile l ε u - u - l ^ 2) / u :=
  (rfl)

/-- The integrand `(blowupProfile l ε u - u - l ^ 2) / u` of `blowupCorrection l ε` is a smooth
function of `((l, ε), u)` for `0 < l`, `0 < ε`: it vanishes for `u ≤ ε ^ 2`. -/
theorem contDiffOn_blowupProfile_sub_sub_div {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : (ℝ × ℝ) × ℝ ↦
        (blowupProfile p.1.1 p.1.2 p.2 - p.2 - p.1.1 ^ 2) / p.2)
      (({l | 0 < l} ×ˢ {ε | 0 < ε}) ×ˢ univ) := by
  rintro ⟨⟨l, ε⟩, u⟩ ⟨⟨hl, hε⟩, -⟩
  simp only [mem_ofPred_eq] at hl hε
  refine ContDiffAt.contDiffWithinAt ?_
  rcases lt_or_ge 0 u with hu | hu
  · have hU : IsOpen ({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε} ×ˢ (univ : Set ℝ)) :=
      (isOpen_lt continuous_const continuous_id).prod
        ((isOpen_lt continuous_const continuous_id).prod isOpen_univ)
    have hh : ContDiffAt ℝ n (fun p : (ℝ × ℝ) × ℝ ↦ blowupProfile p.1.1 p.1.2 p.2)
        ((l, ε), u) :=
      ((contDiffOn_blowupProfile (n := n)).contDiffAt
        (hU.mem_nhds ⟨hl, hε, mem_univ u⟩)).comp ((l, ε), u)
        (by fun_prop : ContDiff ℝ n fun p : (ℝ × ℝ) × ℝ ↦ (p.1.1, p.1.2, p.2)).contDiffAt
    exact ((hh.sub contDiffAt_snd).sub (contDiffAt_fst.fst.pow 2)).div contDiffAt_snd hu.ne'
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    have hV : IsOpen {p : (ℝ × ℝ) × ℝ | 0 < p.1.1 ∧ 0 < p.1.2 ∧ p.2 < p.1.2 ^ 2} :=
      (isOpen_lt continuous_const continuous_fst.fst).inter
        ((isOpen_lt continuous_const continuous_fst.snd).inter
          (isOpen_lt continuous_snd (continuous_fst.snd.pow 2)))
    filter_upwards [hV.mem_nhds ⟨hl, hε, hu.trans_lt (by positivity)⟩] with p hp
    rw [blowupProfile_of_le hp.1 hp.2.1 hp.2.2.le]; ring

/-- The correction `blowupCorrection l ε s` is a smooth function of `(l, ε, s)` for `0 < l`,
`0 < ε`. -/
theorem contDiffOn_blowupCorrection {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ × ℝ ↦ blowupCorrection p.1 p.2.1 p.2.2)
      ({l | 0 < l} ×ˢ {ε | 0 < ε} ×ˢ univ) := by
  have hS : IsOpen ({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε}) :=
    (isOpen_lt continuous_const continuous_id).prod (isOpen_lt continuous_const continuous_id)
  have h := ((convex_Ioi 0).prod (convex_Ioi 0)).contDiffOn_parametric_primitive convex_univ
    hS.uniqueDiffOn (mem_univ 0) (contDiffOn_blowupProfile_sub_sub_div (n := n))
  have hm : MapsTo (fun p : ℝ × ℝ × ℝ ↦ ((p.1, p.2.1), p.2.2))
      ({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε} ×ˢ univ)
      (({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε}) ×ˢ univ) :=
    fun p hp ↦ ⟨⟨hp.1, hp.2.1⟩, mem_univ _⟩
  have hφ : ContDiff ℝ n fun p : ℝ × ℝ × ℝ ↦ ((p.1, p.2.1), p.2.2) := by fun_prop
  exact (h.comp hφ.contDiffOn hm).congr fun p _ ↦ blowupCorrection_def _ _ _

/-- For `0 < l` and `0 < ε`, the integrand `(blowupProfile l ε u - u - l ^ 2) / u` of
`blowupCorrection l ε` is smooth in `u`. -/
theorem contDiff_blowupProfile_sub_sub_div {n : ℕ∞} (hl : 0 < l) (hε : 0 < ε) :
    ContDiff ℝ n fun u ↦ (blowupProfile l ε u - u - l ^ 2) / u := by
  have hm : MapsTo (fun u : ℝ ↦ ((l, ε), u)) univ
      (({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε}) ×ˢ univ) :=
    fun u _ ↦ ⟨⟨hl, hε⟩, mem_univ u⟩
  have hg : ContDiff ℝ n fun u : ℝ ↦ ((l, ε), u) := contDiff_const.prodMk contDiff_id
  have h := (contDiffOn_blowupProfile_sub_sub_div (n := n)).comp hg.contDiffOn hm
  rw [← contDiffOn_univ]
  exact h

/-- The derivative of `blowupCorrection l ε` at `s` is `(h(s) - s - l²) / s`, with
`h = blowupProfile l ε`; at `s = 0` the quotient is `0`, since the integrand vanishes near `0`. -/
theorem hasDerivAt_blowupCorrection (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (blowupCorrection l ε) ((blowupProfile l ε s - s - l ^ 2) / s) s :=
  ((contDiff_blowupProfile_sub_sub_div (n := 0) hl hε).continuous.integral_hasStrictDerivAt 0
    s).hasDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ blowupCorrection_def l ε s)

/-- For `0 < l` and `0 < ε`, the correction `blowupCorrection l ε` is smooth in `s`. -/
theorem contDiff_blowupCorrection {n : ℕ∞} (hl : 0 < l) (hε : 0 < ε) :
    ContDiff ℝ n (blowupCorrection l ε) := by
  have hg : ContDiff ℝ n fun s : ℝ ↦ (l, ε, s) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hm : MapsTo (fun s : ℝ ↦ (l, ε, s)) univ ({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε} ×ˢ univ) :=
    fun s _ ↦ ⟨hl, hε, mem_univ s⟩
  have h := (contDiffOn_blowupCorrection (n := n)).comp hg.contDiffOn hm
  rw [← contDiffOn_univ]
  exact h

/-- The derivative of the correction against the profile: `s q'(s) = h(s) - s - l²` for
`q = blowupCorrection l ε` and `h = blowupProfile l ε`. -/
theorem mul_deriv_blowupCorrection (hl : 0 < l) (hε : 0 < ε) (s : ℝ) :
    s * deriv (blowupCorrection l ε) s = blowupProfile l ε s - s - l ^ 2 := by
  rw [(hasDerivAt_blowupCorrection hl hε s).deriv]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [blowupProfile_of_le hl hε (by positivity)]; ring
  · exact mul_div_cancel₀ _ hs

/-- Near the exceptional divisor, the correction `blowupCorrection l ε` vanishes. -/
theorem blowupCorrection_of_le (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε ^ 2) :
    blowupCorrection l ε s = 0 := by
  rw [blowupCorrection_def, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro u hu
  dsimp only
  rw [blowupProfile_of_le hl hε ((mem_uIcc.1 hu).elim (fun h ↦ h.2.trans hs)
    fun h ↦ h.2.trans (by positivity))]
  ring

/-- Far from the exceptional divisor, `l² log s + blowupCorrection l ε s` is constant: it takes
its value at `(l + ε)²` for every `s ≥ (l + ε)²`. -/
theorem sq_mul_log_add_blowupCorrection_of_ge (hl : 0 < l) (hε : 0 < ε) {s : ℝ}
    (hs : (l + ε) ^ 2 ≤ s) :
    l ^ 2 * Real.log s + blowupCorrection l ε s =
      l ^ 2 * Real.log ((l + ε) ^ 2) + blowupCorrection l ε ((l + ε) ^ 2) := by
  have hc : 0 < (l + ε) ^ 2 := by positivity
  have hs0 : 0 < s := hc.trans_le hs
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun u ↦ (blowupProfile l ε u - u - l ^ 2) / u) MeasureTheory.volume a b :=
    (contDiff_blowupProfile_sub_sub_div (n := 0) hl hε).continuous.intervalIntegrable
  have hsplit : blowupCorrection l ε s = blowupCorrection l ε ((l + ε) ^ 2) +
      ∫ u in (l + ε) ^ 2..s, (blowupProfile l ε u - u - l ^ 2) / u := by
    rw [blowupCorrection_def, blowupCorrection_def,
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have hint : ∫ u in (l + ε) ^ 2..s, (blowupProfile l ε u - u - l ^ 2) / u =
      ∫ u in (l + ε) ^ 2..s, -l ^ 2 * u⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le hs] at hu
    simp only [blowupProfile_of_ge hl hε hu.1]
    ring
  rw [hsplit, hint, intervalIntegral.integral_const_mul, integral_inv_of_pos hc hs0,
    Real.log_div hs0.ne' hc.ne']
  ring

/-- The derivative of the correction `blowupCorrection l ε` vanishes on `Iic (ε ^ 2)`. -/
theorem deriv_blowupCorrection_of_le (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε ^ 2) :
    deriv (blowupCorrection l ε) s = 0 := by
  rw [(hasDerivAt_blowupCorrection hl hε s).deriv, blowupProfile_of_le hl hε hs]
  ring

/-- The second derivative of the correction `blowupCorrection l ε` vanishes on `Iic (ε ^ 2)`, its
end point included. -/
theorem deriv_deriv_blowupCorrection_of_le (hl : 0 < l) (hε : 0 < ε) {s : ℝ} (hs : s ≤ ε ^ 2) :
    deriv (deriv (blowupCorrection l ε)) s = 0 := by
  have hd : Differentiable ℝ (deriv (blowupCorrection l ε)) :=
    (contDiff_infty_iff_deriv.1 (contDiff_blowupCorrection hl hε)).2.differentiable (by simp)
  have h₀ : HasDerivWithinAt (deriv (blowupCorrection l ε)) 0 (Iic (ε ^ 2)) s :=
    (hasDerivWithinAt_const s _ 0).congr (fun t ht ↦ deriv_blowupCorrection_of_le hl hε ht)
      (deriv_blowupCorrection_of_le hl hε hs)
  exact (uniqueDiffOn_Iic _ s hs).eq_deriv _ (hd s).hasDerivAt.hasDerivWithinAt h₀

/-! ### The forms `ω̃_{λ,ε}` -/

section ProfileForm

open TauCeti SmoothAlmostComplexStructure TopologicalSpace
open scoped Manifold ContDiff TauCeti.ComplexManifold

variable (n : ℕ)

/-- The correction potential `z ↦ q(|z|²)` on `E = ℂⁿ⁺¹`, for `q = blowupCorrection l ε` and
`|z|` the Euclidean norm, as a smooth function when `0 < l` and `0 < ε`
(`correctionPotential_apply`); it is `0` for other values of the parameters. -/
noncomputable def correctionPotential (l ε : ℝ) :
    C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ :=
  ⟨fun z ↦ if 0 < l ∧ 0 < ε then
      blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) else 0, by
    split_ifs with h
    · exact ((contDiff_blowupCorrection h.1 h.2).comp
        contDiff_norm_sq_complexToRealEuclidean).contMDiff
    · exact contMDiff_const⟩

theorem coe_correctionPotential (l ε : ℝ) :
    ⇑(correctionPotential n l ε) = fun z ↦ if 0 < l ∧ 0 < ε then
      blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) else 0 :=
  (rfl)

/-- For `0 < l` and `0 < ε`, the correction potential is `z ↦ q(|z|²)`. -/
@[simp]
theorem correctionPotential_apply {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) (z : Fin (n + 1) → ℂ) :
    correctionPotential n l ε z =
      blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) := by
  simp [coe_correctionPotential, hl, hε]

/-- Unless `0 < l` and `0 < ε`, the correction potential is `0`. -/
theorem correctionPotential_of_not {l ε : ℝ} (h : ¬(0 < l ∧ 0 < ε)) :
    correctionPotential n l ε = 0 :=
  ContMDiffMap.ext fun z ↦ by simp [coe_correctionPotential, h]

/-- The form `ω_q = (1/4) d (J* d φ)` on `E` of the correction potential
`φ = correctionPotential n l ε`, where `J*` is the structure `a ↦ -a ∘ J` on one-forms of the
complex structure `J` of `E`; by `Dolbeault/Potential.lean` it is `(i/2) ∂∂bar φ`. -/
noncomputable def correctionForm (l ε : ℝ) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ) :=
  (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
    (SmoothForm.ofFunction (correctionPotential n l ε))

theorem correctionForm_def (l ε : ℝ) :
    correctionForm n l ε =
      (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
        (SmoothForm.ofFunction (correctionPotential n l ε)) :=
  (rfl)

/-- The form of the correction potential vanishes at the points of the closed ball of radius `ε`:
by `mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt` its value at
`z` is a combination of `q'(|z|²)` and `q''(|z|²)`, which vanish for `|z|² ≤ ε²`. -/
theorem correctionForm_apply_eq_zero {l ε : ℝ} {z : Fin (n + 1) → ℂ}
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε) : (correctionForm n l ε).val z = 0 := by
  by_cases h : 0 < l ∧ 0 < ε
  swap
  · have h0 : SmoothForm.ofFunction (correctionPotential n l ε) = 0 := by
      rw [correctionPotential_of_not n h]
      exact SmoothBundleForm.ext fun x v ↦ by
        simp [SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply]
    rw [correctionForm_def, h0, map_zero]
    simp
  obtain ⟨hl, hε⟩ := h
  have hq := contDiff_blowupCorrection (n := ⊤) hl hε
  have hq' := (contDiff_infty_iff_deriv.1 hq).2
  have hq'' := (contDiff_infty_iff_deriv.1 hq').2
  have hs := contDiff_norm_sq_complexToRealEuclidean (ι := Fin (n + 1)) (n := ∞)
  let s : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, hs.contMDiff⟩
  let a : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, (hq'.comp hs).contMDiff⟩
  let b : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, (hq''.comp hs).contMDiff⟩
  have hz2 : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [correctionForm_def, potentialForm_def,
    mextDerivₗ_covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt (f := s)
      (a := a) (b := b) (fun x ↦ by simp [s, correctionPotential_apply n hl hε x])
      (fun _ ↦ by simp [a, s]) (fun _ ↦ by simp [b, s])
      (fun _ ↦ (hq.differentiable (by simp) _).hasDerivAt)
      (fun _ ↦ (hq'.differentiable (by simp) _).hasDerivAt)]
  have ha : a z = 0 := by
    simp only [a, ContMDiffMap.coeFn_mk, Function.comp_apply]
    exact deriv_blowupCorrection_of_le hl hε hz2
  have hb : b z = 0 := by
    simp only [b, ContMDiffMap.coeFn_mk, Function.comp_apply]
    exact deriv_deriv_blowupCorrection_of_le hl hε hz2
  simp [ha, hb]

/-- On `E ∖ 0`, the form of the correction potential is the radial potential form of
`q = blowupCorrection l ε`, for `0 < l` and `0 < ε`: the inclusion is holomorphic, so pulling back
commutes with forms of potentials (`mpullback_potentialForm`). -/
theorem mpullback_subtypeVal_correctionForm {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    SmoothForm.mpullback (Subtype.val : puncturedSpace (Fin (n + 1) → ℂ) → _) contMDiff_subtypeVal
        (correctionForm n l ε) =
      radialPotentialForm (Fin (n + 1)) (blowupCorrection l ε)
        (contDiff_blowupCorrection hl hε).contDiffOn := by
  rw [correctionForm_def, radialPotentialForm_def,
    mpullback_potentialForm _ (isPseudoholomorphic_ofComplexManifold_subtype_val _)]
  congr 1
  refine SmoothBundleForm.ext fun z v ↦ ?_
  rw [SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply,
    SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply, correctionPotential_apply n hl hε,
    coe_radialPotential]

/-- The form `ω̃_{l,ε} = ω̃_l + π^* ω_q` on the model blowup, where `ω̃_l = blowupForm n l`, `π` is
the blowdown and `ω_q = correctionForm n l ε` is the form of the potential `q(|z|²)` on `E`, for
`q = blowupCorrection l ε`. It is `ω̃_l` on `L(ε)` (`profileForm_eq_blowupForm_on`), and for
`0 < l` and `0 < ε` it is `π^* ω₀` off `L(l + ε)` (`profileForm_eq_on_compl`). -/
noncomputable def profileForm (l ε : ℝ) : SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) :=
  blowupForm n l +
    SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ) (correctionForm n l ε)

theorem profileForm_def (l ε : ℝ) :
    profileForm n l ε = blowupForm n l +
      SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
        (correctionForm n l ε) :=
  (rfl)

/-- On `L(ε) = closedNbhd n ε`, the form `ω̃_{l,ε}` is `ω̃_l`, since the correction potential
vanishes to second order there. -/
theorem profileForm_eq_blowupForm_on {l ε : ℝ} :
    ∀ p ∈ closedNbhd n ε, (profileForm n l ε).val p = (blowupForm n l).val p := by
  intro p hp
  ext v
  simp [profileForm_def,
    correctionForm_apply_eq_zero n (mem_closedNbhd_iff.1 hp)]

/-- The form `ω_q` of the correction potential is closed: it is a multiple of an exterior
derivative. -/
theorem isClosed_correctionForm (l ε : ℝ) : (correctionForm n l ε).IsClosed := by
  rw [correctionForm_def]
  exact (SmoothForm.isClosed_mextDerivₗ _).smul _

/-- The form `ω̃_{l,ε}` is closed, as the sum of `ω̃_l` and the pull-back of a closed form. -/
theorem isClosed_profileForm (l ε : ℝ) : (profileForm n l ε).IsClosed := by
  rw [profileForm_def]
  exact (isClosed_blowupForm l).add ((isClosed_correctionForm n l ε).mpullback _ _)

/-- The radial potential `s ↦ s + l² log s + q(s)` of `ω̃_{l,ε}` off the divisor, for
`q = blowupCorrection l ε`, is smooth on `(0, ∞)`. -/
theorem contDiffOn_add_mul_log_add_blowupCorrection {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s) (Ioi 0) :=
  (contDiffOn_add_mul_log l).add (contDiff_blowupCorrection hl hε).contDiffOn

/-- On `(0, ∞)`, the radial potential `g(s) = s + l² log s + q(s)` of `ω̃_{l,ε}` has derivative
`h(s) / s`, for the profile `h = blowupProfile l ε` and `q = blowupCorrection l ε`. -/
theorem deriv_add_mul_log_add_blowupCorrection {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) {s : ℝ}
    (hs : 0 < s) :
    deriv (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s) s =
      blowupProfile l ε s / s := by
  have hd : HasDerivAt (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s)
      (1 + l ^ 2 * s⁻¹ + (blowupProfile l ε s - s - l ^ 2) / s) s :=
    ((hasDerivAt_id s).add ((Real.hasDerivAt_log hs.ne').const_mul _)).add
      (hasDerivAt_blowupCorrection hl hε s)
  rw [hd.deriv]
  field_simp
  ring

/-- Off the exceptional divisor, `ω̃_{l,ε}` is the form of the radial potential
`|z|² + l² log |z|² + q(|z|²)`, for `0 < l` and `0 < ε`: its pull-back along the inverse of the
blowdown, from `E ∖ 0` to the complement of the divisor, is `radialPotentialForm` of
`s ↦ s + l² log s + q(s)`. -/
theorem mpullback_blowdownDiffeomorph_symm_profileForm {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    SmoothForm.mpullback (blowdownPuncturedDiffeomorph n).symm
        (blowdownPuncturedDiffeomorph n).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (profileForm n l ε)) =
      radialPotentialForm (Fin (n + 1)) (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s)
        (contDiffOn_add_mul_log_add_blowupCorrection hl hε) := by
  rw [profileForm_def, map_add, map_add, mpullback_blowdownDiffeomorph_symm_blowupForm,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ contMDiff_subtypeVal
      blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
    mpullback_subtypeVal_correctionForm n hl hε,
    ← radialPotentialForm_add _ (contDiff_blowupCorrection hl hε).contDiffOn]

/-- Off `L(l + ε) = closedNbhd n (l + ε)`, the form `ω̃_{l,ε}` is `π^* ω₀`, for `0 < l` and
`0 < ε`: there `l² log s + q(s)` is constant in `s = |z|²`, so the Fubini–Study term of `ω̃_l`
and the correction cancel. -/
theorem profileForm_eq_on_compl {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    ∀ p ∉ closedNbhd n (l + ε), (profileForm n l ε).val p =
      (SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
        (ω₀E n)).val p := by
  intro p hp
  have hlε : 0 < l + ε := add_pos hl hε
  have hp' : l + ε < ‖complexToRealEuclidean (Fin (n + 1)) p.blowdown‖ :=
    not_le.1 (mt mem_closedNbhd_iff.2 hp)
  have hpU : p ∈ offDivisorOpens n := mem_offDivisorOpens.2 fun h0 ↦ by
    rw [mem_exceptionalDivisor_iff.1 h0, map_zero, norm_zero] at hp'
    exact hlε.not_gt hp'
  refine SmoothForm.apply_eq_of_mpullback_symm_mpullback_subtype_val_apply_eq
    (blowdownPuncturedDiffeomorph n) ⟨p, hpU⟩ ?_
  rw [mpullback_blowdownDiffeomorph_symm_profileForm n hl hε, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_congr _ contMDiff_subtypeVal
      blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
    ω₀E_def, ← radialPotentialForm_id contDiffOn_id]
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
  set x := ∑ i, ‖((blowdownPuncturedDiffeomorph n ⟨p, hpU⟩ : puncturedSpace _) :
    Fin (n + 1) → ℂ) i‖ ^ 2
  have hx : (l + ε) ^ 2 < x := by
    simp only [x, coe_blowdownPuncturedDiffeomorph_apply, ← norm_sq_complexToRealEuclidean]
    exact pow_lt_pow_left₀ hp' hlε.le two_ne_zero
  have he : (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s) =ᶠ[nhds x]
      fun s ↦ s + (l ^ 2 * Real.log ((l + ε) ^ 2) + blowupCorrection l ε ((l + ε) ^ 2)) := by
    filter_upwards [Ioi_mem_nhds hx] with s hs
    rw [← sq_mul_log_add_blowupCorrection_of_ge hl hε (le_of_lt hs)]
    ring
  rw [radialPotentialForm_apply, radialPotentialForm_apply, he.deriv_eq, he.deriv.deriv_eq]
  simp

/-- The radial map `F_{l,ε} z = √(h(|z|²) / |z|²) z` of the profile `h = blowupProfile l ε`,
composed with the blowdown, pulls `ω₀` back to `ω̃_{l,ε}` off the exceptional divisor, for
`0 < l` and `0 < ε`. -/
theorem mpullback_radialMap_profileForm {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    SmoothForm.mpullback
        (radialMap (blowupProfile l ε) (fun _ hs ↦ blowupProfile_pos hl hε (le_of_lt hs)) ∘
          blowdownPuncturedDiffeomorph n)
        ((contMDiff_radialMap (contDiff_blowupProfile (n := ⊤) hl hε).contDiffOn _).comp
          (blowdownPuncturedDiffeomorph n).contMDiff)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (profileForm n l ε) := by
  have hs : ContDiffOn ℝ ∞ (blowupProfile l ε) (Ioi 0) :=
    (contDiff_blowupProfile (n := ⊤) hl hε).contDiffOn
  rw [← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).contMDiff
      (contMDiff_radialMap hs _), ω₀E_def,
    mpullback_radialMap_stdForm (ι := Fin (n + 1)) hs _
      (contDiffOn_add_mul_log_add_blowupCorrection hl hε)
      fun s hs ↦ deriv_add_mul_log_add_blowupCorrection hl hε hs,
    ← mpullback_blowdownDiffeomorph_symm_profileForm n hl hε, SmoothForm.mpullback_mpullback_symm]

/-- For `0 < l` and `0 < ε`, the form `ω̃_{l,ε}` is Kähler for the complex structure of the model
blowup. Compatibility is checked on two open sets that cover the model, since the exceptional
divisor lies in `openNbhd n ε`: on `openNbhd n ε` the form is `ω̃_l`, which is Kähler
(`isKahler_blowupForm`), and off the divisor it is the pull-back of `ω₀` along `F_{l,ε} ∘ π`
(`mpullback_radialMap_profileForm`), which is Kähler since the profile `h_{l,ε}` is positive and
increasing (`isKahler_mpullback_radialMap`), pulled back along the holomorphic map `π`. -/
theorem isKahler_profileForm {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) :
    (profileForm n l ε).IsKahler (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n)) := by
  set V : Opens (BlowupModel n) := ⟨openNbhd n ε, isOpen_openNbhd ε⟩
  set U : Opens (BlowupModel n) := offDivisorOpens n
  -- On `V`, the form restricts as `ω̃_l` does.
  have hV : SmoothForm.mpullback (Subtype.val : V → BlowupModel n) contMDiff_subtypeVal
      (profileForm n l ε) =
      SmoothForm.mpullback (Subtype.val : V → BlowupModel n) contMDiff_subtypeVal
        (blowupForm n l) :=
    SmoothBundleForm.ext fun p v ↦ by
      rw [SmoothForm.mpullback_apply, SmoothForm.mpullback_apply,
        profileForm_eq_blowupForm_on n p (openNbhd_subset_closedNbhd ε p.property)]
  -- On `U`, it is the pull-back along `π` of a Kähler form on `E ∖ 0`.
  have hU : SmoothTwoForm.Compatible
      (SmoothForm.mpullback (Subtype.val : U → BlowupModel n) contMDiff_subtypeVal
        (profileForm n l ε)) (ofComplexManifold (Fin (n + 1) → ℂ) U) := by
    rw [← mpullback_radialMap_profileForm n hl hε,
      ← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).contMDiff, ω₀E_def]
    exact (isKahler_mpullback_radialMap (contDiff_blowupProfile hl hε).contDiffOn _
      fun s _ ↦ deriv_blowupProfile_pos hl hε s).compatible.mpullback
      isPseudoholomorphic_blowdownPuncturedDiffeomorph _
      fun x ↦ ((blowdownPuncturedDiffeomorph n).isInvertible_mfderiv (x := x) (by simp)).injective
  refine SmoothTwoForm.isKahler_ofComplexManifold_iff.2 ⟨isClosed_profileForm n l ε,
    SmoothTwoForm.compatible_of_compatible_restrictOpen (fun b : Bool ↦ bif b then V else U)
      (fun p ↦ ?_) (Bool.rec ?_ ?_)⟩
  · by_cases hp : p ∈ openNbhd n ε
    · exact ⟨true, hp⟩
    · exact ⟨false, mem_offDivisorOpens.2 fun h ↦
        hp (exceptionalDivisor_subset_openNbhd hε h)⟩
  · dsimp only [Bool.cond_false]
    rw [SmoothAlmostComplexStructure.restrictOpen_ofComplexManifold]
    exact hU
  · dsimp only [Bool.cond_true]
    rw [hV]
    exact (isKahler_blowupForm hl.ne').compatible.restrictOpen V

/-- **The forms `ω̃_{l,ε}` in smooth families.** For smooth `l ε : unitInterval → ℝ` with positive
values, the forms `ω̃_{l t, ε t} = profileForm n (l t) (ε t)` on the model blowup form a smooth
family. -/
theorem isSmoothFamily_profileForm {l ε : unitInterval → ℝ} (hl : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ l)
    (hε : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ ε) (hl0 : ∀ t, 0 < l t) (hε0 : ∀ t, 0 < ε t) :
    IsSmoothFamily (𝓡∂ 1) fun t ↦ profileForm n (l t) (ε t) := by
  let s : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ :=
    ⟨fun z ↦ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2,
      (contDiff_norm_sq_complexToRealEuclidean (n := ∞)).contMDiff⟩
  -- The coefficient `q'(|z|²)`, jointly smooth in the parameter and the point.
  have hU : IsOpen (({l : ℝ | 0 < l} ×ˢ {ε : ℝ | 0 < ε}) ×ˢ (univ : Set ℝ)) :=
    ((isOpen_lt continuous_const continuous_id).prod
      (isOpen_lt continuous_const continuous_id)).prod isOpen_univ
  have ha : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, Fin (n + 1) → ℂ)) 𝓘(ℝ) ∞
      fun p : unitInterval × (Fin (n + 1) → ℂ) ↦
        (blowupProfile (l p.1) (ε p.1) (s p.2) - s p.2 - l p.1 ^ 2) / s p.2 := fun p ↦
    ((contDiffOn_blowupProfile_sub_sub_div.contDiffAt
      (hU.mem_nhds ⟨⟨hl0 p.1, hε0 p.1⟩, mem_univ _⟩)).contMDiffAt).comp p
      ((((hl.comp contMDiff_fst).prodMk_space (hε.comp contMDiff_fst)).prodMk_space
        (s.contMDiff.comp contMDiff_snd)) p)
  have hat (t : unitInterval) : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℂ) 𝓘(ℝ) ∞
      fun z ↦ (blowupProfile (l t) (ε t) (s z) - s z - l t ^ 2) / s z :=
    ha.comp (f := fun z ↦ (t, z)) (contMDiff_const.prodMk contMDiff_id)
  let a : unitInterval → C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := fun t ↦ ⟨_, hat t⟩
  have hq (t : unitInterval) : correctionForm n (l t) (ε t) = (4 : ℝ)⁻¹ •
      mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (SmoothForm.funSMulₗ (a t)
        ((ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (SmoothForm.ofFunction s)))) := by
    rw [correctionForm_def, potentialForm_def,
      covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt (f := s) (g' := a t)
        (fun x ↦ correctionPotential_apply n (hl0 t) (hε0 t) x)
        (fun x ↦ hasDerivAt_blowupCorrection (hl0 t) (hε0 t) (s x))]
  simp_rw [profileForm_def, blowupForm_def, hq]
  exact ((isSmoothFamily_const _).add ((isSmoothFamily_const _).fun_smul (hl.pow 2))).add
    ((((isSmoothFamily_const _).funSMul_family a ha).mextDeriv.smul _).mpullback _ _)

end ProfileForm

end SymplecticGeometry.BlowupModel

end
