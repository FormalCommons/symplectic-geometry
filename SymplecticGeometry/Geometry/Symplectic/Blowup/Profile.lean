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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Dolbeault.Potential
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Smooth
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Submanifold
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pseudoholomorphic
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm

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
  `deriv_blowupProfile_le_one`); so `s ≤ h s ≤ s + l ^ 2` (`le_blowupProfile`,
  `blowupProfile_le`).
* `SymplecticGeometry.BlowupModel.IsBlowupProfile l ε h`: the properties of `blowupProfile l ε`
  that the forms below use, for a general profile `h`: `0 < l`, `0 < ε`, `h` smooth with
  positive derivative, `h s = l ^ 2 + s` for `s ≤ ε ^ 2` and `h s = s` for `(l + ε) ^ 2 ≤ s`
  (`isBlowupProfile_blowupProfile`). Such an `h` is strictly increasing
  (`IsBlowupProfile.strictMono`) and positive on `[0, ∞)` (`IsBlowupProfile.pos`), as `radialMap`
  asks on `Ioi 0`. The profiles of weight `l` and collar `ε` form a convex set
  (`convex_setOfPred_isBlowupProfile`, and `IsBlowupProfile.one_sub_smul_add_smul` for the segment
  `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`).
* `SymplecticGeometry.BlowupModel.profileCorrection l h s`: the correction
  `q(s) = ∫₀ˢ (h(u) - u - l²) / u du` of a profile `h`. For `IsBlowupProfile l ε h` it is smooth
  (`contDiff_profileCorrection`), zero for `s ≤ ε ^ 2` (`profileCorrection_of_le`), equal to
  `-l² log s` plus a constant for `s ≥ (l + ε) ^ 2` (`sq_mul_log_add_profileCorrection_of_ge`),
  with `s q'(s) = h(s) - s - l²` (`mul_deriv_profileCorrection`). For `h = blowupProfile l ε`
  it is smooth in `(l, ε, s)` (`contDiffOn_profileCorrection_blowupProfile`). It is affine in
  the profile (`profileCorrection_one_sub_smul_add_smul`), by linearity of the integral.

The smoothness of `q` is that of the primitive of its integrand, which is smooth
(`IsBlowupProfile.contDiff_sub_sub_div`) since it vanishes for `u ≤ ε ^ 2`, so near `u = 0`.
For `h = blowupProfile l ε` the integrand is smooth in the parameters as well
(`contDiffOn_blowupProfile_sub_sub_div`), and the smoothness of `q` in them is that of a
parametric primitive, Tau Ceti's `Convex.contDiffOn_parametric_primitive`.

The second half of the file defines the forms `ω̃_{l,ε}` of a profile `h` on the model blowup
`L = BlowupModel n`, with blowdown `π : L → E = ℂⁿ⁺¹`, the exceptional divisor `Z` and the
neighbourhoods `L(ε) = closedNbhd n ε` of `Model.lean`. Each takes the profile `h` as its last
argument, which defaults to `blowupProfile l ε`, so that `profileForm n l ε` is the form of
`blowupProfile l ε`; the statements below but the last hold for every `h` with
`IsBlowupProfile l ε h`:

* `SymplecticGeometry.BlowupModel.correctionPotential n l ε h`: the smooth function
  `z ↦ q(|z|²)` on `E`, for `q = profileCorrection l h` and the Euclidean norm `|z|`
  (`correctionPotential_apply`; it is `0` unless `IsBlowupProfile l ε h`), and
  `SymplecticGeometry.BlowupModel.correctionForm n l ε h`: its form
  `ω_q = (1/4) d (J* d (q(|z|²)))` on all of `E`, the `potentialForm` of that function. It vanishes
  on the closed ball of radius `ε` (`correctionForm_apply_eq_zero`), since there the form of a
  composite potential, `potentialForm_ofFunction_comp_of_hasDerivAt`, only
  involves `q'(|z|²)` and `q''(|z|²)` (`deriv_profileCorrection_of_le`,
  `deriv_deriv_profileCorrection_of_le`); on `E ∖ 0` it is `radialPotentialForm` of `q`
  (`mpullback_subtypeVal_correctionForm`, by `mpullback_potentialForm` along the
  holomorphic inclusion).
* `SymplecticGeometry.BlowupModel.profileForm n l ε h`: the form `ω̃_{l,ε} = ω̃_l + π^* ω_q`,
  defined on all of `L` at once, so that no form is glued across `Z`.
* `SymplecticGeometry.BlowupModel.profileForm_eq_blowupForm_on`: it is `ω̃_l` at the points of
  `L(ε)`.
* `SymplecticGeometry.BlowupModel.profileForm_eq_on_compl`: for a profile `h` it is
  `π^* ω₀` at the points off `L(l + ε)`. Off `Z`, read on `E ∖ 0` through the blowdown, `ω̃_l` is
  `radialPotentialForm` of `s + l² log s` (`mpullback_blowdownDiffeomorph_symm_blowupForm`), so
  `ω̃_{l,ε}` is that of `s + l² log s + q(s)`, whose derivatives are those of `s` for
  `s > (l + ε)²` (`sq_mul_log_add_profileCorrection_of_ge`); and `π^* ω₀` is that of `s`
  (`radialPotentialForm_id`). That reading of `ω̃_{l,ε}` off `Z` is
  `mpullback_blowdownDiffeomorph_symm_profileForm`.
* `SymplecticGeometry.BlowupModel.mpullback_radialMap_profileForm`: for a profile `h`, off `Z`
  the form `ω̃_{l,ε}` is the pull-back of `ω₀` along `F_{l,ε} ∘ π`, where `F_{l,ε}` is
  `radialMap` of `h`: by `mpullback_radialMap_stdForm`, since
  `s + l² log s + q(s)` has derivative `h(s) / s` (`deriv_add_mul_log_add_profileCorrection`).
  This follows `mpullback_radialMap_blowdown` of `Model.lean`, the case `h(s) = s + l²`.
* `SymplecticGeometry.BlowupModel.profileForm_one_sub_smul_add_smul`: along the segment
  `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`, between two profiles, `ω̃_{l,ε}` is the segment between
  their forms, as are the correction potential and its form
  (`correctionPotential_one_sub_smul_add_smul`, `correctionForm_one_sub_smul_add_smul`). The
  bound on `t` keeps the segment among the profiles, outside of which these definitions take
  their default values.
* `SymplecticGeometry.BlowupModel.isKahler_profileForm`: for a profile `h`, `ω̃_{l,ε}` is
  Kähler for the complex structure of `L`. It is closed (`isClosed_profileForm`), and its
  compatibility is checked on two open sets that cover `L`
  (`TauCeti.SmoothTwoForm.compatible_of_compatible_restrictOpen`): on `openNbhd n ε` it is `ω̃_l`,
  compatible by `isKahler_blowupForm`, and off `Z` it is the pull-back along the holomorphic
  blowdown (`isPseudoholomorphic_blowdownPuncturedDiffeomorph`) of `F_{l,ε}^* ω₀`, which
  `isKahler_mpullback_radialMap` makes Kähler, as `h > 0` and `h' > 0`.
* `SymplecticGeometry.BlowupModel.isSmoothFamily_profileForm`: for smooth positive `l ε` on
  `unitInterval`, `t ↦ ω̃_{l t, ε t}`, for the profiles `blowupProfile (l t) (ε t)`, is a smooth
  family of forms. Here `ω̃_l` is affine in `l²`, and for positive parameters
  the correction form is `(1/4) d (q'(|z|²) J* d|z|²)`
  (`covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt`), with `q'(s)` the
  integrand of `q`, smooth in `(l, ε, s)`; the coefficient is jointly smooth in the parameter
  and the point (`IsSmoothFamily.funSMul_family`).
* `SymplecticGeometry.BlowupModel.IsBlowupProfile.image_Ioi`: a profile maps `(0, ∞)` onto
  `(l², ∞)`, so its radial map `F_h` is a diffeomorphism of `E ∖ 0` onto `|w| > l`
  (`IsBlowupProfile.radialDiffeomorph`, `IsBlowupProfile.mem_radialShell_iff`).
* `SymplecticGeometry.BlowupModel.IsBlowupProfile.radialMap_of_le`,
  `IsBlowupProfile.radialMap_of_le_collar`: `F_h` is the identity on `|z| ≥ l + ε` and the
  radial map `F_l` of the model on `|z| ≤ ε`; for `l + ε < r` it maps the open ball of radius
  `r` minus `0` into itself (`IsBlowupProfile.norm_radialMap_lt`), and only its points
  there (`IsBlowupProfile.norm_lt_of_norm_radialMap_lt`,
  `IsBlowupProfile.norm_radialDiffeomorph_symm_lt`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.1 and
  Lemma A.3.1.
-/

public section

noncomputable section

open Set
open scoped ContDiff

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

/-! ### Profiles of the blowup and their corrections -/

/-- `h` is a profile of the blowup of weight `l` with collar `ε`, in the variable `s = |z|²`:
`0 < l`, `0 < ε`, and `h : ℝ → ℝ` is smooth with positive derivative, `l² + s` for `s ≤ ε²` and
`s` for `s ≥ (l + ε)²`. For `0 < l` and `0 < ε`, `blowupProfile l ε` is one
(`isBlowupProfile_blowupProfile`). -/
structure IsBlowupProfile (l ε : ℝ) (h : ℝ → ℝ) : Prop where
  /-- The weight is positive. -/
  weight_pos : 0 < l
  /-- The collar is positive. -/
  collar_pos : 0 < ε
  /-- The profile is smooth. -/
  contDiff : ContDiff ℝ ∞ h
  /-- Near the exceptional divisor, the profile is `l² + s`. -/
  eq_of_le ⦃s : ℝ⦄ : s ≤ ε ^ 2 → h s = l ^ 2 + s
  /-- Off the collar, the profile is the identity. -/
  eq_of_ge ⦃s : ℝ⦄ : (l + ε) ^ 2 ≤ s → h s = s
  /-- The profile has positive derivative. -/
  deriv_pos (s : ℝ) : 0 < deriv h s

/-- For `0 < l` and `0 < ε`, `blowupProfile l ε` is a profile of the blowup of weight `l` with
collar `ε`. -/
theorem isBlowupProfile_blowupProfile (hl : 0 < l) (hε : 0 < ε) :
    IsBlowupProfile l ε (blowupProfile l ε) :=
  ⟨hl, hε, contDiff_blowupProfile hl hε, fun _ ↦ blowupProfile_of_le hl hε,
    fun _ ↦ blowupProfile_of_ge hl hε, deriv_blowupProfile_pos hl hε⟩

/-- The profiles of the blowup of weight `l` with collar `ε` form a convex set: the two boundary
equations are affine in `h`, and the derivative of a convex combination of profiles is a convex
combination of positive numbers. -/
theorem convex_setOfPred_isBlowupProfile :
    Convex ℝ {h : ℝ → ℝ | IsBlowupProfile l ε h} := by
  intro h₀ hh₀ h₁ hh₁ a b ha hb hab
  have hd₀ := hh₀.contDiff.differentiable (by simp)
  have hd₁ := hh₁.contDiff.differentiable (by simp)
  refine ⟨hh₀.weight_pos, hh₀.collar_pos,
    (hh₀.contDiff.const_smul a).add (hh₁.contDiff.const_smul b), fun s hs ↦ ?_, fun s hs ↦ ?_,
    fun s ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh₀.eq_of_le hs, hh₁.eq_of_le hs]
    linear_combination (l ^ 2 + s) * hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh₀.eq_of_ge hs, hh₁.eq_of_ge hs]
    linear_combination s * hab
  · rw [(((hd₀ s).hasDerivAt.const_smul a).add ((hd₁ s).hasDerivAt.const_smul b)).deriv]
    exact convex_Ioi (0 : ℝ) (hh₀.deriv_pos s) (hh₁.deriv_pos s) ha hb hab

namespace IsBlowupProfile

variable {h : ℝ → ℝ}

/-- A profile of the blowup is strictly increasing. -/
theorem strictMono (hh : IsBlowupProfile l ε h) : StrictMono h :=
  strictMono_of_deriv_pos hh.deriv_pos

/-- A profile of the blowup is positive on `[0, ∞)`: it is increasing, with `h 0 = l²`. -/
theorem pos (hh : IsBlowupProfile l ε h) {s : ℝ} (hs : 0 ≤ s) : 0 < h s := by
  have := hh.strictMono.monotone hs
  rw [hh.eq_of_le (by positivity : (0 : ℝ) ≤ ε ^ 2)] at this
  linarith [pow_pos hh.weight_pos 2]

/-- The integrand `(h u - u - l²) / u` of the correction of a profile is smooth: it vanishes for
`u ≤ ε²`, so near `u = 0`. -/
theorem contDiff_sub_sub_div {k : ℕ∞} (hh : IsBlowupProfile l ε h) :
    ContDiff ℝ k fun u ↦ (h u - u - l ^ 2) / u := by
  refine contDiff_iff_contDiffAt.2 fun u ↦ ?_
  rcases lt_or_ge 0 u with hu | hu
  · exact (((hh.contDiff.of_le (mod_cast le_top)).contDiffAt.sub contDiffAt_id).sub
      contDiffAt_const).div contDiffAt_id hu.ne'
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    have hε2 : u < ε ^ 2 := hu.trans_lt (pow_pos hh.collar_pos 2)
    filter_upwards [Iio_mem_nhds hε2] with v hv
    rw [hh.eq_of_le (le_of_lt hv)]; ring

/-- A convex combination `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`, of profiles of the blowup of
weight `l` with collar `ε` is a profile of the blowup of weight `l` with collar `ε`. -/
theorem one_sub_smul_add_smul {h₀ h₁ : ℝ → ℝ} (hh₀ : IsBlowupProfile l ε h₀)
    (hh₁ : IsBlowupProfile l ε h₁) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsBlowupProfile l ε ((1 - t) • h₀ + t • h₁) :=
  convex_setOfPred_isBlowupProfile hh₀ hh₁ (sub_nonneg.2 ht₁) ht₀ (sub_add_cancel 1 t)

end IsBlowupProfile

/-- The correction `q = profileCorrection l h` of a profile `h` of the blowup of weight `l`:
`q(s) = ∫₀ˢ (h(u) - u - l²) / u du`. For a profile with collar `ε` (`IsBlowupProfile l ε h`),
`q` is smooth (`contDiff_profileCorrection`) and zero on `Iic (ε ^ 2)`
(`profileCorrection_of_le`); it satisfies `s q'(s) = h(s) - s - l²`
(`mul_deriv_profileCorrection`), and `l² log s + q s` is constant for `s ≥ (l + ε)²`
(`sq_mul_log_add_profileCorrection_of_ge`). -/
def profileCorrection (l : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u in 0..s, (h u - u - l ^ 2) / u

theorem profileCorrection_def (l : ℝ) (h : ℝ → ℝ) (s : ℝ) :
    profileCorrection l h s = ∫ u in 0..s, (h u - u - l ^ 2) / u :=
  (rfl)

/-- The integrand `(blowupProfile l ε u - u - l ^ 2) / u` of the correction of `blowupProfile l ε`
is a smooth function of `((l, ε), u)` for `0 < l`, `0 < ε`: it vanishes for `u ≤ ε ^ 2`. -/
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

/-- The correction `profileCorrection l (blowupProfile l ε) s` of `blowupProfile l ε` is a smooth
function of `(l, ε, s)` for `0 < l`, `0 < ε`. -/
theorem contDiffOn_profileCorrection_blowupProfile {n : ℕ∞} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ × ℝ ↦ profileCorrection p.1 (blowupProfile p.1 p.2.1) p.2.2)
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
  exact (h.comp hφ.contDiffOn hm).congr fun p _ ↦ profileCorrection_def _ _ _

variable {h : ℝ → ℝ}

/-- The derivative of the correction `profileCorrection l h` of a profile `h` at `s` is
`(h(s) - s - l²) / s`; at `s = 0` the quotient is `0`, since the integrand vanishes near `0`. -/
theorem hasDerivAt_profileCorrection (hh : IsBlowupProfile l ε h) (s : ℝ) :
    HasDerivAt (profileCorrection l h) ((h s - s - l ^ 2) / s) s :=
  ((hh.contDiff_sub_sub_div (k := 0)).continuous.integral_hasStrictDerivAt 0
    s).hasDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ profileCorrection_def l h s)

/-- The correction of a profile of the blowup is smooth, as the primitive of a smooth
function. -/
theorem contDiff_profileCorrection {k : ℕ∞} (hh : IsBlowupProfile l ε h) :
    ContDiff ℝ k (profileCorrection l h) := by
  rw [show profileCorrection l h = _ from funext (profileCorrection_def l h)]
  exact ((hh.contDiff_sub_sub_div (k := k)).contDiff_add_one_integral 0).of_le le_self_add

/-- The derivative of the correction against the profile: `s q'(s) = h(s) - s - l²` for
`q = profileCorrection l h`. -/
theorem mul_deriv_profileCorrection (hh : IsBlowupProfile l ε h) (s : ℝ) :
    s * deriv (profileCorrection l h) s = h s - s - l ^ 2 := by
  rw [(hasDerivAt_profileCorrection hh s).deriv]
  rcases eq_or_ne s 0 with rfl | hs
  · rw [hh.eq_of_le (by positivity)]; ring
  · exact mul_div_cancel₀ _ hs

/-- Near the exceptional divisor, the correction of a profile vanishes. -/
theorem profileCorrection_of_le (hh : IsBlowupProfile l ε h) {s : ℝ} (hs : s ≤ ε ^ 2) :
    profileCorrection l h s = 0 := by
  rw [profileCorrection_def, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro u hu
  dsimp only
  rw [hh.eq_of_le ((mem_uIcc.1 hu).elim (fun h ↦ h.2.trans hs)
    fun h ↦ h.2.trans (by positivity))]
  ring

/-- Far from the exceptional divisor, `l² log s + profileCorrection l h s` is constant: it takes
its value at `(l + ε)²` for every `s ≥ (l + ε)²`. -/
theorem sq_mul_log_add_profileCorrection_of_ge (hh : IsBlowupProfile l ε h) {s : ℝ}
    (hs : (l + ε) ^ 2 ≤ s) :
    l ^ 2 * Real.log s + profileCorrection l h s =
      l ^ 2 * Real.log ((l + ε) ^ 2) + profileCorrection l h ((l + ε) ^ 2) := by
  have hc : 0 < (l + ε) ^ 2 := by have := hh.weight_pos; have := hh.collar_pos; positivity
  have hs0 : 0 < s := hc.trans_le hs
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun u ↦ (h u - u - l ^ 2) / u) MeasureTheory.volume a b :=
    (hh.contDiff_sub_sub_div (k := 0)).continuous.intervalIntegrable
  have hsplit : profileCorrection l h s = profileCorrection l h ((l + ε) ^ 2) +
      ∫ u in (l + ε) ^ 2..s, (h u - u - l ^ 2) / u := by
    rw [profileCorrection_def, profileCorrection_def,
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have hint : ∫ u in (l + ε) ^ 2..s, (h u - u - l ^ 2) / u =
      ∫ u in (l + ε) ^ 2..s, -l ^ 2 * u⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le hs] at hu
    simp only [hh.eq_of_ge hu.1]
    ring
  rw [hsplit, hint, intervalIntegral.integral_const_mul, integral_inv_of_pos hc hs0,
    Real.log_div hs0.ne' hc.ne']
  ring

/-- The derivative of the correction of a profile vanishes on `Iic (ε ^ 2)`. -/
theorem deriv_profileCorrection_of_le (hh : IsBlowupProfile l ε h) {s : ℝ} (hs : s ≤ ε ^ 2) :
    deriv (profileCorrection l h) s = 0 := by
  rw [(hasDerivAt_profileCorrection hh s).deriv, hh.eq_of_le hs]
  ring

/-- The second derivative of the correction of a profile vanishes on `Iic (ε ^ 2)`, its end point
included. -/
theorem deriv_deriv_profileCorrection_of_le (hh : IsBlowupProfile l ε h) {s : ℝ}
    (hs : s ≤ ε ^ 2) : deriv (deriv (profileCorrection l h)) s = 0 := by
  have hd : Differentiable ℝ (deriv (profileCorrection l h)) :=
    (contDiff_infty_iff_deriv.1 (contDiff_profileCorrection hh)).2.differentiable (by simp)
  have h₀ : HasDerivWithinAt (deriv (profileCorrection l h)) 0 (Iic (ε ^ 2)) s :=
    (hasDerivWithinAt_const s _ 0).congr (fun t ht ↦ deriv_profileCorrection_of_le hh ht)
      (deriv_profileCorrection_of_le hh hs)
  exact (uniqueDiffOn_Iic _ s hs).eq_deriv _ (hd s).hasDerivAt.hasDerivWithinAt h₀

/-- The correction is affine in the profile: for profiles `h₀`, `h₁` of the blowup of weight `l`
(with any collars) and every real `t`, the correction of `(1 - t) • h₀ + t • h₁` is
`(1 - t) • profileCorrection l h₀ + t • profileCorrection l h₁`. -/
theorem profileCorrection_one_sub_smul_add_smul {ε₀ ε₁ : ℝ} {h₀ h₁ : ℝ → ℝ}
    (hh₀ : IsBlowupProfile l ε₀ h₀) (hh₁ : IsBlowupProfile l ε₁ h₁) (t : ℝ) :
    profileCorrection l ((1 - t) • h₀ + t • h₁) =
      (1 - t) • profileCorrection l h₀ + t • profileCorrection l h₁ := by
  funext s
  have hi₀ := (hh₀.contDiff_sub_sub_div (k := 0)).continuous.intervalIntegrable
    (μ := MeasureTheory.volume) 0 s
  have hi₁ := (hh₁.contDiff_sub_sub_div (k := 0)).continuous.intervalIntegrable
    (μ := MeasureTheory.volume) 0 s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, profileCorrection_def]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hi₀.const_mul _) (hi₁.const_mul _)]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  ring

/-! ### The forms `ω̃_{λ,ε}` -/

section ProfileForm

open TauCeti SmoothAlmostComplexStructure TopologicalSpace
open scoped Manifold ContDiff TauCeti.ComplexManifold

variable (n : ℕ)

open Classical in
/-- The correction potential `z ↦ q(|z|²)` on `E = ℂⁿ⁺¹`, for `q = profileCorrection l h` and
`|z|` the Euclidean norm, as a smooth function when `h` is a profile of the blowup of weight `l`
with collar `ε` (`correctionPotential_apply`); it is `0` otherwise. The profile defaults to
`blowupProfile l ε`. -/
noncomputable def correctionPotential (l ε : ℝ) (h : ℝ → ℝ := blowupProfile l ε) :
    C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ :=
  ⟨fun z ↦ if IsBlowupProfile l ε h then
      profileCorrection l h (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) else 0, by
    split_ifs with hh
    · exact ((contDiff_profileCorrection hh).comp
        contDiff_norm_sq_complexToRealEuclidean).contMDiff
    · exact contMDiff_const⟩

open Classical in
theorem coe_correctionPotential (l ε : ℝ) (h : ℝ → ℝ) :
    ⇑(correctionPotential n l ε h) = fun z ↦ if IsBlowupProfile l ε h then
      profileCorrection l h (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) else 0 :=
  (rfl)

/-- For a profile `h` of the blowup, the correction potential is `z ↦ q(|z|²)`. -/
@[simp]
theorem correctionPotential_apply {l ε : ℝ} {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h)
    (z : Fin (n + 1) → ℂ) :
    correctionPotential n l ε h z =
      profileCorrection l h (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) := by
  simp [coe_correctionPotential, hh]

/-- Unless `h` is a profile of the blowup of weight `l` with collar `ε`, the correction potential
is `0`. -/
theorem correctionPotential_of_not {l ε : ℝ} {h : ℝ → ℝ} (hh : ¬IsBlowupProfile l ε h) :
    correctionPotential n l ε h = 0 :=
  ContMDiffMap.ext fun z ↦ by simp [coe_correctionPotential, hh]

/-- The form `ω_q = (1/4) d (J* d φ)` on `E` of the correction potential
`φ = correctionPotential n l ε h`, where `J*` is the structure `a ↦ -a ∘ J` on one-forms of the
complex structure `J` of `E`; by `Dolbeault/Potential.lean` it is `(i/2) ∂∂bar φ`. The profile
defaults to `blowupProfile l ε`. -/
noncomputable def correctionForm (l ε : ℝ) (h : ℝ → ℝ := blowupProfile l ε) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ) :=
  (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
    (SmoothForm.ofFunction (correctionPotential n l ε h))

theorem correctionForm_def (l ε : ℝ) (h : ℝ → ℝ) :
    correctionForm n l ε h =
      (ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).potentialForm
        (SmoothForm.ofFunction (correctionPotential n l ε h)) :=
  (rfl)

/-- The form of the correction potential vanishes at the points of the closed ball of radius `ε`:
by `potentialForm_ofFunction_comp_of_hasDerivAt` its value at `z` is a combination of `q'(|z|²)`
and `q''(|z|²)`, which vanish for `|z|² ≤ ε²`. -/
theorem correctionForm_apply_eq_zero {l ε : ℝ} {h : ℝ → ℝ} {z : Fin (n + 1) → ℂ}
    (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε) :
    (correctionForm n l ε h).val z = 0 := by
  by_cases hh : IsBlowupProfile l ε h
  swap
  · rw [correctionForm_def, correctionPotential_of_not n hh, SmoothForm.ofFunction_zero, map_zero]
    simp
  have hq := contDiff_profileCorrection (k := ⊤) hh
  have hq' := (contDiff_infty_iff_deriv.1 hq).2
  have hq'' := (contDiff_infty_iff_deriv.1 hq').2
  have hs := contDiff_norm_sq_complexToRealEuclidean (ι := Fin (n + 1)) (n := ∞)
  let s : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, hs.contMDiff⟩
  let a : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, (hq'.comp hs).contMDiff⟩
  let b : C^∞⟮𝓘(ℝ, Fin (n + 1) → ℂ), Fin (n + 1) → ℂ; ℝ⟯ := ⟨_, (hq''.comp hs).contMDiff⟩
  have hz2 : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [correctionForm_def,
    potentialForm_ofFunction_comp_of_hasDerivAt (f := s)
      (a := a) (b := b) (fun x ↦ by simp [s, correctionPotential_apply n hh x])
      (fun _ ↦ by simp [a, s]) (fun _ ↦ by simp [b, s])
      (fun _ ↦ (hq.differentiable (by simp) _).hasDerivAt)
      (fun _ ↦ (hq'.differentiable (by simp) _).hasDerivAt)]
  have ha : a z = 0 := by
    simp only [a, ContMDiffMap.coeFn_mk, Function.comp_apply]
    exact deriv_profileCorrection_of_le hh hz2
  have hb : b z = 0 := by
    simp only [b, ContMDiffMap.coeFn_mk, Function.comp_apply]
    exact deriv_deriv_profileCorrection_of_le hh hz2
  simp [ha, hb]

/-- On `E ∖ 0`, the form of the correction potential of a profile `h` is the radial potential
form of `q = profileCorrection l h`: the inclusion is holomorphic, so pulling back commutes with
forms of potentials (`mpullback_potentialForm`). -/
theorem mpullback_subtypeVal_correctionForm {l ε : ℝ} {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    SmoothForm.mpullback (Subtype.val : puncturedSpace (Fin (n + 1) → ℂ) → _) contMDiff_subtypeVal
        (correctionForm n l ε h) =
      radialPotentialForm (Fin (n + 1)) (profileCorrection l h)
        (contDiff_profileCorrection hh).contDiffOn := by
  rw [correctionForm_def, radialPotentialForm_def,
    mpullback_potentialForm _ (isPseudoholomorphic_ofComplexManifold_subtype_val _)]
  congr 1
  refine SmoothBundleForm.ext fun z v ↦ ?_
  rw [SmoothForm.mpullback_apply, SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply,
    SmoothForm.coe_ofFunction, RoughForm.ofFunction_apply, correctionPotential_apply n hh,
    coe_radialPotential]

/-- The form `ω̃_{l,ε} = ω̃_l + π^* ω_q` on the model blowup of the profile `h`, where
`ω̃_l = blowupForm n l`, `π` is the blowdown and `ω_q = correctionForm n l ε h` is the form of the
potential `q(|z|²)` on `E`, for `q = profileCorrection l h`. It is `ω̃_l` on `L(ε)`
(`profileForm_eq_blowupForm_on`), and for a profile `h` of the blowup it is `π^* ω₀` off
`L(l + ε)` (`profileForm_eq_on_compl`). The profile defaults to `blowupProfile l ε`. -/
noncomputable def profileForm (l ε : ℝ) (h : ℝ → ℝ := blowupProfile l ε) :
    SmoothTwoForm 𝓘(ℝ, Fin (n + 1) → ℂ) (BlowupModel n) :=
  blowupForm n l +
    SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
      (correctionForm n l ε h)

theorem profileForm_def (l ε : ℝ) (h : ℝ → ℝ) :
    profileForm n l ε h = blowupForm n l +
      SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
        (correctionForm n l ε h) :=
  (rfl)

/-- On `L(ε) = closedNbhd n ε`, the form `ω̃_{l,ε}` of any `h` is `ω̃_l`, since the correction
potential vanishes to second order there. -/
theorem profileForm_eq_blowupForm_on {l ε : ℝ} {h : ℝ → ℝ} :
    ∀ p ∈ closedNbhd n ε, (profileForm n l ε h).val p = (blowupForm n l).val p := by
  intro p hp
  ext v
  simp [profileForm_def,
    correctionForm_apply_eq_zero n (mem_closedNbhd_iff.1 hp)]

/-- The form `ω_q` of the correction potential is closed: it is a multiple of an exterior
derivative. -/
theorem isClosed_correctionForm (l ε : ℝ) (h : ℝ → ℝ) : (correctionForm n l ε h).IsClosed := by
  rw [correctionForm_def]
  exact isClosed_potentialForm _ _

/-- The form `ω̃_{l,ε}` is closed, as the sum of `ω̃_l` and the pull-back of a closed form. -/
theorem isClosed_profileForm (l ε : ℝ) (h : ℝ → ℝ) : (profileForm n l ε h).IsClosed := by
  rw [profileForm_def]
  exact (isClosed_blowupForm l).add ((isClosed_correctionForm n l ε h).mpullback _ _)

/-- Along the segment `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`, between two profiles of the blowup,
the correction potential is the segment between those of `h₀` and `h₁`. -/
theorem correctionPotential_one_sub_smul_add_smul {l ε : ℝ} {h₀ h₁ : ℝ → ℝ}
    (hh₀ : IsBlowupProfile l ε h₀) (hh₁ : IsBlowupProfile l ε h₁) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    correctionPotential n l ε ((1 - t) • h₀ + t • h₁) =
      (1 - t) • correctionPotential n l ε h₀ + t • correctionPotential n l ε h₁ :=
  ContMDiffMap.ext fun z ↦ by
    simp [correctionPotential_apply n (hh₀.one_sub_smul_add_smul hh₁ ht₀ ht₁),
      correctionPotential_apply n hh₀, correctionPotential_apply n hh₁,
      profileCorrection_one_sub_smul_add_smul hh₀ hh₁ t]

/-- Along the segment `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`, between two profiles of the blowup,
the form `ω_q` of the correction potential is the segment between those of `h₀` and `h₁`, since
the form of a potential is linear in the potential. -/
theorem correctionForm_one_sub_smul_add_smul {l ε : ℝ} {h₀ h₁ : ℝ → ℝ}
    (hh₀ : IsBlowupProfile l ε h₀) (hh₁ : IsBlowupProfile l ε h₁) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    correctionForm n l ε ((1 - t) • h₀ + t • h₁) =
      (1 - t) • correctionForm n l ε h₀ + t • correctionForm n l ε h₁ := by
  rw [correctionForm_def, correctionForm_def, correctionForm_def,
    correctionPotential_one_sub_smul_add_smul n hh₀ hh₁ ht₀ ht₁, SmoothForm.ofFunction_add,
    SmoothForm.ofFunction_smul, SmoothForm.ofFunction_smul, map_add, map_smul, map_smul]

/-- Along the segment `(1 - t) • h₀ + t • h₁`, `t ∈ [0, 1]`, between two profiles of the blowup,
the form `ω̃_{l,ε}` is the segment between those of `h₀` and `h₁`: the form `ω̃_l` does not
depend on the profile, and the correction form is affine in it. -/
theorem profileForm_one_sub_smul_add_smul {l ε : ℝ} {h₀ h₁ : ℝ → ℝ}
    (hh₀ : IsBlowupProfile l ε h₀) (hh₁ : IsBlowupProfile l ε h₁) {t : ℝ} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    profileForm n l ε ((1 - t) • h₀ + t • h₁) =
      (1 - t) • profileForm n l ε h₀ + t • profileForm n l ε h₁ := by
  rw [profileForm_def, profileForm_def, profileForm_def,
    correctionForm_one_sub_smul_add_smul n hh₀ hh₁ ht₀ ht₁, map_add, map_smul, map_smul]
  module

/-- The radial potential `s ↦ s + l² log s + q(s)` of `ω̃_{l,ε}` off the divisor, for
`q = profileCorrection l h`, is smooth on `(0, ∞)`. -/
theorem contDiffOn_add_mul_log_add_profileCorrection {l ε : ℝ} {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h) :
    ContDiffOn ℝ ∞ (fun s ↦ s + l ^ 2 * Real.log s + profileCorrection l h s) (Ioi 0) :=
  (contDiffOn_add_mul_log l).add (contDiff_profileCorrection hh).contDiffOn

/-- On `(0, ∞)`, the radial potential `g(s) = s + l² log s + q(s)` of `ω̃_{l,ε}` has derivative
`h(s) / s`, for a profile `h` of the blowup and `q = profileCorrection l h`. -/
theorem deriv_add_mul_log_add_profileCorrection {l ε : ℝ} {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h) {s : ℝ} (hs : 0 < s) :
    deriv (fun s ↦ s + l ^ 2 * Real.log s + profileCorrection l h s) s = h s / s := by
  have hd : HasDerivAt (fun s ↦ s + l ^ 2 * Real.log s + profileCorrection l h s)
      (1 + l ^ 2 * s⁻¹ + (h s - s - l ^ 2) / s) s :=
    ((hasDerivAt_id s).add ((Real.hasDerivAt_log hs.ne').const_mul _)).add
      (hasDerivAt_profileCorrection hh s)
  rw [hd.deriv]
  field_simp
  ring

/-- Off the exceptional divisor, `ω̃_{l,ε}` is the form of the radial potential
`|z|² + l² log |z|² + q(|z|²)`, for a profile `h` of the blowup and `q = profileCorrection l h`:
its pull-back along the inverse of the blowdown, from `E ∖ 0` to the complement of the divisor,
is `radialPotentialForm` of `s ↦ s + l² log s + q(s)`. -/
theorem mpullback_blowdownDiffeomorph_symm_profileForm {l ε : ℝ} {h : ℝ → ℝ}
    (hh : IsBlowupProfile l ε h) :
    SmoothForm.mpullback (blowdownPuncturedDiffeomorph n).symm
        (blowdownPuncturedDiffeomorph n).symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (profileForm n l ε h)) =
      radialPotentialForm (Fin (n + 1)) (fun s ↦ s + l ^ 2 * Real.log s + profileCorrection l h s)
        (contDiffOn_add_mul_log_add_profileCorrection hh) := by
  rw [profileForm_def, map_add, map_add, mpullback_blowdownDiffeomorph_symm_blowupForm,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_congr _ contMDiff_subtypeVal
      blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
    mpullback_subtypeVal_correctionForm n hh,
    ← radialPotentialForm_add _ (contDiff_profileCorrection hh).contDiffOn]

/-- Off `L(l + ε) = closedNbhd n (l + ε)`, the form `ω̃_{l,ε}` of a profile `h` of the blowup is
`π^* ω₀`: there `l² log s + q(s)` is constant in `s = |z|²`, so the Fubini–Study term of `ω̃_l`
and the correction cancel. -/
theorem profileForm_eq_on_compl {l ε : ℝ} {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    ∀ p ∉ closedNbhd n (l + ε), (profileForm n l ε h).val p =
      (SmoothForm.mpullback blowdown ((contMDiff_blowdown ∞).restrictScalars' ℝ)
        (ω₀E n)).val p := by
  intro p hp
  have hlε : 0 < l + ε := add_pos hh.weight_pos hh.collar_pos
  have hp' : l + ε < ‖complexToRealEuclidean (Fin (n + 1)) p.blowdown‖ :=
    not_le.1 (mt mem_closedNbhd_iff.2 hp)
  have hpU : p ∈ offDivisorOpens n := mem_offDivisorOpens.2 fun h0 ↦ by
    rw [mem_exceptionalDivisor_iff.1 h0, map_zero, norm_zero] at hp'
    exact hlε.not_gt hp'
  refine SmoothForm.apply_eq_of_mpullback_symm_mpullback_subtype_val_apply_eq
    (blowdownPuncturedDiffeomorph n) ⟨p, hpU⟩ ?_
  rw [mpullback_blowdownDiffeomorph_symm_profileForm n hh, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, SmoothForm.mpullback_congr _ contMDiff_subtypeVal
      blowdown_comp_subtypeVal_comp_blowdownPuncturedDiffeomorph_symm,
    ω₀E_def, ← radialPotentialForm_id contDiffOn_id]
  refine SmoothBundleForm.apply_eq_of_eval₂_eq fun v w ↦ ?_
  set x := ∑ i, ‖((blowdownPuncturedDiffeomorph n ⟨p, hpU⟩ : puncturedSpace _) :
    Fin (n + 1) → ℂ) i‖ ^ 2
  have hx : (l + ε) ^ 2 < x := by
    simp only [x, coe_blowdownPuncturedDiffeomorph_apply, ← norm_sq_complexToRealEuclidean]
    exact pow_lt_pow_left₀ hp' hlε.le two_ne_zero
  have he : (fun s ↦ s + l ^ 2 * Real.log s + profileCorrection l h s) =ᶠ[nhds x]
      fun s ↦ s + (l ^ 2 * Real.log ((l + ε) ^ 2) + profileCorrection l h ((l + ε) ^ 2)) := by
    filter_upwards [Ioi_mem_nhds hx] with s hs
    rw [← sq_mul_log_add_profileCorrection_of_ge hh (le_of_lt hs)]
    ring
  rw [radialPotentialForm_apply, radialPotentialForm_apply, he.deriv_eq, he.deriv.deriv_eq]
  simp

/-- The radial map `F_{l,ε} z = √(h(|z|²) / |z|²) z` of a profile `h` of the blowup, composed
with the blowdown, pulls `ω₀` back to `ω̃_{l,ε}` off the exceptional divisor. -/
theorem mpullback_radialMap_profileForm {l ε : ℝ} {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    SmoothForm.mpullback
        (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) ∘ blowdownPuncturedDiffeomorph n)
        ((contMDiff_radialMap hh.contDiff.contDiffOn _).comp
          (blowdownPuncturedDiffeomorph n).contMDiff)
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (ω₀E n)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (profileForm n l ε h) := by
  have hs : ContDiffOn ℝ ∞ h (Ioi 0) := hh.contDiff.contDiffOn
  rw [← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).contMDiff
      (contMDiff_radialMap hs _), ω₀E_def,
    mpullback_radialMap_stdForm (ι := Fin (n + 1)) hs _
      (contDiffOn_add_mul_log_add_profileCorrection hh)
      fun s hs ↦ deriv_add_mul_log_add_profileCorrection hh hs,
    ← mpullback_blowdownDiffeomorph_symm_profileForm n hh, SmoothForm.mpullback_mpullback_symm]

/-- For a profile `h` of the blowup, the form `ω̃_{l,ε}` is Kähler for the complex structure of
the model blowup. Compatibility is checked on two open sets that cover the model, since the
exceptional divisor lies in `openNbhd n ε`: on `openNbhd n ε` the form is `ω̃_l`, which is Kähler
(`isKahler_blowupForm`), and off the divisor it is the pull-back of `ω₀` along `F_{l,ε} ∘ π`
(`mpullback_radialMap_profileForm`), which is Kähler since the profile is positive and
increasing (`isKahler_mpullback_radialMap`), pulled back along the holomorphic map `π`. -/
theorem isKahler_profileForm {l ε : ℝ} {h : ℝ → ℝ} (hh : IsBlowupProfile l ε h) :
    (profileForm n l ε h).IsKahler (ofComplexManifold (Fin (n + 1) → ℂ) (BlowupModel n)) := by
  set V : Opens (BlowupModel n) := openNbhdOpens n ε
  set U : Opens (BlowupModel n) := offDivisorOpens n
  -- On `V`, the form restricts as `ω̃_l` does.
  have hV : SmoothForm.mpullback (Subtype.val : V → BlowupModel n) contMDiff_subtypeVal
      (profileForm n l ε h) =
      SmoothForm.mpullback (Subtype.val : V → BlowupModel n) contMDiff_subtypeVal
        (blowupForm n l) :=
    SmoothBundleForm.ext fun p v ↦ by
      rw [SmoothForm.mpullback_apply, SmoothForm.mpullback_apply,
        profileForm_eq_blowupForm_on n p
          (openNbhd_subset_closedNbhd ε (mem_openNbhdOpens_iff.1 p.property))]
  -- On `U`, it is the pull-back along `π` of a Kähler form on `E ∖ 0`.
  have hU : SmoothTwoForm.Compatible
      (SmoothForm.mpullback (Subtype.val : U → BlowupModel n) contMDiff_subtypeVal
        (profileForm n l ε h)) (ofComplexManifold (Fin (n + 1) → ℂ) U) := by
    rw [← mpullback_radialMap_profileForm n hh,
      ← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).contMDiff, ω₀E_def]
    exact (isKahler_mpullback_radialMap hh.contDiff.contDiffOn _
      fun s _ ↦ hh.deriv_pos s).compatible.mpullback
      isPseudoholomorphic_blowdownPuncturedDiffeomorph _
      fun x ↦ ((blowdownPuncturedDiffeomorph n).isInvertible_mfderiv (x := x) (by simp)).injective
  refine SmoothTwoForm.isKahler_ofComplexManifold_iff.2 ⟨isClosed_profileForm n l ε h,
    SmoothTwoForm.compatible_of_compatible_restrictOpen (fun b : Bool ↦ bif b then V else U)
      (fun p ↦ ?_) (Bool.rec ?_ ?_)⟩
  · by_cases hp : p ∈ openNbhd n ε
    · exact ⟨true, mem_openNbhdOpens_iff.2 hp⟩
    · exact ⟨false, mem_offDivisorOpens.2 fun h ↦
        hp (exceptionalDivisor_subset_openNbhd hh.collar_pos h)⟩
  · dsimp only [Bool.cond_false]
    rw [SmoothAlmostComplexStructure.restrictOpen_ofComplexManifold]
    exact hU
  · dsimp only [Bool.cond_true]
    rw [hV]
    exact (isKahler_blowupForm hh.weight_pos.ne').compatible.restrictOpen V

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
  have hb (t : unitInterval) := isBlowupProfile_blowupProfile (hl0 t) (hε0 t)
  have hq (t : unitInterval) : correctionForm n (l t) (ε t) = (4 : ℝ)⁻¹ •
      mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (SmoothForm.funSMulₗ (a t)
        ((ofComplexManifold (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).covectorComplexStructure
          (mextDerivₗ 𝓘(ℝ, Fin (n + 1) → ℂ) 0 (SmoothForm.ofFunction s)))) := by
    rw [correctionForm_def, potentialForm_def,
      covectorComplexStructure_mextDerivₗ_ofFunction_comp_of_hasDerivAt (f := s) (g' := a t)
        (fun x ↦ correctionPotential_apply n (hb t) x)
        (fun x ↦ hasDerivAt_profileCorrection (hb t) (s x))]
  simp_rw [profileForm_def, blowupForm_def, hq]
  exact ((isSmoothFamily_const _).add ((isSmoothFamily_const _).fun_smul (hl.pow 2))).add
    ((((isSmoothFamily_const _).funSMul_family a ha).mextDeriv.smul _).mpullback _ _)

end ProfileForm

/-! ### The radial map of a profile -/

namespace IsBlowupProfile

open TauCeti

variable {n : ℕ} {h : ℝ → ℝ}

/-- A profile of the blowup of weight `l` maps `(0, ∞)` onto `(l², ∞)`: it is increasing, equal
to `l²` at `0` and to the identity far out. -/
theorem image_Ioi (hh : IsBlowupProfile l ε h) : h '' Ioi 0 = Ioi (l ^ 2) := by
  have h0 : h 0 = l ^ 2 := by rw [hh.eq_of_le (by positivity)]; ring
  ext t
  refine ⟨?_, fun ht ↦ ?_⟩
  · rintro ⟨s, hs, rfl⟩
    exact h0 ▸ hh.strictMono hs
  · rw [mem_Ioi] at ht
    have hs₁ : h (max t ((l + ε) ^ 2)) = max t ((l + ε) ^ 2) := hh.eq_of_ge (le_max_right _ _)
    have hpos : 0 < max t ((l + ε) ^ 2) :=
      lt_max_of_lt_left ((sq_nonneg l).trans_lt ht)
    obtain ⟨s, hs, hst⟩ := intermediate_value_Ioc hpos.le hh.contDiff.continuous.continuousOn
      ⟨by rw [h0]; exact ht, by rw [hs₁]; exact le_max_left _ _⟩
    exact ⟨s, hs.1, hst⟩

variable (n) in
/-- The radial map `F_h z = √(h(|z|²) / |z|²) z` of a profile `h` of the blowup of weight `l`, as
a diffeomorphism of `E ∖ 0` onto the complement of the closed ball `|w| ≤ l`. -/
abbrev radialDiffeomorph (hh : IsBlowupProfile l ε h) :=
  radialMapDiffeomorph (Fin (n + 1)) h hh.contDiff.contDiffOn (fun _ hs ↦ hh.pos (le_of_lt hs))
    fun s _ ↦ hh.deriv_pos s

/-- The shell of a profile of the blowup of weight `l` is the complement of the closed ball of
radius `l`. -/
theorem mem_radialShell_iff (hh : IsBlowupProfile l ε h) {w : Fin (n + 1) → ℂ} :
    w ∈ radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s) ↔
      l < ‖complexToRealEuclidean (Fin (n + 1)) w‖ := by
  rw [mem_radialShell, ← norm_sq_complexToRealEuclidean, hh.image_Ioi, mem_Ioi,
    pow_lt_pow_iff_left₀ hh.weight_pos.le (norm_nonneg _) two_ne_zero]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` is the identity on
`|z| ≥ l + ε`. -/
theorem radialMap_of_le (hh : IsBlowupProfile l ε h) {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖) :
    radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z = z := by
  have hz0 := norm_sq_complexToRealEuclidean_pos z
  refine Subtype.ext ?_
  rw [radialMap_apply, ← norm_sq_complexToRealEuclidean,
    hh.eq_of_ge (pow_le_pow_left₀ (by linarith [hh.weight_pos, hh.collar_pos]) hz 2),
    div_self hz0.ne', Real.sqrt_one, one_smul]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` is the radial map
`F_l z = √(1 + l² / |z|²) z` of the model on `|z| ≤ ε`. -/
theorem radialMap_of_le_collar (hh : IsBlowupProfile l ε h)
    {z : puncturedSpace (Fin (n + 1) → ℂ)} (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ ≤ ε) :
    radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z =
      radialMap (fun s ↦ s + l ^ 2) (fun _ hs ↦ add_pos_of_pos_of_nonneg hs (sq_nonneg l)) z := by
  refine Subtype.ext ?_
  rw [radialMap_apply, radialMap_apply, ← norm_sq_complexToRealEuclidean,
    hh.eq_of_le (pow_le_pow_left₀ (norm_nonneg _) hz 2), add_comm (l ^ 2)]

/-- The radial map of a profile of the blowup of weight `l` with collar `ε` maps the open ball of
radius `r > l + ε` into itself. -/
theorem norm_radialMap_lt (hh : IsBlowupProfile l ε h) {r : ℝ} (hr : l + ε < r)
    {z : puncturedSpace (Fin (n + 1) → ℂ)} (hz : ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r) :
    ‖complexToRealEuclidean (Fin (n + 1)) (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z)‖ <
      r := by
  have hle : 0 ≤ l + ε := by linarith [hh.weight_pos, hh.collar_pos]
  by_cases hzle : l + ε ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖
  · rwa [hh.radialMap_of_le hzle]
  · refine (pow_lt_pow_iff_left₀ (norm_nonneg _) (hle.trans hr.le) two_ne_zero).1 ?_
    rw [norm_radialMap]
    calc h (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) < h ((l + ε) ^ 2) :=
          hh.strictMono (pow_lt_pow_left₀ (not_le.1 hzle) (norm_nonneg _) two_ne_zero)
      _ = (l + ε) ^ 2 := hh.eq_of_ge le_rfl
      _ < r ^ 2 := pow_lt_pow_left₀ hr hle two_ne_zero

/-- For `l + ε < r`, a point `z ≠ 0` whose image under the radial map of `h` lies in the open ball
of radius `r` lies in it too: off `B(l + ε)` the radial map is the identity. -/
theorem norm_lt_of_norm_radialMap_lt (hh : IsBlowupProfile l ε h) {r : ℝ} (hr : l + ε < r)
    {z : puncturedSpace (Fin (n + 1) → ℂ)}
    (hz : ‖complexToRealEuclidean (Fin (n + 1))
      (radialMap h (fun _ hs ↦ hh.pos (le_of_lt hs)) z)‖ < r) :
    ‖complexToRealEuclidean (Fin (n + 1)) z‖ < r := by
  by_contra hle
  rw [hh.radialMap_of_le (hr.le.trans (not_lt.1 hle))] at hz
  exact hle hz

/-- For `l + ε < r`, the inverse of `radialDiffeomorph` maps the points of the shell in the open
ball of radius `r` into that ball. -/
theorem norm_radialDiffeomorph_symm_lt (hh : IsBlowupProfile l ε h) {r : ℝ} (hr : l + ε < r)
    {w : radialShell (Fin (n + 1)) h hh.contDiff.contDiffOn (fun s _ ↦ hh.deriv_pos s)}
    (hw : ‖complexToRealEuclidean (Fin (n + 1)) w‖ < r) :
    ‖complexToRealEuclidean (Fin (n + 1)) ((hh.radialDiffeomorph n).symm w)‖ < r :=
  hh.norm_lt_of_norm_radialMap_lt hr (by rwa [coe_radialMap_radialMapDiffeomorph_symm_apply])

end IsBlowupProfile

end SymplecticGeometry.BlowupModel

end
