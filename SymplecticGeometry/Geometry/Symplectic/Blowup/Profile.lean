/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
import Mathlib.Analysis.Calculus.Deriv.MeanValue

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

end SymplecticGeometry.BlowupModel

end
