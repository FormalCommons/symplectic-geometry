/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothedMax
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
`h = blowupProfile l ε` (which is `0` at `s = 0`). -/
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

end SymplecticGeometry.BlowupModel

end
