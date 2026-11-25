/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Analysis.Normed.Operator.Pi

/-!
# Holonomic approximation along a zig-zag: cutoffs at the crossings

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, fix a core coordinate `i₀` and a transverse
coordinate `j`. Let `g` be a zig-zag profile with crossings at `c 0 < ⋯ < c n` and width `w`, as
`SymplecticGeometry.exists_zigzag_profile` gives, and consider the curve
`u ↦ (u, r g (u i₀) eⱼ)`, the other core coordinates being parameters. To chain Taylor sections
along this curve, as in [EliashbergMishachev2002], §3.2, one needs one cutoff for each crossing: a
smooth function on `D` with values in `[0, 1]` that is `0` near the curve before the crossing and
`1` near it after.

The point of the construction is that, at the points of the curve, the derivative of each cutoff
is at most `3 / r`, a bound that depends neither on the profile nor on its width: the cutoff
switches in the transverse direction, where the curve crosses a band of height `r / 2`, and not
along the core direction, where the crossings may be as close together as wanted.

The cutoff at a crossing `c` of sign `σ = ± 1` is
`βR (u i₀) + (1 - βR (u i₀)) βL (u i₀) μ (-σ vⱼ / r)`, where `βL` and `βR` are smooth steps in
`u i₀` rising on `[c - 2 w, c - w]` and on `[c + w, c + 2 w]`, and `μ` is a smooth antitone step
from `1` to `0` on `[-1/4, 1/4]` with derivative at most `3`
(`TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`). This explicit formula is the
library's own.

## Main results

* `SymplecticGeometry.exists_zigzag_cutoffs`: the cutoffs at the crossings of a zig-zag profile.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Filter Set
open scoped Topology ContDiff

namespace SymplecticGeometry

variable {m k : ℕ}

/-- The smooth ramp in `t` that rises from `0` at `t = a` to `1` at `t = a + w`. -/
private noncomputable def ramp (w a t : ℝ) : ℝ := Real.smoothTransition ((t - a) / w)

private theorem ramp_of_le {w a t : ℝ} (hw : 0 < w) (h : t ≤ a) : ramp w a t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)

private theorem ramp_of_ge {w a t : ℝ} (hw : 0 < w) (h : a + w ≤ t) : ramp w a t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div hw).2 (by linarith))

private theorem contDiff_ramp (w a : ℝ) : ContDiff ℝ ∞ (ramp w a) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)

/-- The cutoff at the crossing `c` of width `w`, built from a transverse step `μ ∘ ℓ`: it is `0`
before the left ramp, `μ ∘ ℓ` between the two ramps and `1` after the right ramp. -/
private noncomputable def cutoff (i₀ : Fin m) (μ : ℝ → ℝ)
    (ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ) (c w : ℝ) (y : (Fin m → ℝ) × (Fin k → ℝ)) : ℝ :=
  ramp w (c + w) (y.1 i₀) + (1 - ramp w (c + w) (y.1 i₀)) * ramp w (c - 2 * w) (y.1 i₀) * μ (ℓ y)

/-- Before the crossing the cutoff vanishes near `x`: either `x` lies before the left ramp, or the
transverse step vanishes near `x`. -/
private theorem cutoff_eventuallyEq_zero (i₀ : Fin m) {μ : ℝ → ℝ}
    {ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ} {c w : ℝ} (hw : 0 < w)
    (hμ : ∀ s, 1 / 4 ≤ s → μ s = 0) {x : (Fin m → ℝ) × (Fin k → ℝ)} (hx : x.1 i₀ ≤ c - w)
    (hℓ : c - 2 * w ≤ x.1 i₀ → 1 / 4 < ℓ x) :
    cutoff i₀ μ ℓ c w =ᶠ[𝓝 x] 0 := by
  have hcore : Tendsto (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀) (𝓝 x) (𝓝 (x.1 i₀)) :=
    (by fun_prop : Continuous fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀).tendsto x
  rcases lt_or_ge (x.1 i₀) (c - 2 * w) with hx' | hx'
  · filter_upwards [hcore.eventually (gt_mem_nhds hx')] with y hy
    simp [cutoff, ramp_of_le hw (by linarith : y.1 i₀ ≤ c + w), ramp_of_le hw hy.le]
  · filter_upwards [hcore.eventually (gt_mem_nhds (by linarith : x.1 i₀ < c + w)),
      (ℓ.continuous.tendsto x).eventually (lt_mem_nhds (hℓ hx'))] with y hy hy'
    simp [cutoff, ramp_of_le hw hy.le, hμ _ hy'.le]

/-- After the crossing the cutoff is `1` near `x`: either `x` lies after the right ramp, or the
transverse step is `1` near `x`. -/
private theorem cutoff_eventuallyEq_one (i₀ : Fin m) {μ : ℝ → ℝ}
    {ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ} {c w : ℝ} (hw : 0 < w)
    (hμ : ∀ s, s ≤ -1 / 4 → μ s = 1) {x : (Fin m → ℝ) × (Fin k → ℝ)} (hx : c + w ≤ x.1 i₀)
    (hℓ : x.1 i₀ ≤ c + 2 * w → ℓ x < -1 / 4) :
    cutoff i₀ μ ℓ c w =ᶠ[𝓝 x] 1 := by
  have hcore : Tendsto (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀) (𝓝 x) (𝓝 (x.1 i₀)) :=
    (by fun_prop : Continuous fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀).tendsto x
  rcases lt_or_ge (c + 2 * w) (x.1 i₀) with hx' | hx'
  · filter_upwards [hcore.eventually (lt_mem_nhds hx')] with y hy
    simp [cutoff, ramp_of_ge hw (by linarith : c + w + w ≤ y.1 i₀)]
  · filter_upwards [hcore.eventually (lt_mem_nhds (by linarith : c - w < x.1 i₀)),
      (ℓ.continuous.tendsto x).eventually (gt_mem_nhds (hℓ hx'))] with y hy hy'
    simp [cutoff, ramp_of_ge hw (by linarith : c - 2 * w + w ≤ y.1 i₀), hμ _ hy'.le]

/-- Between the two ramps the cutoff is the transverse step `μ ∘ ℓ`. -/
private theorem cutoff_eventuallyEq_comp (i₀ : Fin m) (μ : ℝ → ℝ)
    (ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ) {c w : ℝ} (hw : 0 < w)
    {x : (Fin m → ℝ) × (Fin k → ℝ)} (hx : c - w < x.1 i₀) (hx' : x.1 i₀ < c + w) :
    cutoff i₀ μ ℓ c w =ᶠ[𝓝 x] μ ∘ ℓ := by
  have hcore : Tendsto (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀) (𝓝 x) (𝓝 (x.1 i₀)) :=
    (by fun_prop : Continuous fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀).tendsto x
  filter_upwards [hcore.eventually (lt_mem_nhds hx), hcore.eventually (gt_mem_nhds hx')]
    with y hy hy'
  simp [cutoff, ramp_of_le hw hy'.le, ramp_of_ge hw (by linarith : c - 2 * w + w ≤ y.1 i₀)]

/-- The transverse coordinate `vⱼ`, scaled by `-σ / r` with `|σ| = 1`, has operator norm at most
`1 / r` in the sup norm. -/
private theorem norm_transverse_le (j : Fin k) {σ r : ℝ} (hσ : |σ| = 1) (hr : 0 < r) :
    ‖(-(σ / r)) • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k ↦ ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin k → ℝ)))‖ ≤ 1 / r := by
  have hcomp : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k ↦ ℝ) j).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin k → ℝ))‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (ContinuousLinearMap.norm_proj_le j) (ContinuousLinearMap.norm_snd_le ..)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hσr : ‖-(σ / r)‖ = 1 / r := by
    rw [norm_neg, norm_div, Real.norm_eq_abs, hσ, Real.norm_of_nonneg hr.le]
  rw [norm_smul, hσr]
  exact mul_le_of_le_one_right (by positivity) hcomp

/-- The cutoff at one crossing `c` of sign `σ`, with `|σ| = 1`. -/
private theorem exists_zigzag_cutoff (i₀ : Fin m) (j : Fin k) {g : ℝ → ℝ} {σ c w r : ℝ}
    (hσ : |σ| = 1) (hw : 0 < w) (hr : 0 < r)
    (hg : ∀ t, w ≤ |t - c| → |t - c| ≤ 2 * w → 1 / 2 ≤ σ * SignType.sign (t - c) * g t) :
    ∃ φ : (Fin m → ℝ) × (Fin k → ℝ) → ℝ, ContDiff ℝ ∞ φ ∧ (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      ∀ u : Fin m → ℝ,
        ‖fderiv ℝ φ (u, Pi.single j (r * g (u i₀)))‖ ≤ 3 / r ∧
        (u i₀ ≤ c - w → φ =ᶠ[𝓝 (u, Pi.single j (r * g (u i₀)))] 0) ∧
        (c + w ≤ u i₀ → φ =ᶠ[𝓝 (u, Pi.single j (r * g (u i₀)))] 1) := by
  -- The transverse step `μ`: antitone, `1` on `(-∞, -1/4]`, `0` on `[1/4, ∞)`, `|μ'| ≤ 3`.
  obtain ⟨μ, hμ, hμanti, hμ0, hμb, hμa, hμd, -⟩ :=
    TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le (a := -1 / 4) (b := 1 / 4) (v := 1)
      (τ := 3) (by norm_num) zero_le_one (by norm_num)
  have hμ1 : ∀ s, μ s ≤ 1 := fun s ↦ by
    rcases le_total s (-1 / 4) with hs | hs
    · exact (hμa s hs).le
    · exact (hμanti hs).trans (hμa _ le_rfl).le
  -- The scaled transverse coordinate `ℓ (u, v) = -σ vⱼ / r`.
  set ℓ : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ :=
    (-(σ / r)) • ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin k → ℝ))) with hℓ
  have hℓ_apply : ∀ y, ℓ y = -(σ / r) * y.2 j := fun y ↦ by simp [hℓ]
  refine ⟨cutoff i₀ μ ℓ c w, ?_, fun y ↦ ?_, fun u ↦ ?_⟩
  -- Smoothness.
  · have h0 : ContDiff ℝ ∞ fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ y.1 i₀ := by fun_prop
    exact ((contDiff_ramp _ _).comp h0).add ((((contDiff_const.sub
      ((contDiff_ramp _ _).comp h0)).mul ((contDiff_ramp _ _).comp h0))).mul
      (hμ.comp ℓ.contDiff))
  -- Values in `[0, 1]`.
  · have a0 := Real.smoothTransition.nonneg ((y.1 i₀ - (c + w)) / w)
    have a1 := Real.smoothTransition.le_one ((y.1 i₀ - (c + w)) / w)
    have b0 := Real.smoothTransition.nonneg ((y.1 i₀ - (c - 2 * w)) / w)
    have b1 := Real.smoothTransition.le_one ((y.1 i₀ - (c - 2 * w)) / w)
    have m0 := hμ0 (ℓ y)
    have m1 := hμ1 (ℓ y)
    simp only [cutoff, ramp]
    constructor
    · have := mul_nonneg (mul_nonneg (sub_nonneg.2 a1) b0) m0
      linarith
    · have hbm := mul_le_mul b1 m1 m0 zero_le_one
      have := mul_le_of_le_one_right (sub_nonneg.2 a1) (hbm.trans_eq (one_mul 1))
      rw [mul_assoc]
      linarith
  -- On the curve `ℓ x = -σ g (u i₀)`, which the crossing hypothesis bounds on the ramps.
  set x : (Fin m → ℝ) × (Fin k → ℝ) := (u, Pi.single j (r * g (u i₀))) with hx
  have hℓx : ℓ x = -(σ * g (u i₀)) := by
    rw [hℓ_apply, hx]
    simp only [Pi.single_eq_same]
    field_simp
  have hleft : u i₀ ≤ c - w → cutoff i₀ μ ℓ c w =ᶠ[𝓝 x] 0 := fun hu ↦
    cutoff_eventuallyEq_zero i₀ hw hμb hu fun hu' ↦ by
      have hs := hg (u i₀) (by rw [abs_of_neg (by linarith)]; linarith)
        (by rw [abs_of_neg (by linarith)]; linarith)
      rw [sign_neg (by linarith : u i₀ - c < 0)] at hs
      simp only [SignType.coe_neg, SignType.coe_one, mul_neg, mul_one] at hs
      rw [hℓx]; linarith
  have hright : c + w ≤ u i₀ → cutoff i₀ μ ℓ c w =ᶠ[𝓝 x] 1 := fun hu ↦
    cutoff_eventuallyEq_one i₀ hw hμa hu fun hu' ↦ by
      have hs := hg (u i₀) (by rw [abs_of_pos (by linarith)]; linarith)
        (by rw [abs_of_pos (by linarith)]; linarith)
      rw [sign_pos (by linarith : 0 < u i₀ - c)] at hs
      simp only [SignType.coe_one, mul_one] at hs
      rw [hℓx]; linarith
  refine ⟨?_, hleft, hright⟩
  -- The derivative: `0` where the cutoff is locally constant, `μ' (ℓ x) • ℓ` in the middle.
  have hr3 : 0 ≤ 3 / r := by positivity
  rcases le_or_gt (u i₀) (c - w) with hu | hu
  · rw [(hleft hu).fderiv_eq]; simpa using hr3
  rcases le_or_gt (c + w) (u i₀) with hu' | hu'
  · rw [(hright hu').fderiv_eq]; simpa using hr3
  have hd : HasFDerivAt (μ ∘ ℓ) (deriv μ (ℓ x) • ℓ) x :=
    ((hμ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt x ℓ.hasFDerivAt
  rw [(cutoff_eventuallyEq_comp i₀ μ ℓ hw hu hu').fderiv_eq, hd.fderiv, norm_smul]
  calc ‖deriv μ (ℓ x)‖ * ‖ℓ‖ ≤ 3 * (1 / r) :=
        mul_le_mul (hμd _) (norm_transverse_le j hσ hr) (norm_nonneg _) (by norm_num)
    _ = 3 / r := by ring

/-- **Cutoffs at the crossings of a zig-zag profile.** Let `g : ℝ → ℝ` change sign near the points
`c 0, …, c n`, in the sense that `(-1) ^ i sign (t - c i) g t ≥ 1/2` whenever
`w ≤ |t - c i| ≤ 2 w`, and let `r > 0`. Fix a core coordinate `i₀` and a transverse coordinate
`j`, and consider the points `(u, r g (u i₀) eⱼ)` of `(Fin m → ℝ) × (Fin k → ℝ)`. There are smooth
functions `φ i` with values in `[0, 1]` such that, at each such point `x`, `‖D φ i (x)‖ ≤ 3 / r`,
`φ i` vanishes near `x` if `u i₀ ≤ c i - w`, and `φ i` equals `1` near `x` if `c i + w ≤ u i₀`.

The bound `3 / r` depends neither on `g`, nor on the points `c i`, nor on the width `w`. -/
theorem exists_zigzag_cutoffs (i₀ : Fin m) (j : Fin k) {g : ℝ → ℝ} {n : ℕ}
    {c : Fin (n + 1) → ℝ} {w r : ℝ} (hw : 0 < w) (hr : 0 < r)
    (hg : ∀ i : Fin (n + 1), ∀ t, w ≤ |t - c i| → |t - c i| ≤ 2 * w →
      1 / 2 ≤ (-1) ^ (i : ℕ) * SignType.sign (t - c i) * g t) :
    ∃ φ : Fin (n + 1) → (Fin m → ℝ) × (Fin k → ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1) ∧
      ∀ i (u : Fin m → ℝ),
        ‖fderiv ℝ (φ i) (u, Pi.single j (r * g (u i₀)))‖ ≤ 3 / r ∧
        (u i₀ ≤ c i - w → φ i =ᶠ[𝓝 (u, Pi.single j (r * g (u i₀)))] 0) ∧
        (c i + w ≤ u i₀ → φ i =ᶠ[𝓝 (u, Pi.single j (r * g (u i₀)))] 1) := by
  choose φ hφ hφ01 hφx using fun i : Fin (n + 1) ↦
    exists_zigzag_cutoff i₀ j (σ := (-1) ^ (i : ℕ)) (by simp) hw hr (hg i)
  exact ⟨φ, hφ, hφ01, hφx⟩

end SymplecticGeometry

end
