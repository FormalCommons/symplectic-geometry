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
import SymplecticGeometry.Analysis.Calculus.ContDiff.AddSumRangeSmulSub
import SymplecticGeometry.Analysis.Calculus.FDeriv.AddSmulSub
import SymplecticGeometry.Analysis.Normed.Operator.Pi

/-!
# Holonomic approximation along a zig-zag: cutoffs at the crossings and gluing

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

When consecutive crossings are at least `4 w` apart, near the curve within `w` of the crossing
`c i` every cutoff but the `i`-th is locally `0` or `1`. The chain glued by the cutoffs is then
locally the two-term interpolation of `S i` and `S (i + 1)`, which
`SymplecticGeometry.norm_add_smul_sub_sub_le_max` and
`SymplecticGeometry.norm_fderiv_add_smul_sub_sub_le` estimate.

## Main results

* `SymplecticGeometry.exists_zigzag_cutoffs`: the cutoffs at the crossings of a zig-zag profile.
* `SymplecticGeometry.exists_zigzag_chain`: smooth maps `S 0, …, S (n + 1)` glued along the
  curve by these cutoffs, as `S 0 + ∑ φ l • (S (l + 1) - S l)`, with the glued map equal to `S l`
  near the points of the curve between the crossings and estimated against `S i` and `S (i + 1)`
  near the crossing `c i`.

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

/-- **Gluing sections along a zig-zag.** Let `g` change sign at the points `c 0, …, c n`, spaced
at least `4 w` apart, as in `exists_zigzag_cutoffs`, and let `S 0, …, S (n + 1)` be smooth maps
on `D = (Fin m → ℝ) × (Fin k → ℝ)`. There is a smooth map `f'` such that, at each point
`x = (u, r g (u i₀) eⱼ)` of the curve:

* if `u i₀` is at least `w` above the crossings before `l` and at least `w` below the others,
  then `f'` equals `S l` near `x`;
* if `u i₀` is within `w` of the crossing `c i`, then `f' x` is at most as far from any `A` as the
  farther of `S i x` and `S (i + 1) x`, and `D f' (x)` is at most as far from any `B` as the
  farther of `D (S i) (x)` and `D (S (i + 1)) (x)`, plus `(3 / r) ‖S (i + 1) x - S i x‖`. -/
theorem exists_zigzag_chain (i₀ : Fin m) (j : Fin k) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ → ℝ} {n : ℕ} {c : Fin (n + 1) → ℝ} {w r : ℝ}
    (hw : 0 < w) (hr : 0 < r) (hc : ∀ i : Fin n, c i.castSucc + 4 * w ≤ c i.succ)
    (hg : ∀ i : Fin (n + 1), ∀ t, w ≤ |t - c i| → |t - c i| ≤ 2 * w →
      1 / 2 ≤ (-1) ^ (i : ℕ) * SignType.sign (t - c i) * g t)
    {S : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → F} (hS : ∀ l ≤ n + 1, ContDiff ℝ ∞ (S l)) :
    ∃ f' : (Fin m → ℝ) × (Fin k → ℝ) → F, ContDiff ℝ ∞ f' ∧
      ∀ u : Fin m → ℝ,
        (∀ l ≤ n + 1, (∀ i : Fin (n + 1), (i : ℕ) < l → c i + w ≤ u i₀) →
          (∀ i : Fin (n + 1), l ≤ (i : ℕ) → u i₀ ≤ c i - w) →
          f' =ᶠ[𝓝 (u, Pi.single j (r * g (u i₀)))] S l) ∧
        ∀ i : Fin (n + 1), |u i₀ - c i| < w → ∀ (A : F) (B : _ →L[ℝ] F),
          let x := (u, Pi.single j (r * g (u i₀)))
          ‖f' x - A‖ ≤ max ‖S i x - A‖ ‖S ((i : ℕ) + 1) x - A‖ ∧
          ‖fderiv ℝ f' x - B‖ ≤ max ‖fderiv ℝ (S i) x - B‖ ‖fderiv ℝ (S ((i : ℕ) + 1)) x - B‖ +
            3 / r * ‖S ((i : ℕ) + 1) x - S i x‖ := by
  obtain ⟨φ, hφ, hφ01, hφx⟩ := exists_zigzag_cutoffs i₀ j hw hr hg
  -- The cutoffs, extended by `0` past `n`.
  obtain ⟨ψ, hψφ, hψ0⟩ : ∃ ψ : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → ℝ,
      (∀ i : Fin (n + 1), ψ i = φ i) ∧ ∀ l, n + 1 ≤ l → ψ l = 0 :=
    ⟨fun l ↦ if h : l < n + 1 then φ ⟨l, h⟩ else 0, fun i ↦ dite_eq_left i.isLt,
      fun l hl ↦ dite_eq_right (by omega)⟩
  refine ⟨fun y ↦ S 0 y + ∑ l ∈ Finset.range (n + 1), ψ l y • (S (l + 1) y - S l y),
    .add_sum_range_smul_sub hS fun l hl ↦ ?_, fun u ↦ ?_⟩
  · simpa only [hψφ ⟨l, hl⟩] using hφ ⟨l, hl⟩
  set x : (Fin m → ℝ) × (Fin k → ℝ) := (u, Pi.single j (r * g (u i₀)))
  -- Near `x`, the cutoffs before `l` are `1` and those after it are `0`.
  have hcut : ∀ l : ℕ, (∀ i : Fin (n + 1), (i : ℕ) < l → c i + w ≤ u i₀) →
      (∀ i : Fin (n + 1), l < (i : ℕ) → u i₀ ≤ c i - w) →
      ∀ᶠ y in 𝓝 x, (∀ l' < l, l' < n + 1 → ψ l' y = 1) ∧ ∀ l', l < l' → ψ l' y = 0 := by
    intro l h₁ h₀
    have e : ∀ᶠ y in 𝓝 x, ∀ i : Fin (n + 1),
        ((i : ℕ) < l → ψ i y = 1) ∧ (l < (i : ℕ) → ψ i y = 0) := by
      refine eventually_all.2 fun i ↦ ?_
      rcases lt_trichotomy (i : ℕ) l with hi | hi | hi
      · filter_upwards [(hφx i u).2.2 (h₁ i hi)] with y hy
        exact ⟨fun _ ↦ by rw [hψφ, hy, Pi.one_apply], fun h ↦ absurd hi (by omega)⟩
      · exact .of_forall fun y ↦ ⟨fun h ↦ absurd h (by omega), fun h ↦ absurd h (by omega)⟩
      · filter_upwards [(hφx i u).2.1 (h₀ i hi)] with y hy
        exact ⟨fun h ↦ absurd hi (by omega), fun _ ↦ by rw [hψφ, hy, Pi.zero_apply]⟩
    filter_upwards [e] with y hy
    refine ⟨fun l' hl' hn ↦ (hy ⟨l', hn⟩).1 hl', fun l' hl' ↦ ?_⟩
    by_cases hn : l' < n + 1
    · exact (hy ⟨l', hn⟩).2 hl'
    · rw [hψ0 l' (by omega), Pi.zero_apply]
  refine ⟨fun l hl h₁ h₀ ↦ ?_, fun i hi A B ↦ ?_⟩
  · -- Away from the windows.
    have hev := hcut l h₁ fun i hi ↦ h₀ i hi.le
    rcases hl.lt_or_eq with hl | rfl
    · have hl0 : ∀ᶠ y in 𝓝 x, ψ l y = 0 := by
        filter_upwards [(hφx ⟨l, hl⟩ u).2.1 (h₀ ⟨l, hl⟩ le_rfl)] with y hy
        rw [hψφ ⟨l, hl⟩, hy, Pi.zero_apply]
      filter_upwards [Filter.eventuallyEq_add_sum_range_smul_sub_of_lt (S := S) hl
        (hev.mono fun y hy ↦ ⟨fun l' hl' ↦ hy.1 l' hl' (by omega), fun l' hl' _ ↦ hy.2 l' hl'⟩),
        hl0] with y hy hy0
      rw [hy, hy0, zero_smul, add_zero]
    · exact Filter.eventuallyEq_add_sum_range_smul_sub_right
        (hev.mono fun y hy l' hl' ↦ hy.1 l' hl' hl')
  · -- In the window of `c i`, the other crossings are at least `3 w` away.
    have hi' := abs_lt.1 hi
    have h4 : (0 : ℝ) ≤ 4 * w := by positivity
    have : IsTrans ℝ (· + 4 * w ≤ ·) :=
      ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans ((le_add_of_nonneg_right h4).trans h₂)⟩
    have hc' := (Fin.liftFun_iff_succ (· + 4 * w ≤ ·)).2 hc
    have hev := hcut i (fun i' h ↦ by linarith [hc' (Fin.lt_def.2 h)])
      (fun i' h ↦ by linarith [hc' (Fin.lt_def.2 h)])
    have heq := Filter.eventuallyEq_add_sum_range_smul_sub_of_lt (S := S) i.isLt
      (hev.mono fun y hy ↦ ⟨fun l' hl' ↦ hy.1 l' hl' (by omega), fun l' hl' _ ↦ hy.2 l' hl'⟩)
    have h01 := hφ01 i x
    have hdi : ∀ l ≤ n + 1, DifferentiableAt ℝ (S l) x := fun l hl ↦
      ((hS l hl).differentiable (by simp)).differentiableAt
    refine ⟨?_, ?_⟩
    · refine (congrArg (‖· - A‖) heq.eq_of_nhds).trans_le ?_
      rw [hψφ]
      exact norm_add_smul_sub_sub_le_max _ _ _ h01.1 h01.2
    · rw [heq.fderiv_eq, hψφ]
      exact norm_fderiv_add_smul_sub_sub_le B (hdi i (by omega)) (hdi (i + 1) (by omega))
        (((hφ i).differentiable (by simp)).differentiableAt) h01.1 h01.2 (hφx i u).1

end SymplecticGeometry

end
