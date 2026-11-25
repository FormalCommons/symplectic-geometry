/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Holonomic approximation along a zig-zag: cutoffs at the crossings

In the coordinates of `SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic`, on
`D = (Fin 1 → ℝ) × (Fin k → ℝ)` with sup norms, let `g` be a zig-zag profile with crossings at
`c 0 < ⋯ < c n` and width `w`, as `SymplecticGeometry.exists_zigzag_profile` gives, and consider
the curve `u ↦ (u, r g (u 0) eⱼ)`. To chain Taylor sections along this curve, as in
[EliashbergMishachev2002], §3.2, one needs one cutoff for each crossing: a smooth function on `D`
with values in `[0, 1]` that is `0` near the curve before the crossing and `1` near it after.

The point of the construction is that, at the points of the curve, the derivative of each cutoff
is at most `3 / r`, a bound that depends neither on the profile nor on its width: the cutoff
switches in the transverse direction, where the curve crosses a band of height `r / 2`, and not
along the core direction, where the crossings may be as close together as wanted.

The cutoff at a crossing `c` of sign `σ = ± 1` is
`βR (u 0) + (1 - βR (u 0)) βL (u 0) μ (-σ vⱼ / r)`, where `βL` and `βR` are smooth steps in `u 0`
rising on `[c - 2 w, c - w]` and on `[c + w, c + 2 w]`, and `μ` is a smooth antitone step from `1`
to `0` on `[-1/4, 1/4]` with derivative at most `3`
(`TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`).

## Main results

* `SymplecticGeometry.exists_zigzag_cutoffs`: the cutoffs at the crossings of a zig-zag profile.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Filter Set
open scoped Topology ContDiff

namespace SymplecticGeometry

/-- The cutoff at one crossing `c` of sign `σ`, with `|σ| = 1`. -/
private theorem exists_zigzag_cutoff {k : ℕ} (j : Fin k) {g : ℝ → ℝ} {σ c w r : ℝ}
    (hσ : |σ| = 1) (hw : 0 < w) (hr : 0 < r)
    (hg : ∀ t, w ≤ |t - c| → |t - c| ≤ 2 * w → 1 / 2 ≤ σ * SignType.sign (t - c) * g t) :
    ∃ φ : (Fin 1 → ℝ) × (Fin k → ℝ) → ℝ, ContDiff ℝ ∞ φ ∧ (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      ∀ u : Fin 1 → ℝ,
        ‖fderiv ℝ φ (u, Pi.single j (r * g (u 0)))‖ ≤ 3 / r ∧
        (u 0 ≤ c - w → φ =ᶠ[𝓝 (u, Pi.single j (r * g (u 0)))] 0) ∧
        (c + w ≤ u 0 → φ =ᶠ[𝓝 (u, Pi.single j (r * g (u 0)))] 1) := by
  obtain ⟨μ, hμ, hμanti, hμ0, hμb, hμa, hμd, -⟩ :=
    TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le (a := -1 / 4) (b := 1 / 4) (v := 1)
      (τ := 3) (by norm_num) zero_le_one (by norm_num)
  have hμ1 : ∀ s, μ s ≤ 1 := fun s ↦ by
    rcases le_total s (-1 / 4) with hs | hs
    · exact (hμa s hs).le
    · exact (hμanti hs).trans (hμa _ le_rfl).le
  set ℓ : (Fin 1 → ℝ) × (Fin k → ℝ) →L[ℝ] ℝ :=
    (-(σ / r)) • ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) (Fin k → ℝ))) with hℓ
  have hℓ_apply : ∀ y, ℓ y = -(σ / r) * y.2 j := fun y ↦ by simp [hℓ]
  set β : ℝ → ℝ → ℝ := fun a t ↦ Real.smoothTransition ((t - a) / w) with hβ
  have hβ0 : ∀ a t, t ≤ a → β a t = 0 := fun a t h ↦
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)
  have hβ1 : ∀ a t, a + w ≤ t → β a t = 1 := fun a t h ↦
    Real.smoothTransition.one_of_one_le ((one_le_div hw).2 (by linarith))
  set φ : (Fin 1 → ℝ) × (Fin k → ℝ) → ℝ := fun y ↦
    β (c + w) (y.1 0) + (1 - β (c + w) (y.1 0)) * β (c - 2 * w) (y.1 0) * μ (ℓ y) with hφ
  have hcore : Continuous fun y : (Fin 1 → ℝ) × (Fin k → ℝ) ↦ y.1 0 := by fun_prop
  refine ⟨φ, ?_, fun y ↦ ?_, fun u ↦ ?_⟩
  · have hβc : ∀ a, ContDiff ℝ ∞ (β a) := fun a ↦
      (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
    have h0 : ContDiff ℝ ∞ fun y : (Fin 1 → ℝ) × (Fin k → ℝ) ↦ y.1 0 := by fun_prop
    exact ((hβc _).comp h0).add ((((contDiff_const.sub ((hβc _).comp h0)).mul
      ((hβc _).comp h0))).mul (hμ.comp ℓ.contDiff))
  · have a0 := Real.smoothTransition.nonneg ((y.1 0 - (c + w)) / w)
    have a1 := Real.smoothTransition.le_one ((y.1 0 - (c + w)) / w)
    have b0 := Real.smoothTransition.nonneg ((y.1 0 - (c - 2 * w)) / w)
    have b1 := Real.smoothTransition.le_one ((y.1 0 - (c - 2 * w)) / w)
    have m0 := hμ0 (ℓ y)
    have m1 := hμ1 (ℓ y)
    simp only [hφ, hβ]
    constructor
    · have := mul_nonneg (mul_nonneg (sub_nonneg.2 a1) b0) m0
      linarith
    · have hbm := mul_le_mul b1 m1 m0 zero_le_one
      have := mul_le_of_le_one_right (sub_nonneg.2 a1) (hbm.trans_eq (one_mul 1))
      rw [mul_assoc]
      linarith
  set x : (Fin 1 → ℝ) × (Fin k → ℝ) := (u, Pi.single j (r * g (u 0))) with hx
  have hℓx : ℓ x = -(σ * g (u 0)) := by
    rw [hℓ_apply]; simp [hx]; field_simp
  have hleft : u 0 ≤ c - w → φ =ᶠ[𝓝 x] 0 := fun hu ↦ by
    rcases lt_or_ge (u 0) (c - 2 * w) with hu' | hu'
    · filter_upwards [(hcore.tendsto x).eventually (gt_mem_nhds hu')] with y hy
      simp [hφ, hβ0 (c + w) (y.1 0) (by linarith), hβ0 (c - 2 * w) (y.1 0) hy.le]
    · have hs := hg (u 0) (by rw [abs_of_neg (by linarith)]; linarith)
        (by rw [abs_of_neg (by linarith)]; linarith)
      rw [sign_neg (by linarith : u 0 - c < 0)] at hs
      have h1 : 1 / 4 < ℓ x := by
        rw [hℓx]; simp only [SignType.coe_neg, SignType.coe_one, mul_neg, mul_one] at hs; linarith
      filter_upwards [(hcore.tendsto x).eventually (gt_mem_nhds (by linarith : x.1 0 < c + w)),
        (ℓ.continuous.tendsto x).eventually (lt_mem_nhds h1)] with y hy hy'
      simp [hφ, hβ0 (c + w) (y.1 0) hy.le, hμb _ hy'.le]
  have hright : c + w ≤ u 0 → φ =ᶠ[𝓝 x] 1 := fun hu ↦ by
    rcases lt_or_ge (c + 2 * w) (u 0) with hu' | hu'
    · filter_upwards [(hcore.tendsto x).eventually (lt_mem_nhds hu')] with y hy
      simp [hφ, hβ1 (c + w) (y.1 0) (by linarith)]
    · have hs := hg (u 0) (by rw [abs_of_pos (by linarith)]; linarith)
        (by rw [abs_of_pos (by linarith)]; linarith)
      rw [sign_pos (by linarith : 0 < u 0 - c)] at hs
      have h1 : ℓ x < -1 / 4 := by
        rw [hℓx]; simp only [SignType.coe_one, mul_one] at hs; linarith
      filter_upwards [(hcore.tendsto x).eventually (lt_mem_nhds (by linarith : c - w < x.1 0)),
        (ℓ.continuous.tendsto x).eventually (gt_mem_nhds h1)] with y hy hy'
      simp [hφ, hβ1 (c - 2 * w) (y.1 0) (by linarith), hμa _ hy'.le]
  refine ⟨?_, hleft, hright⟩
  have hr3 : 0 ≤ 3 / r := by positivity
  rcases le_or_gt (u 0) (c - w) with hu | hu
  · rw [(hleft hu).fderiv_eq]; simpa using hr3
  rcases le_or_gt (c + w) (u 0) with hu' | hu'
  · rw [(hright hu').fderiv_eq]; simpa using hr3
  have hmid : φ =ᶠ[𝓝 x] μ ∘ ℓ := by
    filter_upwards [(hcore.tendsto x).eventually (lt_mem_nhds (by simpa [hx] using hu)),
      (hcore.tendsto x).eventually (gt_mem_nhds (by simpa [hx] using hu'))] with y hy hy'
    simp [hφ, hβ0 (c + w) (y.1 0) hy'.le, hβ1 (c - 2 * w) (y.1 0) (by linarith)]
  have hd : HasFDerivAt (μ ∘ ℓ) (deriv μ (ℓ x) • ℓ) x :=
    ((hμ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt x ℓ.hasFDerivAt
  rw [hmid.fderiv_eq, hd.fderiv, norm_smul]
  have hℓn : ‖ℓ‖ ≤ 1 / r := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
    rw [hℓ_apply, norm_mul, norm_neg, norm_div, Real.norm_eq_abs σ, hσ, Real.norm_of_nonneg hr.le,
      one_div, ← div_eq_inv_mul, div_le_iff₀ hr]
    calc ‖y.2 j‖ ≤ ‖y.2‖ := norm_le_pi_norm y.2 j
      _ ≤ ‖y‖ := norm_snd_le y
      _ = _ := by field_simp
  calc ‖deriv μ (ℓ x)‖ * ‖ℓ‖ ≤ 3 * (1 / r) :=
        mul_le_mul (hμd _) hℓn (norm_nonneg _) (by norm_num)
    _ = 3 / r := by ring

/-- **Cutoffs at the crossings of a zig-zag profile.** Let `g : ℝ → ℝ` change sign near the points
`c 0, …, c n`, in the sense that `(-1) ^ i sign (t - c i) g t ≥ 1/2` whenever
`w ≤ |t - c i| ≤ 2 w`, and let `r > 0`. Consider the curve `u ↦ (u, r g (u 0) eⱼ)` in
`(Fin 1 → ℝ) × (Fin k → ℝ)`. There are smooth functions `φ i` with values in `[0, 1]` such that,
at each point `x` of the curve, `‖D φ i (x)‖ ≤ 3 / r`, `φ i` vanishes near `x` if `x` lies before
`c i - w`, and `φ i` equals `1` near `x` if `x` lies after `c i + w`.

The bound `3 / r` depends neither on `g`, nor on the points `c i`, nor on the width `w`. -/
theorem exists_zigzag_cutoffs {k : ℕ} (j : Fin k) {g : ℝ → ℝ} {n : ℕ} {c : Fin (n + 1) → ℝ}
    {w r : ℝ} (hw : 0 < w) (hr : 0 < r)
    (hg : ∀ i : Fin (n + 1), ∀ t, w ≤ |t - c i| → |t - c i| ≤ 2 * w →
      1 / 2 ≤ (-1) ^ (i : ℕ) * SignType.sign (t - c i) * g t) :
    ∃ φ : Fin (n + 1) → (Fin 1 → ℝ) × (Fin k → ℝ) → ℝ,
      (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i y, 0 ≤ φ i y ∧ φ i y ≤ 1) ∧
      ∀ i (u : Fin 1 → ℝ),
        ‖fderiv ℝ (φ i) (u, Pi.single j (r * g (u 0)))‖ ≤ 3 / r ∧
        (u 0 ≤ c i - w → φ i =ᶠ[𝓝 (u, Pi.single j (r * g (u 0)))] 0) ∧
        (c i + w ≤ u 0 → φ i =ᶠ[𝓝 (u, Pi.single j (r * g (u 0)))] 1) := by
  choose φ hφ hφ01 hφx using fun i : Fin (n + 1) ↦
    exists_zigzag_cutoff j (σ := (-1) ^ (i : ℕ)) (by simp) hw hr (hg i)
  exact ⟨φ, hφ, hφ01, hφx⟩

end SymplecticGeometry

end
