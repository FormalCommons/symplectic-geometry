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
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import SymplecticGeometry.Analysis.Calculus.ContDiff.AddSumRangeSmulSub
import SymplecticGeometry.Analysis.Calculus.FDeriv.AddSmulSub
import SymplecticGeometry.Analysis.Calculus.HolonomicApproximation.Basic
import SymplecticGeometry.Analysis.Calculus.MeanValue
import SymplecticGeometry.Analysis.Normed.Group.Pi
import SymplecticGeometry.Analysis.Normed.Operator.Pi
import SymplecticGeometry.Topology.Algebra.Module.LinearMap

/-!
# Holonomic approximation along a zig-zag

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

The gluing gives holonomic approximation along the zig-zag in the direction `i₀` of the core cube:
the map `f` near the faces `|u i₀| = 1`, where `(f, G)` is holonomic, and in between the
first-order Taylor maps `y ↦ f p + G p (y - p)` at the moving base points
`p = (update y.1 i₀ (c l), 0)`, so that the other core coordinates are parameters. The derivative
of such a map is compared with `G'`, which is `D f` on the core directions other than `i₀` and
`G` on the others (`SymplecticGeometry.norm_fderiv_taylor_affine_sub_le`); the gap between the
two is bounded through a uniform bound on the derivative of `u ↦ G (update u i₀ s, 0)`. Where
`(f, G)` is holonomic in the directions `J'` on the cube, `G'` and `G` agree on the vectors
in the directions `insert i₀ J'` up to a small error near the cube. At the points of the curve
outside the windows the error is that of one Taylor map, of order the height `r`. In a window,
the derivative error gains `(3 / r) ‖S (i + 1) - S i‖`, and two neighbouring Taylor maps differ
by the mesh times a bound on `‖D f - G‖`, plus `r` times the variation of `G` over the mesh. So
`r` is chosen first, and then the mesh small against `r`.

## Main results

* `SymplecticGeometry.exists_zigzag_cutoffs`: the cutoffs at the crossings of a zig-zag profile.
* `SymplecticGeometry.exists_zigzag_chain`: smooth maps `S 0, …, S (n + 1)` glued along the
  curve by these cutoffs, as `S 0 + ∑ φ l • (S (l + 1) - S l)`, with the glued map equal to `S l`
  near the points of the curve between the crossings and estimated against `S i` and `S (i + 1)`
  near the crossing `c i`.
* `Monotone.exists_add_le_and_le_sub_of_le_abs_sub`: a point at distance at least `w` from every
  crossing lies between two consecutive crossings, as the first case of `exists_zigzag_chain`
  needs.
* `SymplecticGeometry.exists_holonomic_approximation_zigzag`: a smooth map that approximates a
  formal section `(f, G)` near the zig-zag curve over the core cube, with the derivative
  estimate in the directions `insert i₀ J'`, and equals `f` near the faces `|u i₀| = 1`, where
  `(f, G)` is holonomic.

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

/-- If `t` is at distance at least `w` from each term of a monotone sequence `c 0 ≤ ⋯ ≤ c n`, then
there is `l ≤ n + 1` such that `t` lies at least `w` above `c i` for `i < l`, and at least `w`
below `c i` for `i ≥ l`. -/
theorem _root_.Monotone.exists_add_le_and_le_sub_of_le_abs_sub {α : Type*} [AddCommGroup α]
    [LinearOrder α] [IsOrderedAddMonoid α] {n : ℕ} {c : Fin (n + 1) → α} (hc : Monotone c)
    {t w : α} (h : ∀ i, w ≤ |t - c i|) :
    ∃ l ≤ n + 1, (∀ i : Fin (n + 1), (i : ℕ) < l → c i + w ≤ t) ∧
      ∀ i : Fin (n + 1), l ≤ (i : ℕ) → t ≤ c i - w := by
  classical
  -- `l` is the first index with `t < c l`, or `n + 1` if there is none.
  have hex : ∃ l, l = n + 1 ∨ ∃ hl : l < n + 1, t < c ⟨l, hl⟩ := ⟨n + 1, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · have hi' := Nat.find_min hex hi
    simp only [not_or, not_exists, not_lt] at hi'
    have := h i
    rw [abs_of_nonneg (sub_nonneg.2 (hi'.2 i.isLt))] at this
    exact le_sub_iff_add_le'.1 this
  · rcases Nat.find_spec hex with h' | ⟨hl, h'⟩
    · have := i.isLt
      omega
    have hci : t < c i := h'.trans_le (hc (Fin.le_def.2 hi))
    have := h i
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 hci)] at this
    exact le_sub_comm.1 this

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

/-- The constants of `exists_holonomic_approximation_zigzag`: a height `r` below `r₀`, `ρT` and
`δ` with `M r < ε`, a margin `b < 1` with `3 b < δ`, and a mesh `ρ ≤ b` small against `r`. -/
private theorem exists_zigzag_constants {M ε r₀ ρT δ : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hr₀ : 0 < r₀) (hρT : 0 < ρT) (hδ : 0 < δ) :
    ∃ r b ρ : ℝ, 0 < r ∧ r < r₀ ∧ r < ρT ∧ r < δ ∧ M * r < ε ∧ 0 < b ∧ b < 1 ∧ 3 * b < δ ∧
      0 < ρ ∧ ρ ≤ b ∧ ρ ≤ r / 2 ∧ 3 * M * ρ / r ≤ ε / 4 := by
  set r := min (min (r₀ / 2) (ρT / 2)) (min (δ / 2) (ε / (2 * M)))
  have hr : 0 < r := by positivity
  have hrr₀ : r < r₀ := by
    have := min_le_left (min (r₀ / 2) (ρT / 2)) (min (δ / 2) (ε / (2 * M)))
    have := min_le_left (r₀ / 2) (ρT / 2); linarith
  have hrρT : r < ρT := by
    have := min_le_left (min (r₀ / 2) (ρT / 2)) (min (δ / 2) (ε / (2 * M)))
    have := min_le_right (r₀ / 2) (ρT / 2); linarith
  have hrδ : r < δ := by
    have := min_le_right (min (r₀ / 2) (ρT / 2)) (min (δ / 2) (ε / (2 * M)))
    have := min_le_left (δ / 2) (ε / (2 * M)); linarith
  have hrε : M * r < ε := by
    have := min_le_right (min (r₀ / 2) (ρT / 2)) (min (δ / 2) (ε / (2 * M)))
    have := min_le_right (δ / 2) (ε / (2 * M))
    have h2 : M * r ≤ M * (ε / (2 * M)) := by gcongr; linarith
    rw [show M * (ε / (2 * M)) = ε / 2 by field_simp] at h2
    linarith
  set b := min (δ / 4) (1 / 2)
  have hb : 0 < b := by positivity
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hbδ : 3 * b < δ := by have := min_le_left (δ / 4) (1 / 2); linarith
  set ρ := min (min b (r / 2)) (ε * r / (12 * M))
  have hρ : 0 < ρ := by positivity
  have hρb : ρ ≤ b := (min_le_left _ _).trans (min_le_left _ _)
  have hρr : ρ ≤ r / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρε : 3 * M * ρ / r ≤ ε / 4 := by
    have h1 : ρ ≤ ε * r / (12 * M) := min_le_right _ _
    rw [div_le_iff₀ hr]
    have : 3 * M * ρ ≤ 3 * M * (ε * r / (12 * M)) := by gcongr
    rw [show 3 * M * (ε * r / (12 * M)) = ε / 4 * r by field_simp; ring] at this
    exact this
  exact ⟨r, b, ρ, hr, hrr₀, hrρT, hrδ, hrε, hb, hb1, hbδ, hρ, hρb, hρr, hρε⟩


/-- The sup norm of `x - (update x.1 i₀ s, 0)` on `(Fin m → ℝ) × (Fin k → ℝ)`. -/
private theorem norm_sub_update (i₀ : Fin m) (x : (Fin m → ℝ) × (Fin k → ℝ)) (s : ℝ) :
    ‖x - (Function.update x.1 i₀ s, 0)‖ = max |x.1 i₀ - s| ‖x.2‖ := by
  have h : x.1 - Function.update x.1 i₀ s = Pi.single i₀ (x.1 i₀ - s) := by
    ext i
    rcases eq_or_ne i i₀ with rfl | hi <;> simp [*]
  rw [Prod.norm_def]
  simp [h, Pi.norm_single, Real.norm_eq_abs]

/-- A step of `exists_holonomic_approximation_zigzag`: on the part of the curve where it is used,
each section of the chain is `C¹`-close to `(f, G)`. These are `f` near the faces `u i₀ = ± 1`,
where `(f, G)` is holonomic, and in between the Taylor maps at the crossings within `r` of the
point. -/
private theorem zigzag_section_estimate (i₀ : Fin m) {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {a : ℝ → (Fin m → ℝ) × (Fin k → ℝ)} {S : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → F}
    {c : Fin (n + 1) → ℝ} {K : Set ((Fin m → ℝ) × (Fin k → ℝ))} {b w ρ r δ ρT η M' : ℝ}
    {x : (Fin m → ℝ) × (Fin k → ℝ)}
    (ha : ∀ s, ‖x - a s‖ = max |x.1 i₀ - s| ‖x.2‖) (haK : ∀ s, |s| ≤ 1 → a s ∈ K)
    (hhol : ∀ s, |s| = 1 → ‖x - a s‖ < δ → fderiv ℝ f x = G x)
    (hTay : ∀ p ∈ K, ‖x - p‖ < ρT →
      ‖(f p + G p (x - p)) - f x‖ ≤ (‖fderiv ℝ f p - G p‖ + η) * ‖x - p‖)
    (hM' : ∀ p ∈ K, ‖fderiv ℝ f p - G p‖ + η ≤ M') (hS0 : S 0 = f) (hSn : S (n + 1) = f)
    (hST : ∀ i : Fin (n + 1), (i : ℕ) < n →
      S (i + 1) x = f (a (c i)) + G (a (c i)) (x - a (c i)))
    (hSd : ∀ i : Fin (n + 1), (i : ℕ) < n → ‖x - a (c i)‖ ≤ r →
      ‖fderiv ℝ (S (i + 1)) x - G x‖ ≤ 2 * η)
    (hc : Monotone c) (hc0 : -1 + b < c 0 - 2 * w) (hc0' : c 0 ≤ -1 + 2 * b)
    (hcn : 1 - 2 * b ≤ c (Fin.last n)) (hcn' : c (Fin.last n) + 2 * w < 1 - b)
    (hcc : ∀ i : Fin n, c i.succ - c i.castSucc < ρ ∧ c i.castSucc + 4 * w ≤ c i.succ)
    (hw : 0 < w) (hbδ : 3 * b < δ) (hρr : ρ ≤ r / 2) (hrρT : r < ρT) (hrδ : r < δ)
    (hη : 0 ≤ η) (hM'0 : 0 ≤ M') (hx1 : |x.1 i₀| ≤ 1)
    (hx2 : ‖x.2‖ ≤ r) {l : ℕ} (hl : l ≤ n + 1)
    (h₁ : ∀ i : Fin (n + 1), (i : ℕ) + 1 = l → c i - w ≤ x.1 i₀)
    (h₂ : ∀ i : Fin (n + 1), (i : ℕ) = l → x.1 i₀ ≤ c i + w) :
    ‖S l x - f x‖ ≤ M' * r ∧ ‖fderiv ℝ (S l) x - G x‖ ≤ 2 * η := by
  have hx1' := abs_le.1 hx1
  have h2η : 0 ≤ 2 * η := by positivity
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · -- `f`, near the face `u i₀ = -1`.
    have h := h₂ 0 rfl
    rw [hS0, sub_self, norm_zero, hhol (-1) (by norm_num) ?_, sub_self, norm_zero]
    · exact ⟨mul_nonneg hM'0 ((norm_nonneg _).trans hx2), h2η⟩
    rw [ha]
    refine max_lt ?_ (hx2.trans_lt hrδ)
    rw [abs_lt]; constructor <;> linarith
  rcases hl.lt_or_eq with hl' | rfl
  · -- The Taylor map at `c m`, for `l = m + 1`.
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hm : m < n := by omega
    have e₁ := h₁ ⟨m, by omega⟩ rfl
    have e₂ := h₂ ⟨m + 1, by omega⟩ rfl
    obtain ⟨s₁, s₂⟩ := hcc ⟨m, hm⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at s₁ s₂
    have hcl : |c ⟨m, by omega⟩| ≤ 1 := abs_le.2
      ⟨by linarith [hc (Fin.zero_le (⟨m, by omega⟩ : Fin (n + 1)))],
        by linarith [hc (Fin.le_last (⟨m, by omega⟩ : Fin (n + 1)))]⟩
    have hxa : ‖x - a (c ⟨m, by omega⟩)‖ ≤ r := by
      rw [ha]
      refine max_le ?_ hx2
      rw [abs_le]; constructor <;> linarith
    have t₁ := hTay _ (haK _ hcl) (hxa.trans_lt hrρT)
    rw [show S (m + 1) x = _ from hST ⟨m, by omega⟩ hm]
    exact ⟨t₁.trans (mul_le_mul (hM' _ (haK _ hcl)) hxa (norm_nonneg _) hM'0),
      hSd ⟨m, by omega⟩ hm hxa⟩
  · -- `f`, near the face `u i₀ = 1`.
    have h := h₁ (Fin.last n) (by simp)
    rw [hSn, sub_self, norm_zero, hhol 1 (by norm_num) ?_, sub_self, norm_zero]
    · exact ⟨mul_nonneg hM'0 ((norm_nonneg _).trans hx2), h2η⟩
    rw [ha]
    refine max_lt ?_ (hx2.trans_lt hrδ)
    rw [abs_lt]; constructor <;> linarith

/-- A step of `exists_holonomic_approximation_zigzag`: in the window of a crossing `c i`, the two
sections that the chain interpolates differ by little compared with `r`. -/
private theorem zigzag_neighbour_estimate (i₀ : Fin m) {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {a : ℝ → (Fin m → ℝ) × (Fin k → ℝ)} {S : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → F}
    {c : Fin (n + 1) → ℝ} {K : Set ((Fin m → ℝ) × (Fin k → ℝ))} {b w ρ r δ ρT η M' : ℝ}
    {x : (Fin m → ℝ) × (Fin k → ℝ)}
    (ha : ∀ s, ‖x - a s‖ = max |x.1 i₀ - s| ‖x.2‖) (ha' : ∀ s s', ‖a s - a s'‖ = |s - s'|)
    (haK : ∀ s, |s| ≤ 1 → a s ∈ K)
    (hhol : ∀ s, |s| = 1 → ∀ y, ‖y - a s‖ < δ → fderiv ℝ f y = G y)
    (hTay : ∀ p ∈ K, ∀ x, ‖x - p‖ < ρT →
      ‖(f p + G p (x - p)) - f x‖ ≤ (‖fderiv ℝ f p - G p‖ + η) * ‖x - p‖ ∧
      ‖fderiv ℝ (fun y ↦ f p + G p (y - p)) x - G x‖ ≤ η ∧
      ∀ y, ‖(f p + G p (y - p)) - (f x + G x (y - x))‖ ≤
        (‖fderiv ℝ f p - G p‖ + η) * ‖x - p‖ + η * ‖y - x‖)
    (hM' : ∀ p ∈ K, ‖fderiv ℝ f p - G p‖ + η ≤ M') (hS0 : S 0 = f) (hSn : S (n + 1) = f)
    (hST : ∀ i : Fin (n + 1), (i : ℕ) < n →
      S (i + 1) x = f (a (c i)) + G (a (c i)) (x - a (c i)))
    (hc : Monotone c) (hc0 : -1 + b < c 0 - 2 * w) (hc0' : c 0 ≤ -1 + 2 * b)
    (hcn : 1 - 2 * b ≤ c (Fin.last n)) (hcn' : c (Fin.last n) + 2 * w < 1 - b)
    (hcc : ∀ i : Fin n, c i.succ - c i.castSucc < ρ ∧ c i.castSucc + 4 * w ≤ c i.succ)
    (hw : 0 < w) (hρ : 0 ≤ ρ) (hbδ : 3 * b < δ) (hρb : ρ ≤ b) (hρr : ρ ≤ r / 2) (hrρT : r < ρT)
    (hη : 0 ≤ η) (hM'0 : 0 ≤ M') (hx2 : ‖x.2‖ ≤ r)
    {i : Fin (n + 1)} (hi : |x.1 i₀ - c i| < w) :
    ‖S ((i : ℕ) + 1) x - S i x‖ ≤ M' * ρ + η * r := by
  have hi' := abs_lt.1 hi
  have hcl : ∀ i', |c i'| ≤ 1 := fun i' ↦ abs_le.2
    ⟨by linarith [hc (Fin.zero_le i')], by linarith [hc (Fin.le_last i')]⟩
  have hρ0 : 0 ≤ M' * ρ := mul_nonneg hM'0 hρ
  -- When there are two crossings or more, `4 w < ρ`.
  have hwρ : 0 < n → 4 * w < ρ := fun hn ↦ by have := hcc ⟨0, hn⟩; linarith
  -- A Taylor map at a holonomic point `p` differs from `f` at `x` by at most `η ‖x - p‖`.
  have hhT : ∀ s, |s| ≤ 1 → fderiv ℝ f (a s) = G (a s) → ‖x - a s‖ ≤ r →
      ‖(f (a s) + G (a s) (x - a s)) - f x‖ ≤ η * r := fun s hs hp hxa ↦ by
    have := (hTay _ (haK s hs) x (hxa.trans_lt hrρT)).1
    rw [hp, sub_self, norm_zero, zero_add] at this
    exact this.trans (mul_le_mul_of_nonneg_left hxa hη)
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0 <;>
    rcases (Nat.lt_succ_iff.1 i.isLt).lt_or_eq with hn | hn
  · -- The first window: `f` against the Taylor map at `c 0`.
    obtain rfl : i = 0 := Fin.ext h0
    rw [show S ((0 : Fin (n + 1)) + 1) x = _ from hST 0 hn, Fin.val_zero, hS0]
    refine (hhT _ (hcl 0) (hhol (-1) (by norm_num) _ ?_) ?_).trans (by linarith)
    · rw [ha', abs_lt]; constructor <;> linarith
    · rw [ha]; exact max_le (by rw [abs_le]; constructor <;> linarith [hwρ hn]) hx2
  · -- Only one crossing: both sections are `f`.
    have hn0 : n = 0 := by omega
    subst hn0
    rw [h0, hS0, show S (0 + 1) = f from hSn, sub_self, norm_zero]
    exact add_nonneg hρ0 (mul_nonneg hη ((norm_nonneg _).trans hx2))
  · -- Between the Taylor maps at `c (i - 1)` and `c i`.
    set i' : Fin (n + 1) := ⟨i - 1, by omega⟩
    have hii : (i : ℕ) = (i' : ℕ) + 1 := by simp [i']; omega
    rw [show S ((i : ℕ) + 1) x = _ from hST i hn, hii,
      show S ((i' : ℕ) + 1) x = _ from hST i' (by omega)]
    obtain ⟨s₁, s₂⟩ := hcc ⟨i', by omega⟩
    have hsucc : (Fin.succ ⟨(i' : ℕ), by omega⟩ : Fin (n + 1)) = i := Fin.ext (by simp; omega)
    simp only [hsucc, Fin.castSucc_mk, Fin.eta] at s₁ s₂
    have hab : ‖a (c i) - a (c i')‖ ≤ ρ := by rw [ha', abs_le]; constructor <;> linarith
    obtain ⟨-, -, t₃⟩ := hTay _ (haK _ (hcl i')) (a (c i)) (hab.trans_lt (by linarith))
    rw [norm_sub_rev]
    refine (t₃ x).trans (add_le_add (mul_le_mul (hM' _ (haK _ (hcl i'))) hab (norm_nonneg _)
      hM'0) (mul_le_mul_of_nonneg_left ?_ hη))
    rw [ha]; exact max_le (by rw [abs_le]; constructor <;> linarith [hwρ (by omega)]) hx2
  · -- The last window: the Taylor map at `c (n - 1)` against `f`.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain rfl : i = Fin.last (m + 1) := Fin.ext hn
    set i' : Fin (m + 2) := (Fin.last m).castSucc
    rw [Fin.val_last, hSn, show S (m + 1) x = _ from hST i' (by simp [i']), norm_sub_rev]
    obtain ⟨s₁, s₂⟩ := hcc (Fin.last m)
    simp only [Fin.succ_last] at s₁ s₂
    refine (hhT _ (hcl i') (hhol 1 (by norm_num) _ ?_) ?_).trans (by linarith)
    · rw [ha', abs_lt]; constructor <;> linarith [hc (Fin.le_last i')]
    · rw [ha]; exact max_le (by rw [abs_le]; constructor <;> linarith [hwρ h0]) hx2

/-- A step of `exists_holonomic_approximation_zigzag`: the chain `f'` is `C¹`-close to `(f, G)`
at a point `x` of the curve over `t`, given the estimates of the sections that it glues
(`zigzag_section_estimate`, `zigzag_neighbour_estimate`). -/
private theorem zigzag_curve_estimate {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f f' : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {S : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → F} {c : Fin (n + 1) → ℝ} (hc : Monotone c)
    {t w r ε η M' ρ : ℝ} {x : (Fin m → ℝ) × (Fin k → ℝ)} (hw : 0 ≤ w) (hr : 0 < r) (hε : 0 < ε)
    (hout : ∀ l ≤ n + 1, (∀ i : Fin (n + 1), (i : ℕ) < l → c i + w ≤ t) →
      (∀ i : Fin (n + 1), l ≤ (i : ℕ) → t ≤ c i - w) → f' =ᶠ[𝓝 x] S l)
    (hwin : ∀ i : Fin (n + 1), |t - c i| < w →
      ‖f' x - f x‖ ≤ max ‖S i x - f x‖ ‖S ((i : ℕ) + 1) x - f x‖ ∧
      ‖fderiv ℝ f' x - G x‖ ≤ max ‖fderiv ℝ (S i) x - G x‖ ‖fderiv ℝ (S ((i : ℕ) + 1)) x - G x‖ +
        3 / r * ‖S ((i : ℕ) + 1) x - S i x‖)
    (hB : ∀ l ≤ n + 1, (∀ i : Fin (n + 1), (i : ℕ) + 1 = l → c i - w ≤ t) →
      (∀ i : Fin (n + 1), (i : ℕ) = l → t ≤ c i + w) →
      ‖S l x - f x‖ ≤ M' * r ∧ ‖fderiv ℝ (S l) x - G x‖ ≤ 2 * η)
    (hD : ∀ i : Fin (n + 1), |t - c i| < w → ‖S ((i : ℕ) + 1) x - S i x‖ ≤ M' * ρ + η * r)
    (hrε : M' * r < ε) (hρε : 3 * M' * ρ / r ≤ ε / 4) (hη : η = ε / 8) :
    ‖f' x - f x‖ < ε ∧ ‖fderiv ℝ f' x - G x‖ < ε := by
  by_cases hwin' : ∃ i : Fin (n + 1), |t - c i| < w
  · -- In the window of `c i`, the chain interpolates `S i` and `S (i + 1)`.
    obtain ⟨i, hi⟩ := hwin'
    have hi' := abs_lt.1 hi
    obtain ⟨e₀, e₁⟩ := hwin i hi
    have hBi := hB i (by omega) (fun i' h ↦ by linarith [hc (Fin.le_def.2 (by omega) : i' ≤ i)])
      (fun i' h ↦ by rw [show i' = i from Fin.ext h]; linarith)
    have hBi' := hB (i + 1) (by omega)
      (fun i' h ↦ by rw [show i' = i from Fin.ext (by omega)]; linarith)
      (fun i' h ↦ by linarith [hc (Fin.le_def.2 (by omega) : i ≤ i')])
    refine ⟨e₀.trans_lt (max_lt (hBi.1.trans_lt hrε) (hBi'.1.trans_lt hrε)), e₁.trans_lt ?_⟩
    have h3 : 3 / r * ‖S ((i : ℕ) + 1) x - S i x‖ ≤ 3 * M' * ρ / r + 3 * η :=
      calc 3 / r * ‖S ((i : ℕ) + 1) x - S i x‖ ≤ 3 / r * (M' * ρ + η * r) := by
            gcongr; exact hD i hi
        _ = 3 * M' * ρ / r + 3 * η := by field_simp
    have := max_le hBi.2 hBi'.2
    linarith
  · -- Away from the windows, the chain is one section near `x`.
    push Not at hwin'
    obtain ⟨l, hl, h₁, h₀⟩ := hc.exists_add_le_and_le_sub_of_le_abs_sub hwin'
    have heq := hout l hl h₁ h₀
    rw [heq.eq_of_nhds, heq.fderiv_eq]
    have := hB l hl (fun i h ↦ by linarith [h₁ i (by omega)]) (fun i h ↦ by linarith [h₀ i h.ge])
    exact ⟨this.1.trans_lt hrε, this.2.trans_lt (by linarith)⟩

/-- A step of `exists_holonomic_approximation_zigzag`: the Taylor map of `(f, G)` at the moving
base point `Q' y + (eᵢ₀ s, 0) = (update y.1 i₀ s, 0)` has, at a point `x` within `r` of its base
point, derivative within `2 η` of `G' x`, for a field `G'` that equals
`D f ∘ Q' + G ∘ (1 - Q')` at the base point. This needs a bound `MH` on the derivative of
`u ↦ G (update u i₀ s, 0)` at `x.1`, with `MH r ≤ η`, and `G'` to vary by at most `η` between
the base point and `x`. -/
private theorem zigzag_taylor_fderiv_estimate (i₀ : Fin m) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G G' : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (Q' : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ))
    {x : (Fin m → ℝ) × (Fin k → ℝ)} {s MH r η : ℝ}
    (hQp : Q' x + (Pi.single i₀ s, 0) = (Function.update x.1 i₀ s, 0))
    (hG' : G' (Function.update x.1 i₀ s, 0) =
      (fderiv ℝ f (Function.update x.1 i₀ s, 0)).comp Q' +
        (G (Function.update x.1 i₀ s, 0)).comp (ContinuousLinearMap.id ℝ _ - Q'))
    (hf : DifferentiableAt ℝ f (Function.update x.1 i₀ s, 0))
    (hGs : DifferentiableAt ℝ (fun u : Fin m → ℝ ↦ G (Function.update u i₀ s, 0)) x.1)
    (hMH : ‖fderiv ℝ (fun u : Fin m → ℝ ↦ G (Function.update u i₀ s, 0)) x.1‖ ≤ MH)
    (hMH0 : 0 ≤ MH) (hxr : ‖x - (Function.update x.1 i₀ s, 0)‖ ≤ r) (hrH : MH * r ≤ η)
    (hG'x : ‖G' (Function.update x.1 i₀ s, 0) - G' x‖ ≤ η) :
    ‖fderiv ℝ (fun y ↦ f (Q' y + (Pi.single i₀ s, 0)) +
      G (Function.update y.1 i₀ s, 0) (y - (Q' y + (Pi.single i₀ s, 0)))) x - G' x‖ ≤ 2 * η := by
  have hΓ : HasFDerivAt (fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ G (Function.update y.1 i₀ s, 0))
      ((fderiv ℝ (fun u : Fin m → ℝ ↦ G (Function.update u i₀ s, 0)) x.1).comp
        (ContinuousLinearMap.fst ℝ _ _)) x :=
    hGs.hasFDerivAt.comp x hasFDerivAt_fst
  have h₁ := norm_fderiv_taylor_affine_sub_le
    (Γ := fun y : (Fin m → ℝ) × (Fin k → ℝ) ↦ G (Function.update y.1 i₀ s, 0)) Q'
    (Pi.single i₀ s, 0) x (by rw [hQp]; exact hf) hΓ.differentiableAt
  rw [hΓ.fderiv, hQp, ← hG'] at h₁
  have hΓn : ‖(fderiv ℝ (fun u : Fin m → ℝ ↦ G (Function.update u i₀ s, 0)) x.1).comp
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin k → ℝ))‖ ≤ MH :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ..)).trans hMH)
  have h₃ := h₁.trans ((mul_le_mul hΓn hxr (norm_nonneg _) hMH0).trans hrH)
  refine (norm_sub_le_norm_sub_add_norm_sub _ (G' (Function.update x.1 i₀ s, 0)) _).trans ?_
  linarith

/-- A step of `exists_holonomic_approximation_zigzag`: let `Q'` keep the core coordinates other
than `i₀`, let `P` keep the core directions `insert i₀ J'` and the transverse ones, and let
`G' = D f ∘ Q' + G ∘ (1 - Q')`. If `D f` agrees with `G` on the core vectors in the directions
`J'` over the core cube, then within some `δE > 0` of the cube, `G'` and `G` agree on the image of
`P` up to `ε`: `‖(A - G y) ∘ P‖ < ‖A - G' y‖ + ε` for every linear map `A`. -/
private theorem exists_zigzag_defect_lt (i₀ : Fin m) {J' : Finset (Fin m)} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G G' : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    {Q' P : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ)}
    (hQ' : ∀ y, Q' y = (Function.update y.1 i₀ 0, 0))
    (hP : ∀ y, P y = (ContinuousLinearMap.coordProj (𝕜 := ℝ) (insert i₀ J') y.1, y.2))
    (hfd : Continuous (fderiv ℝ f)) (hG : Continuous G)
    (hG' : ∀ y, G' y = (fderiv ℝ f y).comp Q' + (G y).comp (ContinuousLinearMap.id ℝ _ - Q'))
    (hJ' : ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∀ v : Fin m → ℝ, (∀ i ∉ J', v i = 0) →
      fderiv ℝ f (u, 0) (v, 0) = G (u, 0) (v, 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δE > 0, ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∀ y, dist y (u, 0) < δE →
      ∀ A : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F, ‖(A - G y).comp P‖ < ‖A - G' y‖ + ε := by
  have hGG' : ∀ y, G' y - G y = (fderiv ℝ f y - G y).comp Q' := fun y ↦ by
    rw [hG', ContinuousLinearMap.comp_add_comp_id_sub_sub]
  have hPn : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y ↦ by
    rw [one_mul, hP, Prod.norm_def, Prod.norm_def]
    exact max_le_max (ContinuousLinearMap.norm_coordProj_apply_le _ _) le_rfl
  -- The defect `(D f - G) ∘ Q' ∘ P` vanishes on the cube, so it is small near it.
  have hO : IsOpen {y | ‖(fderiv ℝ f y - G y).comp (Q'.comp P)‖ < ε} :=
    isOpen_lt (((hfd.sub hG).clm_comp continuous_const).norm) continuous_const
  have hBO : Metric.closedBall (0 : Fin m → ℝ) 1 ×ˢ {(0 : Fin k → ℝ)} ⊆
      {y | ‖(fderiv ℝ f y - G y).comp (Q'.comp P)‖ < ε} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    rw [mem_singleton_iff] at hv
    subst hv
    have : (fderiv ℝ f (u, 0) - G (u, 0)).comp (Q'.comp P) = 0 :=
      ContinuousLinearMap.ext fun w ↦ by
        simp only [ContinuousLinearMap.comp_apply, sub_apply,
          zero_apply, hQ']
        rw [hJ' u hu _ fun i hi ↦ ?_, sub_self]
        rcases eq_or_ne i i₀ with rfl | h
        · simp
        · rw [Function.update_of_ne h]
          simp [hP, h, hi]
    rw [mem_ofPred_eq, this, norm_zero]
    exact hε
  obtain ⟨δE, hδE, hδEO⟩ := ((isCompact_closedBall (0 : Fin m → ℝ) 1).prod
    (isCompact_singleton (x := (0 : Fin k → ℝ)))).exists_thickening_subset_open hO hBO
  refine ⟨δE, hδE, fun u hu y hy A ↦ ?_⟩
  have hyO := hδEO (Metric.mem_thickening_iff.2 ⟨(u, 0), ⟨hu, rfl⟩, hy⟩)
  rw [mem_ofPred_eq] at hyO
  have hsplit : (A - G y).comp P = (A - G' y).comp P + (fderiv ℝ f y - G y).comp (Q'.comp P) := by
    rw [← ContinuousLinearMap.comp_assoc, ← hGG', ← ContinuousLinearMap.add_comp,
      sub_add_sub_cancel]
  rw [hsplit]
  refine (norm_add_le _ _).trans_lt (add_lt_add_of_le_of_lt ?_ hyO)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hPn)

/-- **Holonomic approximation along a zig-zag in one direction of a cube.** On
`D = (Fin m → ℝ) × (Fin k → ℝ)` with sup norms, fix a core direction `i₀`, a transverse direction
`j` and a set `J'` of core directions. Let `(f, G)` be a formal section with `f` smooth and `G`
continuous, such that:
* for each `s`, the map `u ↦ G (update u i₀ s, 0)` is smooth, and its derivative at `u` is
  continuous in `(u, s)`;
* on the core cube `closedBall 0 1 ×ˢ {0}`, `D f` agrees with `G` on the core vectors in the
  directions `J'`;
* `(f, G)` is holonomic (`D f = G`) on an open set `U` containing the faces `|u i₀| = 1` of the
  core cube.

Let `ε, r₀ > 0`. There are a height `0 < r < r₀`, a smooth profile `g₀ : ℝ → ℝ` with `|g₀| ≤ 1`
vanishing near `± 1`, and a smooth map `f'` that equals `f` near the faces `|u i₀| = 1`, such that
on an open set `V` containing the points `(u, r g₀ (u i₀) eⱼ)`, `u` in the cube, `f'` is
`ε`-close to `f` and `(D f' - G) w` has norm at most `ε ‖w‖` for every vector `w` whose core
part lies in the directions `insert i₀ J'`. -/
theorem exists_holonomic_approximation_zigzag (i₀ : Fin m) (j : Fin k) {J' : Finset (Fin m)}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin m → ℝ) × (Fin k → ℝ) → F}
    {G : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hG : Continuous G)
    (hGs : ∀ s, ContDiff ℝ ∞ fun u : Fin m → ℝ ↦ G (Function.update u i₀ s, 0))
    (hGd : Continuous fun q : (Fin m → ℝ) × ℝ ↦
      fderiv ℝ (fun u ↦ G (Function.update u i₀ q.2, 0)) q.1)
    (hJ' : ∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) 1, ∀ v : Fin m → ℝ, (∀ i ∉ J', v i = 0) →
      fderiv ℝ f (u, 0) (v, 0) = G (u, 0) (v, 0))
    {U : Set ((Fin m → ℝ) × (Fin k → ℝ))} (hU : IsOpen U) (hUf : ∀ x ∈ U, fderiv ℝ f x = G x)
    (hU' : {u ∈ Metric.closedBall (0 : Fin m → ℝ) 1 | |u i₀| = 1} ×ˢ {0} ⊆ U)
    {ε r₀ : ℝ} (hε : 0 < ε) (hr₀ : 0 < r₀) :
    ∃ (r : ℝ) (g₀ : ℝ → ℝ) (f' : (Fin m → ℝ) × (Fin k → ℝ) → F)
      (V : Set ((Fin m → ℝ) × (Fin k → ℝ))),
      0 < r ∧ r < r₀ ∧ ContDiff ℝ ∞ g₀ ∧ (∀ t, |g₀ t| ≤ 1) ∧
      (∃ b > 0, ∀ t, 1 - b < |t| → g₀ t = 0) ∧ IsOpen V ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) 1, (u, Pi.single j (r * g₀ (u i₀))) ∈ V) ∧
      ContDiff ℝ ∞ f' ∧
      (∀ x ∈ V, ‖f' x - f x‖ < ε ∧ ∀ w : (Fin m → ℝ) × (Fin k → ℝ),
        (∀ i ∉ insert i₀ J', w.1 i = 0) → ‖(fderiv ℝ f' x - G x) w‖ ≤ ε * ‖w‖) ∧
      ∃ U' ∈ 𝓝ˢ ({u ∈ Metric.closedBall (0 : Fin m → ℝ) 1 | |u i₀| = 1} ×ˢ {0}),
        Set.EqOn f' f U' := by
  set B : Set (Fin m → ℝ) := Metric.closedBall 0 1
  have hB1 : ∀ u ∈ B, |u i₀| ≤ 1 := fun u hu ↦ by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm u i₀).trans (mem_closedBall_zero_iff.1 hu)
  have hupd : ∀ u ∈ B, ∀ s, |s| ≤ 1 → Function.update u i₀ s ∈ B := fun u hu s hs ↦
    mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by
      rcases eq_or_ne i i₀ with rfl | h
      · simpa using hs
      · rw [Function.update_of_ne h]
        exact (norm_le_pi_norm u i).trans (mem_closedBall_zero_iff.1 hu))
  -- `Q'` keeps the core coordinates other than `i₀`; `P` keeps the directions `insert i₀ J'`.
  set Q' : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ) :=
    (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin k → ℝ)).comp
      ((ContinuousLinearMap.coordProj (Finset.univ.erase i₀)).comp
        (ContinuousLinearMap.fst ℝ _ _)) with hQ'
  have hQ'_apply : ∀ y, Q' y = (Function.update y.1 i₀ 0, 0) := fun y ↦ by
    ext i
    · rcases eq_or_ne i i₀ with rfl | h <;> simp [*]
    · simp [hQ']
  set P : (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) × (Fin k → ℝ) :=
    (ContinuousLinearMap.coordProj (insert i₀ J')).prodMap
      (ContinuousLinearMap.id ℝ (Fin k → ℝ)) with hP
  have hP_apply : ∀ y, P y = (ContinuousLinearMap.coordProj (𝕜 := ℝ) (insert i₀ J') y.1, y.2) :=
    fun ⟨_, _⟩ ↦ by simp [hP]
  -- `G'` is `D f` on the core directions other than `i₀`, and `G` on the others.
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  set G' : (Fin m → ℝ) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) →L[ℝ] F := fun y ↦
    (fderiv ℝ f y).comp Q' + (G y).comp (ContinuousLinearMap.id ℝ _ - Q') with hG'_def
  have hG' : Continuous G' := (hfd.clm_comp continuous_const).add (hG.clm_comp continuous_const)
  have hUf' : ∀ x ∈ U, fderiv ℝ f x = G' x := fun x hx ↦ by
    simp only [hG'_def, hUf x hx, ContinuousLinearMap.comp_add_comp_id_sub_self]
  -- `G'` and `G` agree in the directions `insert i₀ J'` near the core cube.
  set ε₂ := ε / 2 with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  obtain ⟨δE, hδE, hδEO⟩ := exists_zigzag_defect_lt (G' := G') i₀ hQ'_apply hP_apply hfd hG
    (fun y ↦ by rw [hG'_def]) hJ' hε₂0
  -- `f` is holonomic within `δ` of the faces `|u i₀| = 1`.
  have hKf : IsCompact ({u ∈ B | |u i₀| = 1} ×ˢ ({0} : Set (Fin k → ℝ))) :=
    ((isCompact_closedBall _ _).inter_right
      (isClosed_eq (by fun_prop) continuous_const)).prod isCompact_singleton
  obtain ⟨δ, hδ, hδU⟩ := hKf.exists_thickening_subset_open hU hU'
  have hhol : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), x.1 ∈ B → ∀ s, |s| = 1 → ∀ y,
      ‖y - (Function.update x.1 i₀ s, 0)‖ < δ → fderiv ℝ f y = G' y := fun x hx s hs y hy ↦
    hUf' y (hδU (Metric.mem_thickening_iff.2 ⟨(Function.update x.1 i₀ s, 0),
      ⟨⟨hupd _ hx s hs.le, by simp [hs]⟩, Set.mem_singleton _⟩,
      by rwa [dist_eq_norm]⟩))
  -- The base points `(update x.1 i₀ s, 0)` of the Taylor maps.
  set K : Set ((Fin m → ℝ) × (Fin k → ℝ)) := B ×ˢ {0}
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_singleton
  have haK : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), x.1 ∈ B → ∀ s, |s| ≤ 1 →
      ((Function.update x.1 i₀ s, 0) : (Fin m → ℝ) × (Fin k → ℝ)) ∈ K := fun x hx s hs ↦
    ⟨hupd _ hx s hs, rfl⟩
  have ha' : ∀ (x : (Fin m → ℝ) × (Fin k → ℝ)) (s s' : ℝ),
      ‖((Function.update x.1 i₀ s, 0) : (Fin m → ℝ) × (Fin k → ℝ)) -
        (Function.update x.1 i₀ s', 0)‖ = |s - s'| := fun x s s' ↦ by
    have := norm_sub_update (k := k) i₀ (Function.update x.1 i₀ s, 0) s'
    simpa using this
  -- Uniform estimates on the cube.
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hfd.sub hG').continuousOn
  obtain ⟨MH, hMH⟩ := ((isCompact_closedBall (0 : Fin m → ℝ) 1).prod
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (f := fun q : (Fin m → ℝ) × ℝ ↦ fderiv ℝ (fun u ↦ G (Function.update u i₀ q.2, 0)) q.1)
    hGd.continuousOn
  set η := ε₂ / 8
  have hη : 0 < η := by positivity
  obtain ⟨ρT, hρT, hTay⟩ := hK.exists_pos_norm_taylor_sub_le
    (fun a _ ↦ (hf.of_le (by simp)).contDiffAt) (fun a _ ↦ hG'.continuousAt) hη
  set M' := max M 0 + η
  have hM' : 0 < M' := by positivity
  have hMa : ∀ p ∈ K, ‖fderiv ℝ f p - G' p‖ + η ≤ M' := fun p hp ↦ by
    have := hM p hp; simp only [Pi.sub_apply] at this
    linarith [le_max_left M 0]
  set MH' := max MH 0 + 1
  have hMH' : 0 < MH' := by positivity
  set ρT' := min ρT (min δE (η / MH'))
  have hρT' : 0 < ρT' := by positivity
  -- The parameters: first the height `r`, then the mesh `ρ`, and the zig-zag profile.
  obtain ⟨r, b, ρ, hr, hrr₀, hrρT', hrδ, hrε, hb, hb1, hbδ, hρ, hρb, hρr, hρε⟩ :=
    exists_zigzag_constants hM' hε₂0 hr₀ hρT' hδ
  have hrρT : r < ρT := hrρT'.trans_le (min_le_left _ _)
  have hrE : r < δE := hrρT'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrH : MH' * r ≤ η := by
    have : r < η / MH' := hrρT'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ hMH'] at this
    linarith
  obtain ⟨g, n, c, w, hg, hg1, hg0, hw, hcm, hc0, hc0', hcn, hcn', hcc, hgs⟩ :=
    exists_zigzag_profile hb hb1 hρ
  have hcl : ∀ i, |c i| ≤ 1 := fun i ↦ abs_le.2
    ⟨by linarith [hcm.monotone (Fin.zero_le i)], by linarith [hcm.monotone (Fin.le_last i)]⟩
  -- The Taylor maps at the moving base points `(update y.1 i₀ s, 0) = Q' y + p₀ s`.
  set p₀ : ℝ → (Fin m → ℝ) × (Fin k → ℝ) := fun s ↦ (Pi.single i₀ s, 0) with hp₀
  have hQp : ∀ y s, Q' y + p₀ s = (Function.update y.1 i₀ s, 0) := fun y s ↦ by
    rw [hQ'_apply]
    ext i
    · rcases eq_or_ne i i₀ with rfl | h <;> simp [*]
    · simp [hp₀]
  have hQX : ∀ (y : (Fin m → ℝ) × (Fin k → ℝ)) (s : ℝ),
      Q' (y - (Function.update y.1 i₀ s, 0)) = 0 := fun y s ↦ by
    rw [hQ'_apply]
    ext i
    · rcases eq_or_ne i i₀ with rfl | h <;> simp [*]
    · simp
  set T : ℝ → (Fin m → ℝ) × (Fin k → ℝ) → F := fun s y ↦
    f (Q' y + p₀ s) + G (Function.update y.1 i₀ s, 0) (y - (Q' y + p₀ s)) with hT_def
  have hT : ∀ s, ContDiff ℝ ∞ (T s) := fun s ↦
    (hf.comp (Q'.contDiff.add contDiff_const)).add
      (((hGs s).comp contDiff_fst).clm_apply (contDiff_id.sub (Q'.contDiff.add contDiff_const)))
  have hTx : ∀ s y, T s y = f (Function.update y.1 i₀ s, 0) +
      G' (Function.update y.1 i₀ s, 0) (y - (Function.update y.1 i₀ s, 0)) := fun s y ↦ by
    simp only [hT_def, hQp, hG'_def, add_apply,
      ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.id_apply, hQX, map_zero, zero_add, sub_zero]
  have hTd : ∀ x : (Fin m → ℝ) × (Fin k → ℝ), x.1 ∈ B → ∀ s, |s| ≤ 1 →
      ‖x - (Function.update x.1 i₀ s, 0)‖ ≤ r → ‖fderiv ℝ (T s) x - G' x‖ ≤ 2 * η := by
    intro x hx s hs hxr
    have h₂ := (hTay _ (haK x hx s hs) x (hxr.trans_lt hrρT)).2.1
    rw [fderiv_taylor] at h₂
    have hMHx := hMH (x.1, s) ⟨hx, (abs_le.1 hs).1, (abs_le.1 hs).2⟩
    exact zigzag_taylor_fderiv_estimate i₀ Q' (hQp x s) (by rw [hG'_def])
      (hf.differentiable (by simp) _) ((hGs s).differentiable (by simp) _)
      (by linarith [le_max_left MH 0]) hMH'.le hxr hrH h₂
  -- The sections: `f`, then the Taylor maps at `c 0, …, c (n - 1)`, then `f`.
  set S : ℕ → (Fin m → ℝ) × (Fin k → ℝ) → F := fun l ↦
    if h : 0 < l ∧ l ≤ n then T (c ⟨l - 1, by omega⟩) else f with hS_def
  have hS0 : S 0 = f := by simp [hS_def]
  have hSn : S (n + 1) = f := by simp [hS_def]
  have hST : ∀ i : Fin (n + 1), (i : ℕ) < n → S (i + 1) = T (c i) := fun i hi ↦ by
    simp [hS_def, hi]
  have hS : ∀ l ≤ n + 1, ContDiff ℝ ∞ (S l) := fun l _ ↦ by
    simp only [hS_def]
    split_ifs
    · exact hT _
    · exact hf
  obtain ⟨f', hf', hf'x⟩ := exists_zigzag_chain i₀ j hw hr (fun i ↦ (hcc i).2) hgs hS
  -- The curve, and the estimate at its points.
  set X : (Fin m → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) := fun u ↦ (u, Pi.single j (r * g (u i₀)))
    with hX
  have hX2 : ∀ u, ‖(X u).2‖ ≤ r := fun u ↦ by
    simp only [hX, Pi.norm_single, norm_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (hg1 _)
  have hcurve : ∀ u ∈ B,
      ‖f' (X u) - f (X u)‖ < ε₂ ∧ ‖fderiv ℝ f' (X u) - G' (X u)‖ < ε₂ := fun u hu ↦
    zigzag_curve_estimate hcm.monotone hw.le hr hε₂0 (hf'x u).1
      (fun i hi ↦ (hf'x u).2 i hi (f (X u)) (G' (X u)))
      (fun l hl h₁ h₂ ↦ zigzag_section_estimate i₀ (norm_sub_update i₀ (X u)) (haK (X u) hu)
        (fun s hs ↦ hhol (X u) hu s hs (X u)) (fun p hp hx ↦ (hTay p hp (X u) hx).1) hMa hS0 hSn
        (fun i hi ↦ by rw [hST i hi, hTx]) (fun i hi hxr ↦ by
          rw [hST i hi]; exact hTd (X u) hu _ (hcl i) hxr)
        hcm.monotone hc0 hc0' hcn hcn' hcc hw hbδ hρr hrρT hrδ hη.le hM'.le (hB1 u hu) (hX2 u)
        hl h₁ h₂)
      (fun i hi ↦ zigzag_neighbour_estimate i₀ (norm_sub_update i₀ (X u)) (ha' (X u))
        (haK (X u) hu) (hhol (X u) hu) hTay hMa hS0 hSn (fun i hi ↦ by rw [hST i hi, hTx])
        hcm.monotone hc0 hc0' hcn hcn' hcc hw hρ.le hbδ hρb hρr hrρT hη.le hM'.le (hX2 u) hi)
      hrε hρε rfl
  refine ⟨r, g, f', {x | ‖f' x - f x‖ < ε ∧ ‖(fderiv ℝ f' x - G x).comp P‖ < ε}, hr, hrr₀,
    hg, hg1, ⟨b, hb, fun t ht ↦ hg0 t ht.le⟩, ?_, fun u hu ↦ ?_, hf', fun x hx ↦ ?_, ?_⟩
  · exact (isOpen_lt (hf'.continuous.sub hf.continuous).norm continuous_const).inter
      (isOpen_lt ((((hf'.continuous_fderiv (by simp)).sub hG).clm_comp
        continuous_const).norm) continuous_const)
  · -- On the curve, `G'` and `G` agree in the directions of `P` up to `ε / 2`.
    obtain ⟨e₀, e₁⟩ := hcurve u hu
    have hXu : dist (X u) (u, 0) < δE := by
      rw [Prod.dist_eq, dist_self, dist_zero_right]
      exact (max_le hr.le (hX2 u)).trans_lt hrE
    exact ⟨e₀.trans (by linarith), (hδEO u hu (X u) hXu _).trans (by linarith)⟩
  · -- In the directions of `P`, the derivative error is that of the projected one.
    refine ⟨hx.1, fun v hv ↦ ?_⟩
    have hPv : P v = v := by rw [hP_apply, ContinuousLinearMap.coordProj_apply_eq_self hv]
    calc ‖(fderiv ℝ f' x - G x) v‖ = ‖((fderiv ℝ f' x - G x).comp P) v‖ := by
          rw [ContinuousLinearMap.comp_apply, hPv]
      _ ≤ ‖(fderiv ℝ f' x - G x).comp P‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖v‖ := by gcongr; exact hx.2.le
  · -- Near the faces `|u i₀| = 1`, `f'` is `f`.
    refine ⟨{y | f' =ᶠ[𝓝 y] f}, isOpen_setOfPred_eventually_nhds.mem_nhdsSet.2 ?_,
      fun y hy ↦ hy.eq_of_nhds⟩
    rintro ⟨u, v⟩ ⟨⟨-, hu1⟩, hv⟩
    rw [mem_singleton_iff] at hv
    subst hv
    have hX0 : X u = (u, 0) := by
      simp only [hX, hg0 _ (by rw [hu1]; linarith), mul_zero, Pi.single_zero]
    rw [mem_ofPred_eq, ← hX0]
    rcases (abs_eq zero_le_one).1 hu1 with h | h
    · rw [← hSn]
      exact (hf'x u).1 _ le_rfl
        (fun i _ ↦ by linarith [hcm.monotone (Fin.le_last i)]) (fun i hi ↦ absurd hi (by omega))
    · rw [← hS0]
      exact (hf'x u).1 _ (by omega) (fun i hi ↦ absurd hi (by omega))
        (fun i _ ↦ by linarith [hcm.monotone (Fin.zero_le i)])

end SymplecticGeometry

end
