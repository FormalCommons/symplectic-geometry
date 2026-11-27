/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition.Deriv
import SymplecticGeometry.Topology.Order.NhdsSet
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Analysis.Calculus.Deriv.Parity
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutoffs and reparametrizations built from the smooth transition function

This file collects smooth functions of one real variable built from `Real.smoothTransition`,
`expNegInvGlue` and smooth bumps, with the properties that later constructions use. The facts
about the derivative of `Real.smoothTransition` itself are in
`SymplecticGeometry/Analysis/SpecialFunctions/SmoothTransition/Deriv.lean`.

A function of class `C^n` on `(δ, ∞)` agrees on `[b, ∞)`, for each `b > δ`, with a function of
class `C^n` on `ℝ` (`ContDiffOn.exists_contDiff_eqOn_Ici`): its product with
`x ↦ smoothTransition ((x - m) / (b - m))`, where `m` is the midpoint of `[δ, b]`.

For a function `G` of class `C^n`, the product `t ↦ expNegInvGlue (t - t₀) * exp (G t)` is of
class `C^n` (`expNegInvGlue.contDiff_sub_mul_exp`), and where `G` has derivative `G'` at `t`, its
derivative there is `expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')`
(`expNegInvGlue.hasDerivAt_sub_mul_exp`), from Tau Ceti's `expNegInvGlue.hasDerivAt`.

For `c < c₁ < b` it gives a smooth map `ℝ → ℝ` that is the identity up to `c₁`, sends `(c, ∞)`
into `(c, b)`, and equals `c₁` from `b` on (`Real.exists_contDiff_eq_self_mapsTo_Ioo`): the map
`x ↦ c₁ + (x - c₁) (1 - smoothTransition ((x - c₁) / (b - c₁)))`.

For Tau Ceti's `TauCeti.collaredSmoothTransition`, the map `s ↦ smoothTransition (2 * s - 1 / 2)`,
it adds that the map is `0` near `0` and `1` near `1`
(`TauCeti.collaredSmoothTransition_eventuallyEq_zero`,
`TauCeti.collaredSmoothTransition_eventuallyEq_one`), that it is monotone
(`TauCeti.monotone_collaredSmoothTransition`), that `(1 - collaredSmoothTransition s) * η` lies in
`[0, η]` for `η ≥ 0` (`TauCeti.one_sub_collaredSmoothTransition_mul_mem_Icc`), and that its
derivative is positive at every point where its value is neither `0` nor `1`
(`TauCeti.deriv_collaredSmoothTransition_pos`).

For Tau Ceti's smooth lower truncation `TauCeti.smoothLowerTruncation a b`, the map
`s ↦ a + τ((s - a) / (b - a)) (s - a)` that is `a` up to `a` and the identity from `b` on, it
computes the derivative (`TauCeti.hasDerivAt_smoothLowerTruncation`) and shows that the map is
monotone for all `a` and `b` (`TauCeti.monotone_smoothLowerTruncation`), with positive derivative
on `(a, ∞)` when `a < b` (`TauCeti.deriv_smoothLowerTruncation_pos`). Conjugating by `x ↦ -x`
gives, for `c < b`, a smooth monotone map that is the identity up to `c`, equal to `b` from `b`
on, at most `b`, and with positive derivative on `(-∞, b)`
(`Real.exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici`).

It also gives a smooth map `c : ℝ → ℝ` that is the identity on a closed interval `[a, b]`,
takes its values in the open interval `(a - ε, b + ε)`, and is constant outside it
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`). It is `t ↦ m + f t * (t - m)` for
the midpoint `m` of `[a, b]` and a smooth bump `f` centred at `m`, equal to `1` on `[a, b]` and
supported in `(a - ε, b + ε)`. The construction adapts Tau Ceti's
`TauCeti.exists_contDiff_eventuallyEq_id_forall_mem_ball` to a prescribed interval on which the
map is the identity, including the degenerate case `a = b`. Since an open set containing `[a, b]`
contains some `(a - ε, b + ε)`, the values can also be kept in any such open set
(`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_of_isOpen`).

For any `0 ≤ r < R ≤ 1` it also gives a smooth odd function that is the identity on `[-r, r]`,
`1` on `[R, ∞)`, bounded by `1` in absolute value, at least `t` at every `t ∈ [0, 1]`, and with
derivative bounded by `1 + 2 (1 - r) / (R - r)` (`SymplecticGeometry.exists_contDiff_odd_clip`).
Its formula `ν t * ν (-t) * t + ν (-t) - ν t`, for an antitone cutoff `ν` that is `1` up to `r`
and `0` from `R` on, adapts the one in the proof of Tau Ceti's
`TauCeti.exists_contDiff_odd_truncation`; with a single cutoff the bounds by `1` and by `t`
follow. Taking `ν` from `TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`, with slope at
most `2 / (R - r)`, gives the bound on the derivative.

Finally it fixes a smooth odd function `SymplecticGeometry.smoothSign : ℝ → ℝ` that is the
identity on `[-1/4, 1/4]`, `1` on `[1/2, ∞)` and `-1` on `(-∞, -1/2]`, bounded by `1` in
absolute value, and has the sign of its argument, by choosing the function of
`SymplecticGeometry.exists_contDiff_odd_clip` for `r = 1/4` and `R = 1/2`; only these
properties are used, so no formula is given.

For the flat function `f = expNegInvGlue`, whose derivatives at `x > 0` are `x⁻² f x` and
`(x⁻⁴ - 2 x⁻³) f x`, the second derivative dominates `K` times the first once
`(|K| + 2) x ≤ 1` (`expNegInvGlue.mul_deriv_le_deriv_deriv`), so for every `K` at all small
`x > 0` (`expNegInvGlue.eventually_mul_deriv_le_deriv_deriv`). From it the file builds, for
`a < b`, a smooth antitone cutoff with values in `[0, 1]`, equal to `1` up to `a`, to `0` from `b`
on and positive before `b`, with derivative `0` outside `(a, b)` and with `K |β'| ≤ β''` on some
interval `[b - s, b)` for each `K`
(`SymplecticGeometry.exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv`). It is
`χ + (1 - χ) g` for `g r = f (b - r) / f (b - a)` and a cutoff `χ` from Tau Ceti's
`TauCeti.exists_contDiff_antitone_cutoff` that vanishes from the midpoint of `[a, b]` on, so it
equals `g` near `b`. Such a cutoff in the radius is used in the modification of a function on a
half-cylinder in the proof of the symplectic h-principle (see McDuff–Salamon, Theorem 7.3.1).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace expNegInvGlue

open Filter Topology

/-- At each `x > 0` with `(|K| + 2) x ≤ 1`, the second derivative of `expNegInvGlue` is at least
`K` times its first derivative. -/
theorem mul_deriv_le_deriv_deriv {K x : ℝ} (hx : 0 < x) (hKx : (|K| + 2) * x ≤ 1) :
    K * deriv expNegInvGlue x ≤ deriv (deriv expNegInvGlue) x := by
  rw [(hasDerivAt x).deriv, deriv_deriv]
  have hf := pos_of_pos hx
  -- After multiplying by `x ^ 4`, the inequality reads `K x ^ 2 ≤ 1 - 2 x`.
  have hx1 : x ≤ 1 := by nlinarith [abs_nonneg K]
  have key : K * x ^ 2 ≤ 1 - 2 * x := by
    nlinarith [le_abs_self K, abs_nonneg K, mul_le_mul_of_nonneg_left hx1 (abs_nonneg K),
      mul_le_mul_of_nonneg_left hx1 hx.le]
  have hxi : 0 < x⁻¹ := inv_pos.2 hx
  have h : K * x⁻¹ ^ 2 ≤ x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3 := by
    have := mul_le_mul_of_nonneg_left key (pow_pos hxi 4).le
    have e₁ : x⁻¹ ^ 4 * (K * x ^ 2) = K * x⁻¹ ^ 2 := by field_simp
    have e₂ : x⁻¹ ^ 4 * (1 - 2 * x) = x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3 := by field_simp
    linarith
  nlinarith [mul_le_mul_of_nonneg_right h hf.le]

/-- For every `K`, the second derivative of `expNegInvGlue` is at least `K` times its first
derivative at all `x > 0` close enough to `0`. -/
theorem eventually_mul_deriv_le_deriv_deriv (K : ℝ) :
    ∀ᶠ x in 𝓝[>] 0, K * deriv expNegInvGlue x ≤ deriv (deriv expNegInvGlue) x := by
  have hK : 0 < (|K| + 2)⁻¹ := inv_pos.2 (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hK] with x hx
  refine mul_deriv_le_deriv_deriv hx.1 ?_
  have hK2 : (0 : ℝ) < |K| + 2 := by positivity
  have := mul_lt_mul_of_pos_left hx.2 hK2
  rw [mul_inv_cancel₀ hK2.ne'] at this
  exact this.le

open Real

/-- If `G` is of class `C^n`, so is `t ↦ expNegInvGlue (t - t₀) * exp (G t)`. -/
theorem contDiff_sub_mul_exp {n : ℕ∞} {G : ℝ → ℝ} (t₀ : ℝ) (hG : ContDiff ℝ n G) :
    ContDiff ℝ n fun t ↦ expNegInvGlue (t - t₀) * exp (G t) :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul hG.exp

/-- The derivative of `t ↦ expNegInvGlue (t - t₀) * exp (G t)` at `t` is
`expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')`, where `G'` is the derivative of `G`
at `t`. -/
theorem hasDerivAt_sub_mul_exp {G : ℝ → ℝ} {G' : ℝ} (t₀ : ℝ) {t : ℝ} (hG : HasDerivAt G G' t) :
    HasDerivAt (fun u ↦ expNegInvGlue (u - t₀) * exp (G u))
      (expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')) t := by
  convert ((hasDerivAt (t - t₀)).comp_sub_const t t₀).mul hG.exp using 1
  ring

end expNegInvGlue

namespace Real

open Set
open scoped ContDiff

/-- For `c < c₁ < b` there is a smooth function `φ : ℝ → ℝ` that is the identity on `Iic c₁`,
maps `Ioi c` into `Ioo c b`, and is constant, equal to `c₁`, on `Ici b`. -/
theorem exists_contDiff_eq_self_mapsTo_Ioo {c c₁ b : ℝ} (hc : c < c₁) (hb : c₁ < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x ≤ c₁, φ x = x) ∧ MapsTo φ (Ioi c) (Ioo c b) ∧
      ∀ x, b ≤ x → φ x = c₁ := by
  have hδ : 0 < b - c₁ := sub_pos.2 hb
  have hone {x : ℝ} (hxb : b ≤ x) : smoothTransition ((x - c₁) / (b - c₁)) = 1 :=
    smoothTransition.one_of_one_le ((one_le_div hδ).2 (sub_le_sub_right hxb c₁))
  refine ⟨fun x ↦ c₁ + (x - c₁) * (1 - smoothTransition ((x - c₁) / (b - c₁))), ?_, ?_, ?_,
    fun x hxb ↦ by simp [hone hxb]⟩
  · fun_prop
  · intro x hx
    dsimp only
    rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
    ring
  · intro x hx
    dsimp only
    rcases le_or_gt x c₁ with hx₁ | hx₁
    · rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
      exact ⟨by simp only [mem_Ioi] at hx; linarith, by linarith⟩
    have h0 := smoothTransition.le_one ((x - c₁) / (b - c₁))
    have h1 := smoothTransition.nonneg ((x - c₁) / (b - c₁))
    refine ⟨by nlinarith, ?_⟩
    rcases lt_or_ge x b with hxb | hxb
    · nlinarith
    · rw [hone hxb]
      linarith

end Real

namespace TauCeti

open Filter Topology

/-- `collaredSmoothTransition` is `0` on a neighbourhood of `0`. -/
theorem collaredSmoothTransition_eventuallyEq_zero :
    collaredSmoothTransition =ᶠ[𝓝 0] fun _ ↦ 0 := by
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  exact collaredSmoothTransition_eq_zero_of_le hs.le

/-- `collaredSmoothTransition` is `1` on a neighbourhood of `1`. -/
theorem collaredSmoothTransition_eventuallyEq_one :
    collaredSmoothTransition =ᶠ[𝓝 1] fun _ ↦ 1 := by
  filter_upwards [Ioi_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1)] with s hs
  exact collaredSmoothTransition_eq_one_of_ge hs.le

/-- `collaredSmoothTransition` is monotone. -/
theorem monotone_collaredSmoothTransition : Monotone collaredSmoothTransition := fun s t hst ↦ by
  rw [collaredSmoothTransition_def, collaredSmoothTransition_def]
  exact Real.smoothTransition.monotone (by linarith)

/-- For `η ≥ 0`, the multiple `(1 - collaredSmoothTransition s) * η` lies in `[0, η]`. -/
theorem one_sub_collaredSmoothTransition_mul_mem_Icc {η : ℝ} (hη : 0 ≤ η) (s : ℝ) :
    (1 - collaredSmoothTransition s) * η ∈ Set.Icc 0 η := by
  obtain ⟨h₀, h₁⟩ := collaredSmoothTransition_mem s
  exact ⟨mul_nonneg (sub_nonneg.2 h₁) hη, mul_le_of_le_one_left hη (by linarith)⟩

/-- Where `collaredSmoothTransition` is neither `0` nor `1`, its derivative is positive. -/
theorem deriv_collaredSmoothTransition_pos {s : ℝ}
    (h₀ : collaredSmoothTransition s ≠ 0) (h₁ : collaredSmoothTransition s ≠ 1) :
    0 < deriv collaredSmoothTransition s := by
  rw [collaredSmoothTransition_def] at h₀ h₁
  have hs₀ : 0 < 2 * s - 1 / 2 :=
    lt_of_not_ge fun h ↦ h₀ (Real.smoothTransition.zero_of_nonpos h)
  have hs₁ : 2 * s - 1 / 2 < 1 :=
    lt_of_not_ge fun h ↦ h₁ (Real.smoothTransition.one_of_one_le h)
  have hd := (((hasDerivAt_id' s).const_mul 2).sub_const (1 / 2)).smoothTransition
    |>.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ collaredSmoothTransition_def r)
  rw [hd.deriv, mul_one]
  exact mul_pos (Real.smoothTransition.deriv_pos hs₀ hs₁) two_pos

/-- The derivative of the smooth lower truncation `a + τ((s - a) / (b - a)) (s - a)` is
`τ'((s - a) / (b - a)) (s - a) / (b - a) + τ((s - a) / (b - a))`. -/
theorem hasDerivAt_smoothLowerTruncation (a b s : ℝ) :
    HasDerivAt (smoothLowerTruncation a b)
      (deriv Real.smoothTransition ((s - a) / (b - a)) / (b - a) * (s - a) +
        Real.smoothTransition ((s - a) / (b - a))) s := by
  have hu := ((hasDerivAt_id s).sub_const a).div_const (b - a)
  have h := (hu.smoothTransition.mul ((hasDerivAt_id s).sub_const a)).const_add a
  convert h using 1
  · exact funext (smoothLowerTruncation_def a b)
  · simp only [id]
    ring

/-- The smooth lower truncation is monotone. -/
theorem monotone_smoothLowerTruncation (a b : ℝ) : Monotone (smoothLowerTruncation a b) := by
  refine monotone_of_deriv_nonneg
    ((contDiff_smoothLowerTruncation a b (n := 1)).differentiable one_ne_zero) fun s ↦ ?_
  rw [(hasDerivAt_smoothLowerTruncation a b s).deriv]
  have h₁ := Real.smoothTransition.mul_deriv_nonneg ((s - a) / (b - a))
  have h₂ := Real.smoothTransition.nonneg ((s - a) / (b - a))
  have : deriv Real.smoothTransition ((s - a) / (b - a)) / (b - a) * (s - a) =
      (s - a) / (b - a) * deriv Real.smoothTransition ((s - a) / (b - a)) := by ring
  linarith

/-- For `a < b`, the smooth lower truncation has positive derivative on `(a, ∞)`. -/
theorem deriv_smoothLowerTruncation_pos {a b s : ℝ} (hab : a < b) (hs : a < s) :
    0 < deriv (smoothLowerTruncation a b) s := by
  rw [(hasDerivAt_smoothLowerTruncation a b s).deriv]
  have := Real.smoothTransition.deriv_nonneg ((s - a) / (b - a))
  have := Real.smoothTransition.pos_of_pos (div_pos (sub_pos.2 hs) (sub_pos.2 hab))
  have := sub_pos.2 hab
  have := sub_pos.2 hs
  positivity

end TauCeti

namespace Real

open Set
open scoped ContDiff

/-- For `c < b` there is a smooth monotone function `φ : ℝ → ℝ` that is the identity on
`(-∞, c]`, equal to `b` on `[b, ∞)`, at most `b` everywhere, and with positive derivative on
`(-∞, b)`. It is `x ↦ -smoothLowerTruncation (-b) (-c) (-x)`; the mirror form, constant up to `c`
and the identity from `b` on, is `TauCeti.smoothLowerTruncation c b` itself
(`TauCeti.monotone_smoothLowerTruncation`, `TauCeti.deriv_smoothLowerTruncation_pos`). -/
theorem exists_contDiff_monotone_eqOn_id_Iic_eqOn_const_Ici {c b : ℝ} (hcb : c < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Monotone φ ∧ EqOn φ id (Iic c) ∧
      EqOn φ (fun _ ↦ b) (Ici b) ∧ (∀ x, φ x ≤ b) ∧ ∀ x < b, 0 < deriv φ x := by
  have hbc : -b < -c := neg_lt_neg hcb
  refine ⟨fun x ↦ -TauCeti.smoothLowerTruncation (-b) (-c) (-x),
    ((TauCeti.contDiff_smoothLowerTruncation _ _).comp contDiff_neg).neg,
    fun x y hxy ↦ neg_le_neg (TauCeti.monotone_smoothLowerTruncation _ _ (neg_le_neg hxy)),
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · simp [TauCeti.smoothLowerTruncation_of_right_le hbc (neg_le_neg (mem_Iic.1 hx))]
  · simp [TauCeti.smoothLowerTruncation_of_le_left hbc.le (neg_le_neg (mem_Ici.1 hx))]
  · exact neg_le.1 (TauCeti.le_smoothLowerTruncation hbc.le _)
  · rw [deriv.fun_neg, deriv_comp_neg, neg_neg]
    exact TauCeti.deriv_smoothLowerTruncation_pos hbc (neg_lt_neg hx)

end Real

namespace ContDiffOn

open Filter Set

/-- A function of class `C^n` on `(δ, ∞)` agrees on `[b, ∞)`, for any `b > δ`, with a function of
class `C^n` on all of `ℝ`. -/
theorem exists_contDiff_eqOn_Ici {n : ℕ∞} {g : ℝ → ℝ} {δ b : ℝ} (hg : ContDiffOn ℝ n g (Ioi δ))
    (hb : δ < b) : ∃ f : ℝ → ℝ, ContDiff ℝ n f ∧ EqOn f g (Ici b) := by
  set m := (δ + b) / 2
  have hm : 0 < b - m := by simp only [m]; linarith
  have hδm : δ < m := by simp only [m]; linarith
  refine ⟨fun x ↦ Real.smoothTransition ((x - m) / (b - m)) * g x,
    contDiff_iff_contDiffAt.2 fun x ↦ ?_, fun x (hx : b ≤ x) ↦ ?_⟩
  · rcases lt_or_ge δ x with hx | hx
    · exact (Real.smoothTransition.contDiffAt.comp x (by fun_prop)).mul
        (hg.contDiffAt (Ioi_mem_nhds hx))
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (hx.trans_lt hδm)] with y (hy : y < m)
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hm.le), zero_mul]
  · simp only
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hm).2 (by linarith)), one_mul]

end ContDiffOn

namespace SymplecticGeometry

open Filter Topology
open scoped ContDiff

/-- A smooth map `ℝ → ℝ` that is the identity on the closed interval `[a, b]`, takes its values
in the open interval `(a - ε, b + ε)`, and is equal to the midpoint `(a + b) / 2` outside that
interval, for any `a ≤ b` and `ε > 0`. -/
theorem exists_contDiff_eqOn_id_Icc_mem_Ioo {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧ Set.EqOn c id (Set.Icc a b) ∧
      (∀ t, c t ∈ Set.Ioo (a - ε) (b + ε)) ∧
      ∀ t ∉ Set.Ioo (a - ε) (b + ε), c t = (a + b) / 2 := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (a + b) / 2 := ⟨_, rfl⟩
  let f : ContDiffBump m := ⟨(b - a) / 2 + ε / 2, (b - a) / 2 + ε, by linarith, by linarith⟩
  have hrIn : f.rIn = (b - a) / 2 + ε / 2 := rfl
  have hrOut : f.rOut = (b - a) / 2 + ε := rfl
  refine ⟨fun t ↦ m + f t * (t - m), contDiff_const.add (f.contDiff.mul (contDiff_id.sub
    contDiff_const)), fun t ht ↦ ?_, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · have : f t = 1 := f.one_of_mem_closedBall <| by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrIn]
      constructor <;> linarith [ht.1, ht.2]
    simp [this]
  · suffices |f t * (t - m)| < (b - a) / 2 + ε by
      rw [abs_lt] at this
      dsimp only
      constructor <;> linarith [this.1, this.2]
    rw [← hrOut]
    rcases lt_or_ge (dist t m) f.rOut with ht | ht
    · rw [abs_mul, abs_of_nonneg f.nonneg, ← Real.dist_eq]
      exact (mul_le_of_le_one_left dist_nonneg f.le_one).trans_lt ht
    · rw [f.zero_of_le_dist ht, zero_mul, abs_zero]
      exact f.rOut_pos
  · -- Outside `(a - ε, b + ε)`, `t` is at distance at least `rOut` from `m`, where `f` is `0`.
    have : f.rOut ≤ dist t m := by
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht
      rw [Real.dist_eq, hrOut, le_abs]
      rcases ht with ht | ht
      · right; linarith
      · left; linarith
    simp [f.zero_of_le_dist this, hm]

/-- A smooth map `ℝ → ℝ` that is the identity on the closed interval `[a, b]` and takes its
values in a given open set `U ⊇ [a, b]`, for any `a ≤ b`. -/
theorem exists_contDiff_eqOn_id_Icc_mem_of_isOpen {a b : ℝ} {U : Set ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hIU : Set.Icc a b ⊆ U) :
    ∃ c : ℝ → ℝ, ContDiff ℝ ∞ c ∧ Set.EqOn c id (Set.Icc a b) ∧ ∀ t, c t ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := hU.exists_pos_Ioo_subset_of_Icc_subset hIU
  obtain ⟨c, hc, hcI, hcU, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo hab hδ
  exact ⟨c, hc, hcI, fun t ↦ hδU (hcU t)⟩

/-- For a differentiable `ν` with values in `[0, 1]`, equal to `1` on `(-∞, r]` for some
`0 ≤ r ≤ R ≤ 1`, with `|ν'| ≤ τ` everywhere and `ν' = 0` outside `(r, R)`, the derivative of
`t ↦ ν t * ν (-t) * t + ν (-t) - ν t` at each `t ≥ 0` is at most `1 + τ (1 - r)` in absolute
value. -/
private theorem abs_deriv_clip_le {ν : ℝ → ℝ} {r R τ : ℝ} (hν : Differentiable ℝ ν) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hR : R ≤ 1) (hν0 : ∀ t, 0 ≤ ν t) (hν1 : ∀ t, ν t ≤ 1) (hνr : ∀ t ≤ r, ν t = 1)
    (hντ : ∀ t, |deriv ν t| ≤ τ) (hν' : ∀ t ∉ Set.Ioo r R, deriv ν t = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    |deriv (fun s ↦ ν s * ν (-s) * s + ν (-s) - ν s) t| ≤ 1 + τ * (1 - r) := by
  -- At `t ≥ 0` the derivative is `ν t - ν' t * (1 - t)`, and `ν'` vanishes outside `(r, R)`.
  have hd (s : ℝ) : HasDerivAt ν (deriv ν s) s := (hν s).hasDerivAt
  have hdn : HasDerivAt (fun s ↦ ν (-s)) (-deriv ν (-t)) t := by
    simpa [Function.comp_def] using (hd (-t)).comp t (hasDerivAt_neg t)
  have h : deriv (fun s ↦ ν s * ν (-s) * s + ν (-s) - ν s) t = ν t - deriv ν t * (1 - t) := by
    have hD : HasDerivAt (fun s ↦ ν s * ν (-s) * s + ν (-s) - ν s) _ t :=
      (((hd t).mul hdn).mul (hasDerivAt_id' t)).add hdn |>.sub (hd t)
    rw [hD.deriv, Pi.mul_apply, hνr (-t) (by linarith), hν' (-t) fun h ↦ by linarith [h.1]]
    ring
  rw [h]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (hν0 t), abs_mul]
  have hτ : 0 ≤ τ := (abs_nonneg _).trans (hντ 0)
  by_cases htI : t ∈ Set.Ioo r R
  · have h₁ : |1 - t| ≤ 1 - r := by
      rw [abs_of_nonneg (by linarith [htI.2, hR])]; linarith [htI.1]
    linarith [hν1 t, mul_le_mul (hντ t) h₁ (abs_nonneg _) hτ]
  · rw [hν' t htI, abs_zero, zero_mul, add_zero]
    nlinarith [hν1 t, hrR.trans hR]

/-- A smooth odd function `ℝ → ℝ` that is the identity on `[-r, r]`, `1` on `[R, ∞)`, bounded
by `1` in absolute value, at least `t` at every `t ∈ [0, 1]`, and with derivative bounded by
`1 + 2 (1 - r) / (R - r)` in absolute value, for any `0 ≤ r < R ≤ 1`. By oddness it is `-1` on
`(-∞, -R]` and at most `t` at every `t ∈ [-1, 0]`, so it moves no point of `[-1, 1]` away from
the end `±1` of its sign. -/
theorem exists_contDiff_odd_clip {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : R ≤ 1) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ Function.Odd f ∧ (∀ t, |t| ≤ r → f t = t) ∧
      (∀ t, R ≤ t → f t = 1) ∧ (∀ t, |f t| ≤ 1) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ f t) ∧
      ∀ t, |deriv f t| ≤ 1 + 2 * (1 - r) / (R - r) := by
  have hRr : 0 < R - r := by linarith
  obtain ⟨ν, hν, hνa, hν0, hνR, hνr, hντ, hν'⟩ :=
    TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le (τ := 2 / (R - r)) hrR zero_le_one
      (by rw [div_mul_cancel₀ _ hRr.ne']; norm_num)
  have hν1 (t : ℝ) : ν t ≤ 1 := by
    rcases le_total t r with ht | ht
    · exact (hνr t ht).le
    · exact (hνa ht).trans (hνr r le_rfl).le
  -- For `t ≥ 0` the function below is `1 - ν t * (1 - t)`.
  set f : ℝ → ℝ := fun t ↦ ν t * ν (-t) * t + ν (-t) - ν t
  have hodd : Function.Odd f := fun t ↦ by simp only [f, neg_neg]; ring
  have hpos {t : ℝ} (ht : 0 ≤ t) : f t = 1 - ν t * (1 - t) := by
    simp only [f, hνr (-t) (by linarith)]
    ring
  have hle (t : ℝ) (ht : 0 ≤ t) : |f t| ≤ 1 := by
    rcases le_total R t with htR | htR
    · rw [hpos ht, hνR t htR]; simp
    · rw [hpos ht, abs_le]
      have : 0 ≤ ν t * (1 - t) := mul_nonneg (hν0 t) (by linarith)
      have : ν t * (1 - t) ≤ 1 := by nlinarith [hν1 t, hν0 t]
      constructor <;> linarith
  have hdle (t : ℝ) (ht : 0 ≤ t) : |deriv f t| ≤ 1 + 2 * (1 - r) / (R - r) := by
    rw [← div_mul_eq_mul_div]
    exact abs_deriv_clip_le (hν.differentiable (by simp)) hr hrR.le hR hν0 hν1 hνr hντ hν' ht
  refine ⟨f, by fun_prop, hodd, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ↦ ?_, fun t ht ↦ ?_,
    fun t ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := abs_le.1 ht
    simp only [f, hνr t h₂, hνr (-t) (by linarith)]
    ring
  · rw [hpos (hr.trans (hrR.le.trans ht)), hνR t ht]
    ring
  · rcases le_total 0 t with ht | ht
    · exact hle t ht
    · have := hle (-t) (by linarith)
      rwa [hodd, abs_neg] at this
  · rw [hpos ht.1]
    nlinarith [hν1 t, ht.2]
  · rcases le_total 0 t with ht | ht
    · exact hdle t ht
    · rw [← TauCeti.deriv_neg_eq_of_eventually_odd (.of_forall hodd)]
      exact hdle (-t) (by linarith)

/-- A smooth odd function `ℝ → ℝ` that is the identity on `[-1/4, 1/4]`, `1` on `[1/2, ∞)` and
`-1` on `(-∞, -1/2]`, bounded by `1` in absolute value, and with the sign of its argument: the
function that `SymplecticGeometry.exists_contDiff_odd_clip` gives for `r = 1/4` and
`R = 1/2`. -/
noncomputable def smoothSign : ℝ → ℝ :=
  (exists_contDiff_odd_clip (r := 1 / 4) (R := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)).choose

private theorem smoothSign_spec :
    ContDiff ℝ ∞ smoothSign ∧ Function.Odd smoothSign ∧
      (∀ t, |t| ≤ 1 / 4 → smoothSign t = t) ∧ (∀ t, 1 / 2 ≤ t → smoothSign t = 1) ∧
      (∀ t, t ≤ -(1 / 2) → smoothSign t = -1) ∧ (∀ t, 0 < t → 0 < smoothSign t) ∧
      (∀ t, t < 0 → smoothSign t < 0) ∧ ∀ t, |smoothSign t| ≤ 1 := by
  obtain ⟨hc, hodd, hid, hone, habs, hge, -⟩ :
      ContDiff ℝ ∞ smoothSign ∧ Function.Odd smoothSign ∧
      (∀ t, |t| ≤ 1 / 4 → smoothSign t = t) ∧ (∀ t, 1 / 2 ≤ t → smoothSign t = 1) ∧
      (∀ t, |smoothSign t| ≤ 1) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ smoothSign t) ∧
      ∀ t, |deriv smoothSign t| ≤ 1 + 2 * (1 - 1 / 4) / (1 / 2 - 1 / 4) :=
    (exists_contDiff_odd_clip (r := 1 / 4) (R := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)).choose_spec
  -- Positive on `(0, 1]` since it is at least `t` there, and `1` from `1/2` on.
  have hpos (t : ℝ) (ht : 0 < t) : 0 < smoothSign t := by
    rcases le_total t 1 with ht₁ | ht₁
    · exact ht.trans_le (hge t ⟨ht.le, ht₁⟩)
    · exact one_pos.trans_eq (hone t (by linarith)).symm
  refine ⟨hc, hodd, hid, hone, fun t ht ↦ ?_, hpos, fun t ht ↦ ?_, habs⟩
  · rw [← neg_neg t, hodd (-t), hone (-t) (by linarith)]
  · rw [← neg_neg t, hodd (-t), neg_lt_zero]
    exact hpos (-t) (by linarith)

/-- `smoothSign` is smooth. -/
theorem contDiff_smoothSign : ContDiff ℝ ∞ smoothSign :=
  smoothSign_spec.1

/-- `smoothSign` is the identity on `[-1/4, 1/4]`. -/
theorem smoothSign_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 4) : smoothSign s = s :=
  smoothSign_spec.2.2.1 s hs

/-- `smoothSign` is `1` on `[1/2, ∞)`. -/
theorem smoothSign_of_le {s : ℝ} (hs : 1 / 2 ≤ s) : smoothSign s = 1 :=
  smoothSign_spec.2.2.2.1 s hs

/-- `smoothSign` is `-1` on `(-∞, -1/2]`. -/
theorem smoothSign_of_le_neg {s : ℝ} (hs : s ≤ -(1 / 2)) : smoothSign s = -1 :=
  smoothSign_spec.2.2.2.2.1 s hs

/-- `smoothSign` takes its values in `[-1, 1]`. -/
theorem abs_smoothSign_le_one (s : ℝ) : |smoothSign s| ≤ 1 :=
  smoothSign_spec.2.2.2.2.2.2.2 s

/-- `smoothSign` is odd. -/
@[simp]
theorem smoothSign_neg (s : ℝ) : smoothSign (-s) = -smoothSign s :=
  smoothSign_spec.2.1 s

@[simp]
theorem smoothSign_zero : smoothSign 0 = 0 :=
  smoothSign_of_abs_le (by norm_num)

@[simp]
theorem smoothSign_pos_iff {s : ℝ} : 0 < smoothSign s ↔ 0 < s := by
  refine ⟨fun h ↦ lt_of_not_ge fun hs ↦ ?_, smoothSign_spec.2.2.2.2.2.1 s⟩
  rcases hs.lt_or_eq with hs | rfl
  · exact (smoothSign_spec.2.2.2.2.2.2.1 s hs).not_gt h
  · simp at h

@[simp]
theorem smoothSign_lt_zero_iff {s : ℝ} : smoothSign s < 0 ↔ s < 0 := by
  rw [← neg_pos, ← smoothSign_neg, smoothSign_pos_iff, neg_pos]

@[simp]
theorem smoothSign_eq_zero_iff {s : ℝ} : smoothSign s = 0 ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ smoothSign_zero⟩
  rcases lt_trichotomy s 0 with hs | hs | hs
  · exact absurd h (smoothSign_lt_zero_iff.2 hs).ne
  · exact hs
  · exact absurd h (smoothSign_pos_iff.2 hs).ne'

@[simp]
theorem smoothSign_nonpos_iff {s : ℝ} : smoothSign s ≤ 0 ↔ s ≤ 0 := by
  rw [← not_lt, smoothSign_pos_iff, not_lt]

@[simp]
theorem smoothSign_nonneg_iff {s : ℝ} : 0 ≤ smoothSign s ↔ 0 ≤ s := by
  rw [← not_lt, smoothSign_lt_zero_iff, not_lt]

/-- A smooth antitone cutoff `β : ℝ → [0, 1]` that is `1` on `(-∞, a]`, `0` on `[b, ∞)` and
positive on `(-∞, b)`, for any `a < b`, with derivative `0` on `(-∞, a]` and on `[b, ∞)`, and
whose second derivative dominates any multiple of its first derivative near `b`: for every `K`
there is `0 < s < (b - a) / 2` with `K |β' r| ≤ β'' r` for all `r ∈ [b - s, b)`. Near `b` it is
`exp (-1 / (b - r))` up to a constant factor. -/
theorem exists_contDiff_antitone_cutoff_mul_abs_deriv_le_deriv_deriv {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ r, β r ∈ Set.Icc 0 1) ∧ Antitone β ∧
      Set.EqOn β 1 (Set.Iic a) ∧ Set.EqOn β 0 (Set.Ici b) ∧ Set.EqOn (deriv β) 0 (Set.Iic a) ∧
      Set.EqOn (deriv β) 0 (Set.Ici b) ∧ (∀ r < b, 0 < β r) ∧
      ∀ K : ℝ, ∃ s, 0 < s ∧ s < (b - a) / 2 ∧
        ∀ r ∈ Set.Ico (b - s) b, K * |deriv β r| ≤ deriv (deriv β) r := by
  set f := expNegInvGlue
  set m := (a + b) / 2
  have ham : a < m := by simp only [m]; linarith
  have hmb : m < b := by simp only [m]; linarith
  obtain ⟨χ, hχ, hχa, hχ0, hχm, hχ1, -⟩ := TauCeti.exists_contDiff_antitone_cutoff ham zero_le_one
  have hχle (r : ℝ) : χ r ≤ 1 := by
    rcases le_total r a with hr | hr
    · exact (hχ1 r hr).le
    · exact (hχa hr).trans (hχ1 a le_rfl).le
  -- `g r = f (b - r) / f (b - a)` is the profile near `b`; `β` interpolates from `1` to it.
  have hc : 0 < f (b - a) := expNegInvGlue.pos_of_pos (sub_pos.2 hab)
  set g : ℝ → ℝ := fun r ↦ f (b - r) / f (b - a)
  have hg0 (r : ℝ) : 0 ≤ g r := div_nonneg (expNegInvGlue.nonneg _) hc.le
  have hga : Antitone g := fun r s hrs ↦
    div_le_div_of_nonneg_right (expNegInvGlue.monotone (by linarith)) hc.le
  have hg1 {r : ℝ} (hr : a ≤ r) : g r ≤ 1 :=
    (div_le_one hc).2 (expNegInvGlue.monotone (by linarith))
  have hgb {r : ℝ} (hr : b ≤ r) : g r = 0 := by
    simp [g, f, expNegInvGlue.zero_of_nonpos (sub_nonpos.2 hr)]
  have hgpos {r : ℝ} (hr : r < b) : 0 < g r :=
    div_pos (expNegInvGlue.pos_of_pos (sub_pos.2 hr)) hc
  set β : ℝ → ℝ := fun r ↦ χ r + (1 - χ r) * g r
  have hβa {r : ℝ} (hr : r ≤ a) : β r = 1 := by simp [β, hχ1 r hr]
  have hβm {r : ℝ} (hr : m ≤ r) : β r = g r := by simp [β, hχm r hr]
  have hβ1 (r : ℝ) : 1 - β r = (1 - χ r) * (1 - g r) := by simp only [β]; ring
  have hβnn (r : ℝ) : 0 ≤ β r := add_nonneg (hχ0 r) (mul_nonneg (sub_nonneg.2 (hχle r)) (hg0 r))
  have hβle (r : ℝ) : β r ≤ 1 := by
    rcases le_total r a with hr | hr
    · exact (hβa hr).le
    · linarith [hβ1 r, mul_nonneg (sub_nonneg.2 (hχle r)) (sub_nonneg.2 (hg1 hr))]
  have hβb {r : ℝ} (hr : b ≤ r) : β r = 0 := by rw [hβm (hmb.le.trans hr), hgb hr]
  refine ⟨β, ?_, fun r ↦ ⟨hβnn r, hβle r⟩, fun r s hrs ↦ ?_, fun r hr ↦ hβa hr,
    fun r hr ↦ hβb hr, fun r hr ↦ ?_, fun r hr ↦ ?_, fun r hr ↦ ?_, fun K ↦ ?_⟩
  · exact hχ.add ((contDiff_const.sub hχ).mul
      ((expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)).div_const _))
  · rcases le_total s a with hs | hs
    · rw [hβa hs, hβa (hrs.trans hs)]
    rcases le_total r a with hr | hr
    · rw [hβa hr]; linarith [hβ1 s, mul_nonneg (sub_nonneg.2 (hχle s)) (sub_nonneg.2 (hg1 hs))]
    have := mul_le_mul (sub_le_sub_left (hχa hrs) 1) (sub_le_sub_left (hga hrs) 1)
      (sub_nonneg.2 (hg1 hr)) (sub_nonneg.2 (hχle s))
    linarith [hβ1 r, hβ1 s]
  · -- `β` attains its maximum `1` at `r ≤ a` and its minimum `0` at `r ≥ b`.
    exact IsLocalMax.deriv_eq_zero (.of_forall fun u ↦ (hβle u).trans_eq (hβa hr).symm)
  · exact IsLocalMin.deriv_eq_zero (.of_forall fun u ↦ (hβb hr).trans_le (hβnn u))
  · rcases (hχ0 r).lt_or_eq with h | h
    · exact add_pos_of_pos_of_nonneg h (mul_nonneg (sub_nonneg.2 (hχle r)) (hg0 r))
    · simp only [β, ← h, zero_add, sub_zero, one_mul]
      exact hgpos hr
  -- Near `b`, `β = g`, whose derivatives are those of `f` at `b - r`, up to sign and the factor.
  obtain ⟨ε, hε, hεs⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (expNegInvGlue.eventually_mul_deriv_le_deriv_deriv K)
  set s := min ((b - a) / 4) (ε / 2)
  have hs0 : 0 < s := lt_min (by linarith) (half_pos hε)
  have hsab : s < (b - a) / 2 := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨s, hs0, hsab, fun r hr ↦ ?_⟩
  have hdg : deriv g = fun t ↦ -deriv f (b - t) / f (b - a) :=
    funext fun t ↦ by simp only [g, deriv_div_const, deriv_comp_const_sub]
  have hddg : deriv (deriv g) r = deriv (deriv f) (b - r) / f (b - a) := by
    rw [hdg]; simp only [neg_div, deriv.fun_neg, deriv_div_const, deriv_comp_const_sub, neg_neg]
  have hs₁ : s ≤ (b - a) / 4 := min_le_left _ _
  have hs₂ : s ≤ ε / 2 := min_le_right _ _
  have hmr : m < r := by simp only [m]; linarith [hr.1]
  have hβg : β =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hmr] with t ht using hβm ht.le
  have hx : b - r ∈ Set.Ioo 0 ε := ⟨sub_pos.2 hr.2, by linarith [hr.1]⟩
  rw [hβg.deriv_eq, hβg.deriv.deriv_eq, hddg, congrFun hdg r, abs_div, abs_neg, abs_of_pos hc,
    abs_of_nonneg expNegInvGlue.monotone.deriv_nonneg, mul_div_assoc']
  exact div_le_div_of_nonneg_right (hεs hx) hc.le

end SymplecticGeometry

end
