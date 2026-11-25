/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Analysis.Calculus.Deriv.Parity
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The derivative of the smooth transition function, and a reparametrization of time

Mathlib's `Real.smoothTransition` is `0` on `(-∞, 0]`, `1` on `[1, ∞)`, and the quotient
`f x / (f x + f (1 - x))` in between, with `f = expNegInvGlue`. Tau Ceti shows that its derivative
vanishes outside `[0, 1]`. This file shows that the derivative is positive on the open interval
`(0, 1)` (`Real.smoothTransition.deriv_pos`): by the quotient rule it is
`(f' x f (1 - x) + f x f' (1 - x)) / (f x + f (1 - x)) ^ 2`, and `f` and `f'` are positive on
`(0, ∞)`.

For `c < c₁ < b` it gives a smooth map `ℝ → ℝ` that is the identity up to `c₁`, sends `(c, ∞)`
into `(c, b)`, and equals `c₁` from `b` on (`Real.exists_contDiff_eq_self_mapsTo_Ioo`): the map
`x ↦ c₁ + (x - c₁) (1 - smoothTransition ((x - c₁) / (b - c₁)))`.

For Tau Ceti's `TauCeti.collaredSmoothTransition`, the map `s ↦ smoothTransition (2 * s - 1 / 2)`,
it adds that the map is `0` near `0` and `1` near `1`
(`TauCeti.collaredSmoothTransition_eventuallyEq_zero`,
`TauCeti.collaredSmoothTransition_eventuallyEq_one`), and that its derivative is positive at
every point where its value is neither `0` nor `1` (`TauCeti.deriv_collaredSmoothTransition_pos`).

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
-/

public section

namespace Real.smoothTransition

/-- The smooth transition function has positive derivative on the open interval `(0, 1)`. -/
theorem deriv_pos {x : ℝ} (h₀ : 0 < x) (h₁ : x < 1) : 0 < deriv smoothTransition x := by
  set f := expNegInvGlue
  have hx : 0 < f x := expNegInvGlue.pos_of_pos h₀
  have hy : 0 < f (1 - x) := expNegInvGlue.pos_of_pos (sub_pos.2 h₁)
  have hd₁ := expNegInvGlue.hasDerivAt x
  have hd₂ : HasDerivAt (fun y ↦ f (1 - y)) ((1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) x :=
    (expNegInvGlue.hasDerivAt (1 - x)).comp x ((hasDerivAt_id x).const_sub 1)
  have hd := hd₁.div (hd₁.add hd₂) (pos_denom x).ne'
  -- `smoothTransition` is, by definition, the quotient that `hd` differentiates.
  rw [show smoothTransition = f / (f + fun y ↦ f (1 - y)) from rfl, hd.deriv, Pi.add_apply]
  refine div_pos ?_ (pow_pos (pos_denom x) 2)
  have key : x⁻¹ ^ 2 * f x * (f x + f (1 - x)) -
      f x * (x⁻¹ ^ 2 * f x + (1 - x)⁻¹ ^ 2 * f (1 - x) * (-1)) =
      x⁻¹ ^ 2 * f x * f (1 - x) + f x * ((1 - x)⁻¹ ^ 2 * f (1 - x)) := by ring
  rw [key]
  positivity

end Real.smoothTransition

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

end TauCeti

namespace SymplecticGeometry

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
  obtain ⟨ε₀, hε₀, h₀⟩ := Metric.isOpen_iff.mp hU a (hIU ⟨le_rfl, hab⟩)
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.mp hU b (hIU ⟨hab, le_rfl⟩)
  obtain ⟨c, hc, hcI, hcU, -⟩ := exists_contDiff_eqOn_id_Icc_mem_Ioo hab (lt_min hε₀ hε₁)
  refine ⟨c, hc, hcI, fun t ↦ ?_⟩
  -- The value `c t` lies in `[a, b]` or within `min ε₀ ε₁` of one of its ends.
  obtain ⟨ht₀, ht₁⟩ := hcU t
  have := min_le_left ε₀ ε₁
  have := min_le_right ε₀ ε₁
  rcases lt_or_ge (c t) a with ha | ha
  · exact h₀ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  rcases le_or_gt (c t) b with hb | hb
  · exact hIU ⟨ha, hb⟩
  · exact h₁ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)

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

end SymplecticGeometry

end
