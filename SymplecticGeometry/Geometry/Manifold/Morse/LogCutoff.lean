/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Module
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Comp
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.Interpolation

/-!
# A logarithmic cut-off keeps a field gradient-like

Let `E` be a finite-dimensional real normed space, `X : E → E` a field and `f H : E → ℝ`
differentiable on a ball `B` around `0`, such that on `B` the field `X` satisfies the
gradient-like inequality `c (‖X‖² + ‖Df‖²) ≤ Df(X)` for both `f` and `f + H`, and
`|H z| ≤ A ‖z‖ ‖Df(z)‖`. This file shows that for every `r > 0` there is a smooth cut-off
`β : E → [0, 1]`, equal to `1` near `0` and supported in the ball of radius `r`, such that `X`
satisfies the gradient-like inequality on `B`, with constant `c / 2`, for every function
`f + t β H` with `t ∈ [0, 1]`. The constant does not depend on `r`.

The cut-off is `β = 1 - ψ ∘ ρ`, with `ρ z = ‖toEuclidean z‖²` and `ψ` Tau Ceti's logarithmic
profile `TauCeti.logCutoffProfile ε δ`, with `δ` of order `r²` and `Λ = log (δ / ε)` large. The
differential of `f + t β H` is `(1 - tβ) Df + tβ D(f + H) + t H Dβ`. The first two terms satisfy
the gradient-like inequality with the constant `c`, by convexity
(`TauCeti.mul_le_one_sub_smul_add_smul_add_apply`). The last term has norm at most
`A ‖z‖ ‖Dβ(z)‖ ‖Df(z)‖`, and `‖z‖ ‖Dβ(z)‖` is of order `1 / Λ` by
`TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`; since `c ‖Df‖ ≤ ‖X‖`, it costs only half
of the constant once `Λ` is large. A cut-off with `‖Dβ‖` of order `1 / r` would not do, since
`A` need not be small: this is why the cut-off is logarithmic.

This is the estimate that lets one cut off `t H` near a critical point in the proof of
Proposition 9.23 of [CieliebakEliashberg2012], as in their Lemma 12.9, where `|H| ≤ A ‖z‖ ‖Df‖`
comes from the radial estimates of `Morse/RadialEstimate.lean`.

## Main results

* `TauCeti.mul_le_one_sub_smul_add_smul_add_apply`: at one point, a convex combination of two
  differentials satisfying the gradient-like inequality, perturbed by a small error, satisfies it
  with half the constant.
* `TauCeti.exists_logCutoff_mul_le_fderiv_add_smul_mul_apply`: the cut-off `β` above.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set Metric Filter Topology
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The gradient-like inequality for a perturbed convex combination.** Let `a b : E →L[ℝ] ℝ`
satisfy `c (‖v‖² + ‖a‖²) ≤ a v` and `c (‖v‖² + ‖b‖²) ≤ b v` with `c > 0`, let `s ∈ [0, 1]`,
and let `e` be an error with `‖e‖ ≤ η ‖a‖`, where `η ≥ 0` and `2 (η + η²) ≤ c²`. Then
`ℓ = (1 - s) • a + s • b + e` satisfies `c / 2 * (‖v‖² + ‖ℓ‖²) ≤ ℓ v`. -/
theorem mul_le_one_sub_smul_add_smul_add_apply {a b e : E →L[ℝ] ℝ} {v : E} {c s η : ℝ}
    (hc : 0 < c) (hs : s ∈ Icc (0 : ℝ) 1) (ha : c * (‖v‖ ^ 2 + ‖a‖ ^ 2) ≤ a v)
    (hb : c * (‖v‖ ^ 2 + ‖b‖ ^ 2) ≤ b v) (hη0 : 0 ≤ η) (hη : 2 * (η + η ^ 2) ≤ c ^ 2)
    (he : ‖e‖ ≤ η * ‖a‖) :
    c / 2 * (‖v‖ ^ 2 + ‖(1 - s) • a + s • b + e‖ ^ 2) ≤ ((1 - s) • a + s • b + e) v := by
  obtain ⟨hs0, hs1⟩ := hs
  set ℓ := (1 - s) • a + s • b
  -- `c ‖a‖ ≤ ‖v‖`, from the inequality for `a` and `a v ≤ ‖a‖ ‖v‖`.
  have hav : c * ‖a‖ ≤ ‖v‖ := by
    have h1 : a v ≤ ‖a‖ * ‖v‖ := (le_abs_self _).trans (a.le_opNorm v)
    rcases (norm_nonneg a).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact norm_nonneg v
    · refine le_of_mul_le_mul_right ?_ h0
      nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖a‖]
  -- The convex combination satisfies the inequality with the constant `c`.
  have hℓn : ‖ℓ‖ ≤ (1 - s) * ‖a‖ + s * ‖b‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hs0]
  have hℓ : c * (‖v‖ ^ 2 + ‖ℓ‖ ^ 2) ≤ ℓ v := by
    have hℓv : ℓ v = (1 - s) * a v + s * b v := by simp [ℓ]
    have hsq : ‖ℓ‖ ^ 2 ≤ (1 - s) * ‖a‖ ^ 2 + s * ‖b‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg ℓ) hℓn 2, mul_nonneg (mul_nonneg hs0
        (sub_nonneg.2 hs1)) (sq_nonneg (‖a‖ - ‖b‖))]
    rw [hℓv]
    nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 hs1), mul_le_mul_of_nonneg_left hb hs0]
  -- The error costs at most half of the constant.
  have hev : -(‖e‖ * ‖v‖) ≤ e v := by
    have := e.le_opNorm v
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (e v)]
  have hce : c * ‖e‖ ≤ η * ‖v‖ := by
    calc c * ‖e‖ ≤ c * (η * ‖a‖) := by gcongr
      _ = η * (c * ‖a‖) := by ring
      _ ≤ η * ‖v‖ := by gcongr
  have hn : ‖ℓ + e‖ ^ 2 ≤ 2 * ‖ℓ‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    nlinarith [norm_add_le ℓ e, norm_nonneg (ℓ + e), sq_nonneg (‖ℓ‖ - ‖e‖)]
  have hce2 : (c * ‖e‖) ^ 2 ≤ (η * ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hce 2
  have hkey : c * (c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖) ≤ c * (c / 2 * ‖v‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hce (norm_nonneg v), sq_nonneg ‖v‖]
  have hkey' : c * ‖e‖ ^ 2 + ‖e‖ * ‖v‖ ≤ c / 2 * ‖v‖ ^ 2 := le_of_mul_le_mul_left hkey hc
  rw [add_apply]
  nlinarith

variable [FiniteDimensional ℝ E]

/-- **A logarithmic cut-off keeps a field gradient-like.** Let `E` be a finite-dimensional real
normed space, `X : E → E`, and `f H : E → ℝ` differentiable on `ball 0 r₀`, such that for every
`z` in that ball and some `c > 0` and `A`,
* `c (‖X z‖² + ‖Df(z)‖²) ≤ Df(z) (X z)`,
* `c (‖X z‖² + ‖D(f + H)(z)‖²) ≤ D(f + H)(z) (X z)`,
* `|H z| ≤ A ‖z‖ ‖Df(z)‖`.

Then for every `r > 0` there is a smooth `β : E → ℝ` with values in `[0, 1]`, equal to `1` near
`0`, with topological support in `ball 0 r`, such that for every `t ∈ [0, 1]` and `z` in
`ball 0 r₀`, with `F = f + t • (β * H)`,
`c / 2 * (‖X z‖² + ‖DF(z)‖²) ≤ DF(z) (X z)`. -/
theorem exists_logCutoff_mul_le_fderiv_add_smul_mul_apply {f H : E → ℝ} {X : E → E}
    {r₀ c A : ℝ} (hc : 0 < c) (hf : DifferentiableOn ℝ f (ball 0 r₀))
    (hH : DifferentiableOn ℝ H (ball 0 r₀))
    (h₁ : ∀ z ∈ ball (0 : E) r₀, c * (‖X z‖ ^ 2 + ‖fderiv ℝ f z‖ ^ 2) ≤ fderiv ℝ f z (X z))
    (h₂ : ∀ z ∈ ball (0 : E) r₀,
      c * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + H) z‖ ^ 2) ≤ fderiv ℝ (f + H) z (X z))
    (h₃ : ∀ z ∈ ball (0 : E) r₀, |H z| ≤ A * ‖z‖ * ‖fderiv ℝ f z‖) {r : ℝ} (hr : 0 < r) :
    ∃ β : E → ℝ, ContDiff ℝ ∞ β ∧ (∀ z, β z ∈ Icc (0 : ℝ) 1) ∧ (∀ᶠ z in 𝓝 0, β z = 1) ∧
      tsupport β ⊆ ball 0 r ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) r₀,
        c / 2 * (‖X z‖ ^ 2 + ‖fderiv ℝ (f + t • (β * H)) z‖ ^ 2) ≤
          fderiv ℝ (f + t • (β * H)) z (X z) := by
  -- The squared Euclidean norm `ρ` and its comparison with the norm of `E`.
  set T := toEuclidean (E := E)
  set ρ : E → ℝ := fun z ↦ ‖T z‖ ^ 2
  set a₁ := ‖(T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)‖
  set a₂ := ‖(T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖
  have hz (z : E) : ‖z‖ ≤ a₁ * ‖T z‖ := by
    simpa using (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E).le_opNorm (T z)
  have hsqrt (z : E) : √(ρ z) = ‖T z‖ := Real.sqrt_sq (norm_nonneg _)
  have hρd (z : E) : HasFDerivAt ρ (2 • (innerSL ℝ (T z)).comp
      (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) z :=
    (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).hasFDerivAt.norm_sq
  have hρD (z : E) : ‖fderiv ℝ ρ z‖ ≤ (2 * a₂) * √(ρ z) := by
    rw [(hρd z).fderiv, hsqrt]
    refine (norm_nsmul_le).trans ?_
    push_cast
    calc 2 * ‖(innerSL ℝ (T z)).comp
          (T : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖
        ≤ 2 * (‖innerSL ℝ (T z)‖ * a₂) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = 2 * a₂ * ‖T z‖ := by rw [innerSL_apply_norm]; ring
  have hρc : ContDiff ℝ ∞ ρ := (contDiff_norm_sq ℝ).comp T.contDiff
  -- The parameters of the cut-off.
  set κ := a₁ * (logCutoffConst * (2 * a₂))
  have hκ : 0 ≤ κ := by have := logCutoffConst_pos; positivity
  set A' := max A 0
  set L := 3 + A' * κ * (4 / c ^ 2 + 1)
  have hAκ : 0 ≤ A' * κ * (4 / c ^ 2 + 1) := by positivity
  set δ := (r / (a₁ + 1)) ^ 2
  have hδ : 0 < δ := by positivity
  set ε := δ / Real.exp L
  have hε : 0 < ε := by positivity
  have hΛ : Real.log (δ / ε) = L := by
    rw [show δ / ε = Real.exp L by simp only [ε]; field_simp, Real.log_exp]
  have h4 : 4 * ε ≤ δ := by
    have : 4 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    simp only [ε]
    rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos L)]
    nlinarith
  have h2 : 2 * ε ≤ δ := by linarith
  set β : E → ℝ := fun z ↦ 1 - logCutoffProfile ε δ (ρ z)
  have hβc : ContDiff ℝ ∞ β :=
    contDiff_const.sub ((contDiff_logCutoffProfile hδ.ne').comp hρc)
  -- `‖z‖ ‖Dβ(z)‖ ≤ κ / L`.
  have hβD (z : E) : ‖z‖ * ‖fderiv ℝ β z‖ ≤ κ / L := by
    have h := sqrt_mul_norm_fderiv_logCutoffProfile_comp_le hε h4 (hρd z).differentiableAt
      (by positivity) (hρD z)
    rw [hΛ] at h
    have hD : fderiv ℝ β z = -fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z := fderiv_const_sub _
    rw [hD, norm_neg]
    calc ‖z‖ * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖
        ≤ a₁ * ‖T z‖ * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖ := by gcongr; exact hz z
      _ = a₁ * (√(ρ z) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) z‖) := by rw [hsqrt]; ring
      _ ≤ a₁ * (logCutoffConst * (2 * a₂) / L) := by gcongr
      _ = κ / L := by simp only [κ]; ring
  refine ⟨β, hβc, fun z ↦ ?_, ?_, ?_, fun t ht z hz₀ ↦ ?_⟩
  · simpa [β] using mul_one_sub_logCutoffProfile_comp_mem_Icc (χ := 1) (ρ := ρ) (p := z) hε h2
      zero_le_one le_rfl
  · have : ∀ᶠ z in 𝓝 (0 : E), ρ z < ε := by
      refine hρc.continuous.continuousAt.eventually_lt continuousAt_const ?_
      simpa [ρ] using hε
    filter_upwards [this] with z hz
    simp [β, logCutoffProfile_eq_zero_of_le h2 hz.le]
  · -- The support lies where `ρ ≤ δ`, that is, in the Euclidean ball of radius `r / (a₁ + 1)`.
    have hsub : tsupport β ⊆ {z | ρ z ≤ δ} := by
      refine closure_minimal (fun z hz ↦ ?_) (isClosed_le hρc.continuous continuous_const)
      by_contra h
      exact hz (by simp [β, logCutoffProfile_eq_one_of_ge hε h2 (not_le.1 h).le])
    intro z hzs
    have hρz := hsub hzs
    have hTz : ‖T z‖ ≤ r / (a₁ + 1) := by
      rw [← hsqrt, ← Real.sqrt_sq (by positivity : 0 ≤ r / (a₁ + 1))]
      exact Real.sqrt_le_sqrt hρz
    rw [mem_ball_zero_iff]
    calc ‖z‖ ≤ a₁ * ‖T z‖ := hz z
      _ ≤ a₁ * (r / (a₁ + 1)) := by gcongr
      _ < r := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  · -- The differential of `f + t • (β * H)` at `z`.
    have hfz := (hf z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
    have hHz := (hH z hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀)
    have hβz : DifferentiableAt ℝ β z := hβc.differentiable (by simp) z
    have hDF : fderiv ℝ (f + t • (β * H)) z =
        (1 - t * β z) • fderiv ℝ f z + (t * β z) • fderiv ℝ (f + H) z +
          (t * H z) • fderiv ℝ β z := by
      rw [fderiv_add hfz ((hβz.mul hHz).const_smul t), fderiv_const_smul (hβz.mul hHz),
        fderiv_mul hβz hHz, fderiv_add hfz hHz]
      module
    have hβI : β z ∈ Icc (0 : ℝ) 1 := by
      simpa [β] using mul_one_sub_logCutoffProfile_comp_mem_Icc (χ := 1) (ρ := ρ) (p := z) hε h2
        zero_le_one le_rfl
    have hs : t * β z ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg ht.1 hβI.1, by nlinarith [ht.1, ht.2, hβI.1, hβI.2]⟩
    set η := A' * κ / L
    have hLpos : 0 < L := by linarith [hAκ]
    have hη0 : 0 ≤ η := by positivity
    have hηle : η * (4 / c ^ 2 + 1) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hLpos]
      linarith
    have hη : 2 * (η + η ^ 2) ≤ c ^ 2 := by
      have hc2 : 0 < c ^ 2 := by positivity
      have hη1 : η ≤ 1 := by nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc2.le]
      have hηc : 4 * η ≤ c ^ 2 := by
        have : η * (4 / c ^ 2) ≤ 1 := by nlinarith
        rw [mul_div_assoc', div_le_one hc2] at this
        linarith
      nlinarith
    rw [hDF]
    refine mul_le_one_sub_smul_add_smul_add_apply hc hs (h₁ z hz₀) (h₂ z hz₀) hη0 hη ?_
    -- The error term `t H Dβ`.
    have hA' : |H z| ≤ A' * ‖z‖ * ‖fderiv ℝ f z‖ :=
      (h₃ z hz₀).trans (by gcongr; exact le_max_left _ _)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
    calc t * |H z| * ‖fderiv ℝ β z‖ ≤ 1 * (A' * ‖z‖ * ‖fderiv ℝ f z‖) * ‖fderiv ℝ β z‖ := by
          gcongr; exact ht.2
      _ = A' * (‖z‖ * ‖fderiv ℝ β z‖) * ‖fderiv ℝ f z‖ := by ring
      _ ≤ A' * (κ / L) * ‖fderiv ℝ f z‖ := by gcongr; exact hβD z
      _ = η * ‖fderiv ℝ f z‖ := by simp only [η]; ring

end TauCeti

end
