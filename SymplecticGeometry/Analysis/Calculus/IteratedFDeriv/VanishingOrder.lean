/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Taylor
import TauCeti.Analysis.Asymptotics.TruncatedPowerSeries
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# Derivatives of a map that vanishes to a given order

If a map `g` between real normed spaces is `C^n` at `a` and `g z = O(‖z - a‖ ^ m)` as `z → a`,
then its iterated derivatives of every order `j ≤ n` with `j < m` vanish at `a`.

The proof restricts `g` to the lines `t ↦ g (a + t • v)`. On a line, Taylor's formula of order
`j` (Mathlib's `taylor_isLittleO`) and the uniqueness of finite power expansions (Tau Ceti's
`TauCeti.eq_zero_of_isBigO_sum_pow_smul`) show that the `j`-th derivative vanishes, so that
`D^j g(a)` vanishes on every constant tuple `(v, …, v)`. Since `D^j g(a)` is symmetric (Tau
Ceti's `ContDiffAt.iteratedFDeriv_comp_perm_of_le`), polarization (Tau Ceti's
`MultilinearMap.eq_zero_of_apply_const_eq_zero`) shows that it is zero.
The one-variable step follows the proof of Tau Ceti's `TauCeti.isBigO_sub_pow_smul_iteratedDeriv`.

## Main results

* `ContDiffAt.iteratedDeriv_eq_zero_of_isBigO_pow`: the one-variable statement.
* `ContDiffAt.iteratedFDeriv_eq_zero_of_isBigO_pow`: the statement in normed spaces.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  proof of Proposition 5.55, where this vanishing step is used.
-/

public section

open Asymptotics Filter Finset
open scoped Topology Nat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `f : ℝ → F` is `C^n` at `x₀` and `f x = O((x - x₀) ^ m)` as `x → x₀`, then the `j`-th
derivative of `f` vanishes at `x₀` for every `j ≤ n` with `j < m`. -/
theorem ContDiffAt.iteratedDeriv_eq_zero_of_isBigO_pow {f : ℝ → F} {x₀ : ℝ}
    {n : WithTop ℕ∞} {j m : ℕ} (hf : ContDiffAt ℝ n f x₀)
    (hO : f =O[𝓝 x₀] fun x ↦ (x - x₀) ^ m) (hj : j ≤ n) (hjm : j < m) :
    iteratedDeriv j f x₀ = 0 := by
  obtain ⟨u, hu, hfu⟩ := (hf.of_le hj).contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  -- Taylor's formula of order `j` on the ball.
  have hT := taylor_isLittleO (convex_ball x₀ ε) (Metric.mem_ball_self hε) (hfu.mono hεu)
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds x₀ hε)] at hT
  set c : ℕ → F := fun i ↦ (i ! : ℝ)⁻¹ • iteratedDerivWithin i f (Metric.ball x₀ ε) x₀
  -- The Taylor polynomial is `o((x - x₀) ^ j)`, since `f` is.
  have hpoly : (fun x ↦ ∑ i ∈ range (j + 1), (x - x₀) ^ i • c i) =o[𝓝 x₀]
      fun x ↦ (x - x₀) ^ j := by
    have hfo : f =o[𝓝 x₀] fun x ↦ (x - x₀) ^ j := by
      refine hO.trans_isLittleO ?_
      exact (isLittleO_pow_pow hjm).comp_tendsto (tendsto_sub_nhds_zero_iff.2 tendsto_id)
    refine (hfo.sub hT).congr_left fun x ↦ ?_
    rw [sub_sub_cancel, taylor_within_apply]
    simp [c, smul_smul, mul_comm]
  -- Along `x = x₀ + h`, the coefficients of a polynomial of degree `j` that is `o(h ^ j)`
  -- vanish: those of order `< j` by the uniqueness of finite power expansions, and then the
  -- last one.
  have htend : Tendsto (fun h : ℝ ↦ x₀ + h) (𝓝[≠] 0) (𝓝 x₀) :=
    (Continuous.tendsto' (by fun_prop) 0 x₀ (add_zero x₀)).mono_left nhdsWithin_le_nhds
  have hp : (fun h : ℝ ↦ ∑ i ∈ range (j + 1), h ^ i • c i) =o[𝓝[≠] 0] fun h ↦ h ^ j :=
    (hpoly.comp_tendsto htend).congr (fun h ↦ by simp) fun h ↦ by simp
  have hsmul : (fun h : ℝ ↦ h ^ j • c j) =O[𝓝[≠] 0] fun h ↦ h ^ j :=
    IsBigO.of_bound ‖c j‖ (by filter_upwards with h; simp [norm_smul, mul_comm])
  have hlow : ∀ i < j, c i = 0 := TauCeti.eq_zero_of_isBigO_sum_pow_smul
    ((hp.isBigO.sub hsmul).congr_left fun h ↦ by simp [sum_range_succ])
  have htop : (fun h : ℝ ↦ h ^ j • c j) =o[𝓝[≠] 0] fun h ↦ h ^ j := by
    refine hp.congr_left fun h ↦ ?_
    rw [sum_range_succ, sum_eq_zero fun i hi ↦ by simp [hlow i (mem_range.1 hi)], zero_add]
  have hconst : (fun _ : ℝ ↦ c j) =o[𝓝[≠] 0] fun _ ↦ (1 : ℝ) := by
    refine ((isBigO_refl (fun h : ℝ ↦ (h ^ j)⁻¹) _).smul_isLittleO htop).congr' ?_ ?_ <;>
      filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
    · rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero j hh), one_smul]
    · rw [smul_eq_mul, inv_mul_cancel₀ (pow_ne_zero j hh)]
  have hcj : c j = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ((isLittleO_one_iff ℝ).1 hconst)
  simp only [c, smul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, j.factorial_ne_zero, false_or] at hcj
  rwa [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε)] at hcj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `g : E → F` is `C^n` at `a` and `g z = O(‖z - a‖ ^ m)` as `z → a`, then the iterated
derivative `D^j g(a)` vanishes for every `j ≤ n` with `j < m`. -/
theorem ContDiffAt.iteratedFDeriv_eq_zero_of_isBigO_pow {g : E → F} {a : E}
    {n : WithTop ℕ∞} {j m : ℕ} (hg : ContDiffAt ℝ n g a)
    (hO : g =O[𝓝 a] fun z ↦ ‖z - a‖ ^ m) (hj : j ≤ n) (hjm : j < m) :
    iteratedFDeriv ℝ j g a = 0 := by
  have : HasUniqueDiv F := .of_isTorsionFree ℝ F
  refine ContinuousMultilinearMap.toMultilinearMap_injective
    (MultilinearMap.eq_zero_of_apply_const_eq_zero
      (fun v σ ↦ hg.iteratedFDeriv_comp_perm_of_le (by simpa using hj) v σ) fun v ↦ ?_)
  have ha : a + (0 : ℝ) • v = a := by simp
  have hline : Tendsto (fun t : ℝ ↦ a + t • v) (𝓝 0) (𝓝 a) :=
    Continuous.tendsto' (by fun_prop) 0 a ha
  have hf : ContDiffAt ℝ n (fun t : ℝ ↦ g (a + t • v)) 0 :=
    (ha ▸ hg).comp (0 : ℝ) (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hfO : (fun t : ℝ ↦ g (a + t • v)) =O[𝓝 0] fun t ↦ (t - 0) ^ m := by
    refine (hO.comp_tendsto hline).trans (IsBigO.of_bound (‖v‖ ^ m) ?_)
    filter_upwards with t
    simp [norm_smul, mul_pow, mul_comm]
  have h := hf.iteratedDeriv_eq_zero_of_isBigO_pow hfO hj hjm
  have hg' : ContDiffAt ℝ j g (a + (0 : ℝ) • v) := by
    rw [ha]
    exact hg.of_le hj
  rwa [hg'.iteratedDeriv_comp_add_smul, ha] at h
