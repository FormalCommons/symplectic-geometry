/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Taylor
import SymplecticGeometry.Analysis.Asymptotics.SumPowSmul
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# Derivatives of a map that vanishes to a given order

If a map `g` between real normed spaces is `C^n` at `a` and `g z = o(‖z - a‖ ^ j)` as `z → a`,
with `j ≤ n`, then its iterated derivative of order `j` vanishes at `a`. In particular, if
`g z = O(‖z - a‖ ^ m)`, then its iterated derivatives of every order `j ≤ n` with `j < m` vanish
at `a`.

The proof restricts `g` to the lines `t ↦ g (a + t • v)`. On a line, Taylor's formula of order
`j` (Mathlib's `taylor_isLittleO`) makes the Taylor polynomial `o((x - x₀) ^ j)`, and then its
coefficients vanish (`SymplecticGeometry.eq_zero_of_isLittleO_sum_pow_smul`), so that `D^j g(a)`
vanishes on every constant tuple `(v, …, v)`. Since `D^j g(a)` is symmetric (Tau Ceti's
`ContDiffAt.iteratedFDeriv_comp_perm_of_le`), polarization (Tau Ceti's
`MultilinearMap.eq_zero_of_apply_const_eq_zero`) shows that it is zero.
The one-variable step follows the proof of Tau Ceti's `TauCeti.isBigO_sub_pow_smul_iteratedDeriv`.

## Main results

* `ContDiffAt.iteratedDeriv_eq_zero_of_isLittleO_pow`: the one-variable statement.
* `ContDiffAt.iteratedFDeriv_eq_zero_of_isLittleO_pow`: the statement in normed spaces.
* `ContDiffAt.iteratedFDeriv_eq_zero_of_isBigO_pow`: its form with a big-O hypothesis of an
  order `m > j`.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  proof of Proposition 5.55, where this vanishing step is used.
-/

public section

open Asymptotics Filter Finset
open scoped Topology Nat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `f : ℝ → F` is `C^n` at `x₀` and `f x = o((x - x₀) ^ j)` as `x → x₀`, with `j ≤ n`, then
the `j`-th derivative of `f` vanishes at `x₀`. -/
theorem ContDiffAt.iteratedDeriv_eq_zero_of_isLittleO_pow {f : ℝ → F} {x₀ : ℝ}
    {n : WithTop ℕ∞} {j : ℕ} (hf : ContDiffAt ℝ n f x₀)
    (hfo : f =o[𝓝 x₀] fun x ↦ (x - x₀) ^ j) (hj : j ≤ n) :
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
    refine (hfo.sub hT).congr_left fun x ↦ ?_
    rw [sub_sub_cancel, taylor_within_apply]
    simp [c, smul_smul, mul_comm]
  -- Along `x = x₀ + h`, the coefficients of this polynomial vanish.
  have htend : Tendsto (fun h : ℝ ↦ x₀ + h) (𝓝[≠] 0) (𝓝 x₀) :=
    (Continuous.tendsto' (by fun_prop) 0 x₀ (add_zero x₀)).mono_left nhdsWithin_le_nhds
  have hcj : c j = 0 := SymplecticGeometry.eq_zero_of_isLittleO_sum_pow_smul
    ((hpoly.comp_tendsto htend).congr (fun h ↦ by simp) fun h ↦ by simp) j le_rfl
  simp only [c, smul_eq_zero, inv_eq_zero, Nat.cast_eq_zero, j.factorial_ne_zero, false_or] at hcj
  rwa [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hε)] at hcj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `g : E → F` is `C^n` at `a` and `g z = o(‖z - a‖ ^ j)` as `z → a`, with `j ≤ n`, then the
iterated derivative `D^j g(a)` vanishes. -/
theorem ContDiffAt.iteratedFDeriv_eq_zero_of_isLittleO_pow {g : E → F} {a : E}
    {n : WithTop ℕ∞} {j : ℕ} (hg : ContDiffAt ℝ n g a)
    (hgo : g =o[𝓝 a] fun z ↦ ‖z - a‖ ^ j) (hj : j ≤ n) :
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
  have hfo : (fun t : ℝ ↦ g (a + t • v)) =o[𝓝 0] fun t ↦ (t - 0) ^ j := by
    refine (hgo.comp_tendsto hline).trans_isBigO (IsBigO.of_bound (‖v‖ ^ j) ?_)
    filter_upwards with t
    simp [norm_smul, mul_pow, mul_comm]
  have h := hf.iteratedDeriv_eq_zero_of_isLittleO_pow hfo hj
  have hg' : ContDiffAt ℝ j g (a + (0 : ℝ) • v) := by
    rw [ha]
    exact hg.of_le hj
  rwa [hg'.iteratedDeriv_comp_add_smul, ha] at h

/-- If `g : E → F` is `C^n` at `a` and `g z = O(‖z - a‖ ^ m)` as `z → a`, then the iterated
derivative `D^j g(a)` vanishes for every `j ≤ n` with `j < m`. -/
theorem ContDiffAt.iteratedFDeriv_eq_zero_of_isBigO_pow {g : E → F} {a : E}
    {n : WithTop ℕ∞} {j m : ℕ} (hg : ContDiffAt ℝ n g a)
    (hO : g =O[𝓝 a] fun z ↦ ‖z - a‖ ^ m) (hj : j ≤ n) (hjm : j < m) :
    iteratedFDeriv ℝ j g a = 0 :=
  hg.iteratedFDeriv_eq_zero_of_isLittleO_pow
    (hO.trans_isLittleO <| (isLittleO_pow_pow hjm).comp_tendsto (tendsto_norm_sub_self a)) hj
