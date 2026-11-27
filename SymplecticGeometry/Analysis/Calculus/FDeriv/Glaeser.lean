/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# Glaeser's inequality

A nonnegative function `f` that is `C²` near a compact set `K` of a finite-dimensional real
normed space has a derivative of size at most a constant times `√(f x)` near `K`:
`IsCompact.exists_eventually_norm_fderiv_le_mul_sqrt`.

The proof is the classical one. At a point `x`, the second-order Taylor estimate
`|f (x + a) - f x - Df x a| ≤ L ‖a‖²`, uniform over a compact neighbourhood of `K`, together
with `0 ≤ f (x + a)` gives `‖Df x‖ ≤ f x / t + L t` for every small `t > 0`
(`ContinuousLinearMap.norm_le_div_add_mul_of_forall_norm_le`, which holds in any real normed
space); one takes `t` proportional to `√(f x)`. The uniform Taylor estimate is Tau Ceti's
`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`.

The bound is a step towards the interpolation of strictly plurisubharmonic functions along a
totally real submanifold (Proposition 3.26 of Cieliebak–Eliashberg).

## References

* G. Glaeser, *Racine carrée d'une fonction différentiable*, Ann. Inst. Fourier 13 (1963),
  no. 2, 203–210.
* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Filter Topology Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Glaeser's inequality at a point.** Let `φ` be a continuous linear form on a real normed
space, `x` a point, and `t > 0`, `L ≥ 0`. If `0 ≤ f (x + a)` and
`|f (x + a) - f x - φ a| ≤ L ‖a‖²` for every `a` with `‖a‖ ≤ t`, then
`‖φ‖ ≤ f x / t + L t`. -/
theorem ContinuousLinearMap.norm_le_div_add_mul_of_forall_norm_le {f : E → ℝ} {x : E}
    {φ : E →L[ℝ] ℝ} {t L : ℝ} (ht : 0 < t) (hL : 0 ≤ L)
    (hf₀ : ∀ a : E, ‖a‖ ≤ t → 0 ≤ f (x + a))
    (hf : ∀ a : E, ‖a‖ ≤ t → |f (x + a) - f x - φ a| ≤ L * ‖a‖ ^ 2) :
    ‖φ‖ ≤ f x / t + L * t := by
  have hfx : 0 ≤ f x := by simpa using hf₀ 0 (by simpa using ht.le)
  -- One side of the bound for every `w`, then the other by `-w`.
  have key (w : E) (hw : w ≠ 0) : -φ w ≤ (f x / t + L * t) * ‖w‖ := by
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have h0 := hf₀ ((t / ‖w‖) • w) (by simp [norm_smul, abs_of_pos ht, hw'.ne'])
    have h1 := hf ((t / ‖w‖) • w) (by simp [norm_smul, abs_of_pos ht, hw'.ne'])
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ht hw'),
      div_mul_cancel₀ _ hw'.ne'] at h1
    have h2 : -(t / ‖w‖ * φ w) ≤ f x + L * t ^ 2 := by linarith [(abs_le.mp h1).2]
    calc -φ w = ‖w‖ / t * -(t / ‖w‖ * φ w) := by field_simp
      _ ≤ ‖w‖ / t * (f x + L * t ^ 2) := by gcongr
      _ = (f x / t + L * t) * ‖w‖ := by field_simp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨by linarith [key w hw], ?_⟩
  simpa using key (-w) (neg_ne_zero.mpr hw)

/-- **Glaeser's inequality.** Let `f` be a real function on a finite-dimensional real normed
space that is `C²` at every point of a compact set `K` and nonnegative near `K`. Then near `K`
the norm of the derivative of `f` is at most a constant times `√(f x)`. -/
theorem IsCompact.exists_eventually_norm_fderiv_le_mul_sqrt [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsCompact K) {f : E → ℝ} (hf : ∀ x ∈ K, ContDiffAt ℝ 2 f x)
    (hf₀ : ∀ᶠ x in 𝓝ˢ K, 0 ≤ f x) :
    ∃ A, ∀ᶠ x in 𝓝ˢ K, ‖fderiv ℝ f x‖ ≤ A * √(f x) := by
  -- An open set `U ⊇ K` on which `f` is `C²` and nonnegative.
  have hS : {x | ContDiffAt ℝ 2 f x} ∩ {x | 0 ≤ f x} ∈ 𝓝ˢ K :=
    inter_mem (mem_nhdsSet_iff_forall.mpr fun x hx => (hf x hx).eventually (by simp)) hf₀
  obtain ⟨U, hUo, hKU, hUS'⟩ := mem_nhdsSet_iff_exists.mp hS
  have hUS (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 f y ∧ 0 ≤ f y := hUS' hy
  -- A compact neighbourhood `K'` of `K` in `U`, and a uniform margin `ε` around it.
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hUo hKU
  obtain ⟨ε, hε, hεU⟩ := hK'.exists_cthickening_subset_open hUo hK'U
  -- The uniform second-order Taylor estimate on `K'`.
  obtain ⟨δ, hδ, L, hL⟩ := IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul
    (F := fun _ : E => f) (x := id) hK'
    (fun p hp => ((hUS _ (hK'U hp)).1).comp _ contDiffAt_snd) continuousOn_id
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn
    (f := f) fun x hx => (ContDiffAt.continuousAt (hUS _ (hK'U hx)).1).continuousWithinAt
  set M := max C 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set s := min δ ε / √M
  have hs : 0 < s := div_pos (lt_min hδ hε) (Real.sqrt_pos.mpr hM)
  refine ⟨1 / s + max L 0 * s, Filter.mem_of_superset
    (isOpen_interior.mem_nhdsSet.mpr hKK') fun x hx => ?_⟩
  have hxK' : x ∈ K' := interior_subset hx
  have hxU : x ∈ U := hK'U hxK'
  rcases (hUS _ hxU).2.eq_or_lt with hfx | hfx
  · -- At a zero of `f`, `x` is a local minimum, so the derivative vanishes.
    have hmin : IsLocalMin f x :=
      Filter.mem_of_superset (hUo.mem_nhds hxU) fun y hy => by
        simpa [← hfx] using (hUS _ hy).2
    simp [hmin.fderiv_eq_zero, ← hfx]
  set t := s * √(f x)
  have hsq : 0 < √(f x) := Real.sqrt_pos.mpr hfx
  have ht : 0 < t := mul_pos hs hsq
  have htle : t ≤ min δ ε := by
    have h1 : √(f x) ≤ √M :=
      Real.sqrt_le_sqrt ((le_abs_self _).trans ((hC x hxK').trans (le_max_left _ _)))
    calc t ≤ s * √M := mul_le_mul_of_nonneg_left h1 hs.le
      _ = min δ ε := div_mul_cancel₀ _ (Real.sqrt_pos.mpr hM).ne'
  have key := ContinuousLinearMap.norm_le_div_add_mul_of_forall_norm_le (f := f) (x := x)
    (φ := fderiv ℝ f x) ht (le_max_right L 0)
    (fun a ha => (hUS _ (hεU (mem_cthickening_of_dist_le _ x ε K' hxK'
      (by simpa [dist_eq_norm] using ha.trans (htle.trans (min_le_right _ _)))))).2)
    fun a ha => by
      have := hL x hxK' a 0 (ha.trans (htle.trans (min_le_left _ _))) (by simpa using hδ.le)
      calc |f (x + a) - f x - fderiv ℝ f x a| ≤ L * ‖a‖ * ‖a‖ := by simpa using this
        _ ≤ max L 0 * ‖a‖ ^ 2 := by rw [mul_assoc, ← sq]; gcongr; exact le_max_left _ _
  calc ‖fderiv ℝ f x‖ ≤ f x / t + max L 0 * t := key
    _ = (1 / s + max L 0 * s) * √(f x) := by
      have : f x = √(f x) * √(f x) := (Real.mul_self_sqrt hfx.le).symm
      simp only [t]
      rw [this, Real.sqrt_mul_self (Real.sqrt_nonneg _)]
      field_simp
