/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# The normal form of a function of one variable with a nonzero cubic term

Let `g : ℝ → ℝ` be of class `C^(n+3)` near `0`, with `n ≥ 1`, and let `0` be a zero of `g`
at which its first two derivatives vanish and its third does not. Then `g` is `φ ^ 3 / 3` for a
local `C^n` diffeomorphism `φ` of `ℝ` with `φ 0 = 0`.

Taylor's formula with the remainder as an averaged derivative
(`ContDiff.eq_sum_add_taylorRemainderFactor_apply`) writes `g y = y ^ 3 * k y` with `k` of
class `C^n` and `k 0 = g'''(0) / 6 ≠ 0`. With `σ = ±1` the sign of `k 0`, the function
`φ y = σ * (y * (3 * σ * k y) ^ (1 / 3))` has `φ ^ 3 / 3 = g` and derivative
`σ * (3 * σ * k 0) ^ (1 / 3) ≠ 0` at `0`, so the inverse function theorem
(`TauCeti.ContDiffOn.exists_openPartialHomeomorph`) makes it a local diffeomorphism.

The derivatives in the hypotheses are curried Fréchet derivatives evaluated at `1`, the form in
which Tau Ceti's `TauCeti.exists_normalized_splitting_chart_of_ker_eq_span_singleton` states
the conditions on the function of one variable that it splits off.

## Main results

* `ContDiff.exists_contDiff_eq_pow_three_mul`: a `C^(n+3)` function with a zero of order at
  least `3` at `0` is `y ^ 3 * k y` with `k` of class `C^n`.
* `ContDiffOn.exists_openPartialHomeomorph_eq_pow_three_div_three`: the normal form
  `g = φ ^ 3 / 3`.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS 39 (1970), 5–173.
-/

public section

open Filter Topology
open scoped ContDiff

/-- **Factoring out a cubic zero.** A `C^(n+3)` function `g : ℝ → ℝ` that vanishes at `0` together
with its first two derivatives is `y ^ 3 * k y` for a `C^n` function `k`, and `k 0` is the third
derivative of `g` at `0` divided by `6`. -/
theorem ContDiff.exists_contDiff_eq_pow_three_mul {n : ℕ∞} {g : ℝ → ℝ}
    (hg : ContDiff ℝ (n + 3 : ℕ∞) g) (h0 : g 0 = 0) (h1 : fderiv ℝ g 0 = 0)
    (h2 : fderiv ℝ (fderiv ℝ g) 0 1 = 0) :
    ∃ k : ℝ → ℝ, ContDiff ℝ n k ∧ (∀ y, g y = y ^ 3 * k y) ∧
      k 0 = fderiv ℝ (fderiv ℝ (fderiv ℝ g)) 0 1 1 1 / 6 := by
  have h2' : fderiv ℝ (fderiv ℝ g) 0 = 0 := by ext1; simpa using h2
  have hg2 : ContDiff ℝ ((2 : ℕ) + 1) g := hg.of_le (by simp; norm_num)
  -- The Taylor expansion of `g` of order `2` at `0` is its remainder term `y ^ 3 * k y`.
  set R := TauCeti.taylorRemainderFactor 2 g 0
  refine ⟨fun y ↦ R y (fun _ ↦ 1),
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 ↦ ℝ) ℝ fun _ ↦ 1).contDiff.comp
      (ContDiff.contDiff_taylorRemainderFactor (k := n) (n := 2) hg 0), fun y ↦ ?_, ?_⟩
  · have hR : R y (fun _ ↦ y) = y ^ 3 * R y (fun _ ↦ 1) := by
      simpa using R y |>.map_smul_univ (fun _ ↦ y) (fun _ ↦ (1 : ℝ))
    rw [ContDiff.eq_sum_add_taylorRemainderFactor_apply (n := 2) hg2 0 y, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, sub_zero, hR]
    simp [h0, h1, h2']
  · simp only [R, TauCeti.taylorRemainderFactor_self]
    rw [smul_apply, TauCeti.iteratedFDeriv_three_apply, smul_eq_mul, div_eq_inv_mul]
    exact congrArg (· * _) (by norm_num [Nat.factorial])

/-- **Normal form of a cubic critical point in one variable.** Let `g : ℝ → ℝ` be of class
`C^(n+3)` on a neighbourhood of `0`, with `n ≠ 0`, such that `g 0 = 0`, its first and second
derivatives vanish at `0`, and its third derivative at `0` does not. Then there is a local
diffeomorphism `φ` of `ℝ` of class `C^n`, whose source is a neighbourhood of `0` inside `s`,
with `φ 0 = 0` and `g = φ ^ 3 / 3` on its source. -/
theorem ContDiffOn.exists_openPartialHomeomorph_eq_pow_three_div_three {n : ℕ∞} {g : ℝ → ℝ}
    {s : Set ℝ} (hg : ContDiffOn ℝ (n + 3 : ℕ∞) g s) (hs : s ∈ 𝓝 0) (hn : n ≠ 0)
    (h0 : g 0 = 0) (h1 : fderiv ℝ g 0 = 0) (h2 : fderiv ℝ (fderiv ℝ g) 0 1 = 0)
    (h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ g)) 0 1 1 1 ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℝ ℝ, 0 ∈ φ.source ∧ φ.source ⊆ s ∧ φ 0 = 0 ∧
      ContDiffOn ℝ n φ φ.source ∧ ContDiffOn ℝ n φ.symm φ.target ∧
      ∀ y ∈ φ.source, g y = φ y ^ 3 / 3 := by
  -- A globally `C^(n+3)` function `g₁` equal to `g` near `0`, and its factorization.
  obtain ⟨g₁, hg₁, -, hg₁g⟩ := hg.exists_contDiff_eventuallyEq_of_finiteDimensional hs
  have hD1 := hg₁g.fderiv (𝕜 := ℝ)
  have hD2 := hD1.fderiv (𝕜 := ℝ)
  obtain ⟨k, hk, hgk, hk0⟩ := hg₁.exists_contDiff_eq_pow_three_mul
    (by rw [hg₁g.eq_of_nhds, h0]) (by rw [hD1.eq_of_nhds, h1]) (by rw [hD2.eq_of_nhds, h2])
  replace hk0 : k 0 ≠ 0 := by
    rw [hk0, hD2.fderiv.eq_of_nhds]; exact div_ne_zero h3 (by norm_num)
  -- The sign `σ` of `k 0`, and `a = 3 σ k`, positive near `0`.
  obtain ⟨σ, hσσ, hσk⟩ : ∃ σ : ℝ, σ * σ = 1 ∧ 0 < σ * k 0 := by
    rcases hk0.lt_or_gt with h | h
    exacts [⟨-1, by norm_num, by linarith⟩, ⟨1, by norm_num, by linarith⟩]
  set a : ℝ → ℝ := fun y ↦ 3 * σ * k y
  have ha : ContDiff ℝ n a := contDiff_const.mul hk
  have ha0 : 0 < a 0 := by simp only [a]; linarith
  -- The open neighbourhood `V` of `0` on which `φ` is a diffeomorphism.
  obtain ⟨U, hUsub, hUo, h0U⟩ := mem_nhds_iff.1 (hg₁g.and hs)
  set V := {y | 0 < a y} ∩ U
  have hVo : IsOpen V := (isOpen_lt continuous_const ha.continuous).inter hUo
  set φ : ℝ → ℝ := fun y ↦ σ * (y * a y ^ (3⁻¹ : ℝ))
  have hφ : ContDiffOn ℝ n φ V := fun y hy ↦
    (contDiffAt_const.mul (contDiffAt_id.mul
      (ha.contDiffAt.rpow_const_of_ne hy.1.ne'))).contDiffWithinAt
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast Order.one_le_iff_ne_zero.2 hn
  have hd : σ * a 0 ^ (3⁻¹ : ℝ) ≠ 0 :=
    mul_ne_zero (left_ne_zero_of_mul_eq_one hσσ) (Real.rpow_pos_of_pos ha0 _).ne'
  have hφd : HasDerivAt φ (σ * a 0 ^ (3⁻¹ : ℝ)) 0 := by
    have hb := ((ha.differentiable (by simpa using hn) 0).rpow_const
      (p := (3⁻¹ : ℝ)) (.inl ha0.ne')).hasDerivAt
    exact (((hasDerivAt_id 0).mul hb).const_mul σ).congr_deriv (by simp)
  obtain ⟨Θ, hΘ, h0Θ, hΘV, hΘsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hφ hVo ⟨ha0, h0U⟩ hn1
    (e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hd))
    (by rw [hφd.hasFDerivAt.fderiv]; ext; simp)
  refine ⟨Θ, h0Θ, fun y hy ↦ (hUsub (hΘV hy).2).2, by simp [hΘ, φ], hΘ ▸ hφ.mono hΘV, hΘsymm,
    fun y hy ↦ ?_⟩
  have hc : (a y ^ (3⁻¹ : ℝ)) ^ 3 = a y := by
    simpa using Real.rpow_inv_natCast_pow (n := 3) (hΘV hy).1.le (by norm_num)
  rw [← (hUsub (hΘV hy).2).1, hgk, hΘ,
    show φ y ^ 3 = σ ^ 3 * y ^ 3 * (a y ^ (3⁻¹ : ℝ)) ^ 3 by simp only [φ]; ring, hc]
  simp only [a]
  linear_combination (-(y ^ 3 * k y) * (σ * σ + 1)) * hσσ

end
