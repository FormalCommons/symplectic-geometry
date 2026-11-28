/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Hadamard.Basic

/-!
# Hadamard's lemma in one variable

A function `f` of one real variable of class `C^(n+1)` is `f x + (u - x) • g u` for a function
`g` of class `C^n`: `g u` is the average of `f'` over the segment from `x` to `u`, Tau Ceti's
`hadamardFactor f x u` applied to `1`. So `g` is smooth when `f` is, also at `u = x`,
where the quotient `(f u - f x) / (u - x)` is not defined. At `u = x` the factor is the
derivative: `g x = deriv f x`.

The same holds to any order `m`. If `f` is of class `C^(n+m)` and its derivatives of order less
than `m` vanish at `x`, then `f u = (u - x) ^ m • g u` for a function `g` of class `C^n`, with
`g x = f⁽ᵐ⁾(x) / m!`. For `m ≥ 1`, `g u` is Tau Ceti's
`TauCeti.taylorRemainderFactor (m - 1) f x u` applied to `m` copies of `1`, by Taylor's formula
with the remainder written as a weighted average of the `m`-th derivative
(`ContDiff.eq_sum_add_taylorRemainderFactor_apply`).

## Main results

* `ContDiff.exists_contDiff_sub_eq_sub_smul`: `f u - f x = (u - x) • g u` with `g` of class `C^n`
  and `g x = deriv f x`.
* `ContDiff.exists_contDiff_eq_pow_smul`: `f u = (u - x) ^ m • g u` with `g` of class `C^n` and
  `g x = f⁽ᵐ⁾(x) / m!`, when the derivatives of `f` of order less than `m` vanish at `x`.
-/

public section

open scoped ContDiff Nat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Hadamard's lemma** in one variable: for `f : ℝ → F` of class `C^(n+1)` and a point `x`,
there is `g : ℝ → F` of class `C^n` with `f u - f x = (u - x) • g u` for all `u`, and
`g x = deriv f x`. -/
theorem ContDiff.exists_contDiff_sub_eq_sub_smul {n : ℕ∞} {f : ℝ → F} (hf : ContDiff ℝ (n + 1) f)
    (x : ℝ) :
    ∃ g : ℝ → F, ContDiff ℝ n g ∧ (∀ u, f u - f x = (u - x) • g u) ∧ g x = deriv f x := by
  refine ⟨fun u ↦ hadamardFactor f x u 1,
    (ContDiff.contDiff_hadamardFactor_of_succ n f hf x).clm_apply contDiff_const, fun u ↦ ?_,
    by simp [hadamardFactor_self]⟩
  rw [ContDiff.sub_eq_hadamardFactor_apply f (hf.of_le (by simp)) x u, ← map_smul, smul_eq_mul,
    mul_one]

/-- **Factoring out a zero of order `m`** in one variable: if `f : ℝ → F` is of class `C^(n+m)`
and its derivatives of order less than `m` vanish at `x`, then there is `g : ℝ → F` of class `C^n`
with `f u = (u - x) ^ m • g u` for all `u`, and `g x` is the `m`-th derivative of `f` at `x`
divided by `m!`. -/
theorem ContDiff.exists_contDiff_eq_pow_smul {n : ℕ∞} {m : ℕ} {f : ℝ → F}
    (hf : ContDiff ℝ (n + m : ℕ∞) f) {x : ℝ} (hfx : ∀ i < m, iteratedDeriv i f x = 0) :
    ∃ g : ℝ → F, ContDiff ℝ n g ∧ (∀ u, f u = (u - x) ^ m • g u) ∧
      g x = (m ! : ℝ)⁻¹ • iteratedDeriv m f x := by
  obtain _ | j := m
  · exact ⟨f, by simpa using hf, by simp, by simp⟩
  -- The Taylor polynomial of `f` of order `j` at `x` vanishes, so `f` is its remainder term.
  set R := TauCeti.taylorRemainderFactor j f x
  refine ⟨fun u ↦ R u (fun _ ↦ 1),
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j + 1) ↦ ℝ) F fun _ ↦ 1).contDiff.comp
      (ContDiff.contDiff_taylorRemainderFactor (by exact_mod_cast hf) x), fun u ↦ ?_, ?_⟩
  · have hR : R u (fun _ ↦ u - x) = (u - x) ^ (j + 1) • R u (fun _ ↦ 1) := by
      simpa using R u |>.map_smul_univ (fun _ ↦ u - x) (fun _ ↦ (1 : ℝ))
    rw [ContDiff.eq_sum_add_taylorRemainderFactor_apply (n := j)
      (hf.of_le (by push_cast; exact le_add_self)) x u, hR,
      Finset.sum_eq_zero fun i hi ↦ ?_, zero_add]
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hfx i (Finset.mem_range.1 hi), smul_zero,
      smul_zero]
  · simp only [R, TauCeti.taylorRemainderFactor_self, smul_apply,
      iteratedDeriv_eq_iteratedFDeriv]

end
