/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Hadamard.Basic

/-!
# Hadamard's lemma in one variable

A function `f` of one real variable of class `C^(n+1)` is `f x + (u - x) • g u` for a function
`g` of class `C^n`: `g u` is the average of `f'` over the segment from `x` to `u`, Tau Ceti's
`hadamardFactor f x u` applied to `1`. So `g` is smooth when `f` is, also at `u = x`,
where the quotient `(f u - f x) / (u - x)` is not defined. At `u = x` the factor is the
derivative: `g x = deriv f x`.

## Main results

* `ContDiff.exists_contDiff_sub_eq_smul`: `f u - f x = (u - x) • g u` with `g` of class `C^n`
  and `g x = deriv f x`.
-/

public section

open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Hadamard's lemma** in one variable: for `f : ℝ → F` of class `C^(n+1)` and a point `x`,
there is `g : ℝ → F` of class `C^n` with `f u - f x = (u - x) • g u` for all `u`, and
`g x = deriv f x`. -/
theorem ContDiff.exists_contDiff_sub_eq_smul {n : ℕ∞} {f : ℝ → F} (hf : ContDiff ℝ (n + 1) f)
    (x : ℝ) :
    ∃ g : ℝ → F, ContDiff ℝ n g ∧ (∀ u, f u - f x = (u - x) • g u) ∧ g x = deriv f x := by
  refine ⟨fun u ↦ hadamardFactor f x u 1,
    (ContDiff.contDiff_hadamardFactor_of_succ n f hf x).clm_apply contDiff_const, fun u ↦ ?_,
    by simp [hadamardFactor_self]⟩
  rw [ContDiff.sub_eq_hadamardFactor_apply f (hf.of_le (by simp)) x u, ← map_smul, smul_eq_mul,
    mul_one]

end
