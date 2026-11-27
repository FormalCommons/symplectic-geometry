/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.IteratedFDeriv.SymmetricFinite

/-!
# Iterated derivatives on tuples with one entry changed

For `f` of class `C^n` at `x` with `minSmoothness 𝕜 (k + 1) ≤ n` (that is, `C^(k+1)` over `ℝ`
or `ℂ`), the iterated derivative `D^(k+1) f(x)` is symmetric, so its value on the tuple
`(y, …, y)` with one entry replaced by `u` does not depend on which entry is replaced.
Summing over the entries gives the derivative of `y ↦ D^(k+1) f(x) (y, …, y)` in the
direction `u`.

## Main results

* `ContDiffAt.sum_iteratedFDeriv_update_const`:
  `∑ᵢ D^(k+1) f(x) (y, …, u, …, y) = (k + 1) • D^(k+1) f(x) (u, y, …, y)`. It follows from Tau
  Ceti's `ContDiffAt.iteratedFDeriv_comp_perm_of_le`.
-/

public section

/-- If `f` is `C^n` at `x` with `minSmoothness 𝕜 (k + 1) ≤ n`, then by the symmetry of
`D^(k+1) f(x)`, replacing one of `k + 1` equal arguments `y` by `u` gives the same value wherever
`u` is placed: `∑ᵢ D^(k+1) f(x) (y, …, u, …, y) = (k + 1) • D^(k+1) f(x) (u, y, …, y)`. -/
theorem ContDiffAt.sum_iteratedFDeriv_update_const {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E} {k : ℕ} {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕜 n f x) (hk : minSmoothness 𝕜 (k + 1) ≤ n) (y u : E) :
    ∑ i, iteratedFDeriv 𝕜 (k + 1) f x (Function.update (fun _ ↦ y) i u) =
      (k + 1) • iteratedFDeriv 𝕜 (k + 1) f x (Fin.cons u fun _ ↦ y) := by
  have hupd (i : Fin (k + 1)) : Function.update (fun _ ↦ y) i u =
      (Fin.cons u fun _ ↦ y : Fin (k + 1) → E) ∘ Equiv.swap 0 i := by
    funext l
    cases l using Fin.cases <;> cases i using Fin.cases <;>
      simp [Equiv.swap_apply_def, Function.update_apply, Fin.succ_ne_zero, eq_comm]
    split_ifs <;> simp
  simp_rw [hupd, hf.iteratedFDeriv_comp_perm_of_le (k := k + 1) hk]
  simp

end
