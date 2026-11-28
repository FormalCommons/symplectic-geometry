/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Calculus.IteratedFDeriv.Parametric

/-!
# Iterated derivatives in the second variable of a function of two variables

* `ContDiffAt.continuousAt_iteratedDeriv_prod_right`: if `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)`,
  then for `m ≤ n` the `m`-th iterated derivative of the slices `y ↦ f (q.1, y)`, evaluated at
  `q.2`, is continuous in `q` at `(p, x)`. It is the one-variable form of the case of order zero
  of Tau Ceti's `ContDiffAt.iteratedFDeriv_snd`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)` and `m ≤ n`, then
`q ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2` is continuous at `(p, x)`. -/
theorem ContDiffAt.continuousAt_iteratedDeriv_prod_right {n : WithTop ℕ∞} {f : P × 𝕜 → F}
    {p : P} {x : 𝕜} (hf : ContDiffAt 𝕜 n f (p, x)) {m : ℕ} (hm : m ≤ n) :
    ContinuousAt (fun q : P × 𝕜 ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2) (p, x) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  have h := ContDiffAt.iteratedFDeriv_snd (m := 0) (f := fun a y ↦ f (a, y)) hf
    (i := m) (by simpa using hm)
  exact (continuous_eval_const _).continuousAt.comp h.continuousAt
