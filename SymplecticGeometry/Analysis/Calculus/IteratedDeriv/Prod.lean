/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Iterated derivatives in the second variable of a function of two variables

`ContDiffAt.continuousAt_iteratedDeriv_prod_right`: if `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)`, then
for `m ≤ n` the `m`-th iterated derivative of the slices `y ↦ f (q.1, y)`, evaluated at `q.2`,
is continuous in `q` at `(p, x)`. It is the one-variable form of Tau Ceti's
`ContDiffAt.iteratedFDeriv_prod_right`, which writes the derivatives of a slice through those of
`f`, and of Mathlib's `ContDiffAt.continuousAt_iteratedFDeriv`.
-/

public section

open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : P × 𝕜 → F` is `Cⁿ` at `(p, x)` and `m ≤ n`, then
`q ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2` is continuous at `(p, x)`. -/
theorem ContDiffAt.continuousAt_iteratedDeriv_prod_right {n : WithTop ℕ∞} {f : P × 𝕜 → F}
    {p : P} {x : 𝕜} (hf : ContDiffAt 𝕜 n f (p, x)) {m : ℕ} (hm : m ≤ n) :
    ContinuousAt (fun q : P × 𝕜 ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2) (p, x) := by
  have hf' : ContDiffAt 𝕜 m f (p, x) := hf.of_le hm
  have h : (fun q : P × 𝕜 ↦ iteratedFDeriv 𝕜 m f q fun _ ↦ (0, 1)) =ᶠ[𝓝 (p, x)]
      fun q : P × 𝕜 ↦ iteratedDeriv m (fun y ↦ f (q.1, y)) q.2 := by
    filter_upwards [hf'.eventually (by simp)] with q hq
    rw [iteratedDeriv_eq_iteratedFDeriv, hq.iteratedFDeriv_prod_right m le_rfl]
    rfl
  exact ((continuous_eval_const _).continuousAt.comp
    (hf'.continuousAt_iteratedFDeriv le_rfl)).congr h
