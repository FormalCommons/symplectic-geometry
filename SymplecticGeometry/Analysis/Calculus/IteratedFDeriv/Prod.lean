/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Iterated derivatives in the second variable of a function on a product

* `ContDiffAt.continuousAt_iteratedFDeriv_prod_right`: if `f : P × E → F` is `Cⁿ` at `(p, x)`,
  then for `m ≤ n` the `m`-th iterated derivative of the slices `y ↦ f (q.1, y)`, evaluated at
  `q.2`, is continuous in `q` at `(p, x)`. It is the pointwise form of Tau Ceti's
  `ContDiff.continuous_iteratedFDeriv_prod_right`, and its proof is that proof at one point:
  Tau Ceti's `ContDiffAt.iteratedFDeriv_prod_right` writes the derivatives of a slice through
  those of `f`, near `(p, x)`, and Mathlib's `ContDiffAt.continuousAt_iteratedFDeriv` makes
  those continuous.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `f : P × E → F` is `Cⁿ` at `(p, x)` and `m ≤ n`, then
`q ↦ iteratedFDeriv 𝕜 m (fun y ↦ f (q.1, y)) q.2` is continuous at `(p, x)`. -/
theorem ContDiffAt.continuousAt_iteratedFDeriv_prod_right {n : WithTop ℕ∞} {f : P × E → F}
    {p : P} {x : E} (hf : ContDiffAt 𝕜 n f (p, x)) {m : ℕ} (hm : m ≤ n) :
    ContinuousAt (fun q : P × E ↦ iteratedFDeriv 𝕜 m (fun y ↦ f (q.1, y)) q.2) (p, x) := by
  have hf' : ContDiffAt 𝕜 m f (p, x) := hf.of_le hm
  refine ((ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin m ↦ ContinuousLinearMap.inr 𝕜 P E)).continuous.continuousAt.comp
      (hf'.continuousAt_iteratedFDeriv le_rfl)).congr ?_
  filter_upwards [hf'.eventually (by simp)] with q hq
  exact (hq.iteratedFDeriv_prod_right m le_rfl).symm

end
