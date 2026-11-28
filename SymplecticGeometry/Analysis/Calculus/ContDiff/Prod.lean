/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.Prod

/-!
# Smoothness of the partial derivative in the first variable

`ContDiffAt.fderiv_slice_left`: if `f : P × E → X` is `Cⁿ` at `(p, x)` and `m + 1 ≤ n`, then
the partial derivative of `f` in the first variable, `q ↦ fderiv 𝕜 (fun l ↦ f (l, q.2)) q.1`,
is `Cᵐ` at `(p, x)`. This is the first-variable counterpart of Tau Ceti's
`ContDiffAt.fderiv_slice`, from which it follows by swapping the two factors.
-/

public section

namespace ContDiffAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The partial derivative in the first variable of a map on a product that is `Cⁿ` at `(p, x)`
is `Cᵐ` at `(p, x)`, jointly in both variables, for `m + 1 ≤ n`. -/
theorem fderiv_slice_left {n m : WithTop ℕ∞} {f : P × E → X} {p : P} {x : E}
    (hf : ContDiffAt 𝕜 n f (p, x)) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun q : P × E ↦ fderiv 𝕜 (fun l ↦ f (l, q.2)) q.1) (p, x) :=
  ((hf.comp (x, p) (contDiffAt_snd.prodMk contDiffAt_fst)).fderiv_slice hmn).comp (p, x)
    (contDiffAt_snd.prodMk contDiffAt_fst)

end ContDiffAt

end
