/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Continuity of evaluation of multivariate polynomials

Complements to Mathlib's `Mathlib/Topology/Algebra/MvPolynomial.lean`.

* `Continuous.mvPolynomial_eval`: evaluating a fixed multivariate polynomial at a continuously
  varying point is continuous. It is tagged `@[fun_prop]`, so `fun_prop` proves such goals.
-/

public section

variable {X σ R : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R]
  [IsTopologicalSemiring R]

/-- If `f : X → σ → R` is continuous, then so is `x ↦ eval (f x) P`, for every multivariate
polynomial `P`. -/
@[fun_prop]
theorem Continuous.mvPolynomial_eval {f : X → σ → R} (hf : Continuous f)
    (P : MvPolynomial σ R) : Continuous fun x => MvPolynomial.eval (f x) P :=
  (MvPolynomial.continuous_eval P).comp hf

end
