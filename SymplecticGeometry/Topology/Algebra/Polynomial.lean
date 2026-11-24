/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomials near a point

Complements to Mathlib's `Mathlib/Topology/Algebra/Polynomial.lean`.

* `Polynomial.exists_eq_X_sub_C_pow_mul_eventually_eval_ne_zero`: over a topological
  commutative ring whose points are closed, a nonzero polynomial is `(X - C a) ^ k` times a
  polynomial that has no zero near `a`.
-/

public section

open Filter Topology

namespace Polynomial

/-- A nonzero polynomial is `(X - C a) ^ k` times a polynomial that has no zero near `a`. -/
theorem exists_eq_X_sub_C_pow_mul_eventually_eval_ne_zero {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [T1Space R] {p : R[X]} (hp : p ≠ 0)
    (a : R) : ∃ k : ℕ, ∃ q : R[X], p = (X - C a) ^ k * q ∧ ∀ᶠ z in 𝓝 a, q.eval z ≠ 0 := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  rw [dvd_iff_isRoot] at hq
  exact ⟨_, q, hpq, q.continuous.continuousAt.eventually_ne hq⟩

end Polynomial

end
