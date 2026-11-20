/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.DysonSeries

/-!
# Smoothness of the left Dyson series

Tau Ceti's `TauCeti.contDiff_dysonSeriesLeft` says that the left Dyson series of a `Cᵏ` path,
for a natural number `k`, is `Cᵏ⁺¹`. This file extends it to every order `n : ℕ∞`, in particular
to smooth paths.

## Main results

* `SymplecticGeometry.contDiff_add_one_dysonSeriesLeft`: if `p` is `Cⁿ` for `n : ℕ∞`, then the
  solution `dysonSeriesLeft p` of `Γ' t = p t * Γ t`, `Γ 0 = 1`, is `Cⁿ⁺¹`.
-/

public section

namespace SymplecticGeometry

open TauCeti

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] {p : ℝ → B}

/-- The left Dyson series of a `Cⁿ` path, for any `n : ℕ∞`, is `Cⁿ⁺¹`. -/
theorem contDiff_add_one_dysonSeriesLeft {n : ℕ∞} (hp : ContDiff ℝ n p) :
    ContDiff ℝ (n + 1) (dysonSeriesLeft p) := by
  have h : ContDiff ℝ ((n + 1 : ℕ∞) : WithTop ℕ∞) (dysonSeriesLeft p) := by
    refine contDiff_iff_forall_nat_le.2 fun m hm => ?_
    rcases m with _ | k
    · exact contDiff_zero.2 (continuous_dysonSeriesLeft hp.continuous)
    · have hk : (k : ℕ∞) ≤ n := by
        rw [Nat.cast_add, Nat.cast_one] at hm
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hm
      exact_mod_cast contDiff_dysonSeriesLeft (hp.of_le (by exact_mod_cast hk))
  exact_mod_cast h

end SymplecticGeometry

end
