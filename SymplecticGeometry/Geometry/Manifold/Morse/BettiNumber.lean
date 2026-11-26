/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.BettiNumber

/-!
# The Euler characteristic of a compact manifold as a sum of Betti numbers

For a compact boundaryless manifold `M` of dimension `m`, modelled on any model with corners, and
a division ring `k`, the Betti numbers `bⱼ(M; k)` vanish above `m`
(`TauCeti.bettiNumber_eq_zero_of_finrank_lt`), so the Euler–Poincaré formula
`TauCeti.eulerChar_eq_finsum_finrank_singularHomology` becomes a finite sum
`eulerChar M = ∑ⱼ₌₀ⁿ (-1)ʲ bⱼ(M; k)` for every `n ≥ m`. Tau Ceti's
`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology` is the case `n = m` for a space charted
on the normed space itself.

## Main results

* `TauCeti.eulerChar_eq_sum_range_bettiNumber`: `χ(M) = ∑ⱼ₌₀ⁿ (-1)ʲ bⱼ(M; k)` for `n ≥ dim M`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Theorem 2.44.
-/

public section

open Module
open scoped Manifold ContDiff

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [FiniteCWType M]

include I in
/-- **The Euler characteristic of a compact manifold as an alternating sum of Betti numbers.**
For a compact boundaryless manifold `M` modelled on `I`, a division ring `k` and any `n` at least
the dimension of `M`, `eulerChar M = ∑ⱼ₌₀ⁿ (-1)ʲ bⱼ(M; k)`. The finite CW type of `M` is an
instance argument; `TauCeti.FiniteCWType.of_isManifold` supplies it. -/
theorem eulerChar_eq_sum_range_bettiNumber (k : Type u) [DivisionRing k] {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    eulerChar M = ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * bettiNumber k M j := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M k]
  simp only [bettiNumber_def]
  refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
  rw [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff]
  by_contra hlt
  have := bettiNumber_eq_zero_of_finrank_lt (I := I) (M := M) k (j := j) (by omega)
  rw [bettiNumber_def] at this
  simp [this] at hj

end TauCeti

end
