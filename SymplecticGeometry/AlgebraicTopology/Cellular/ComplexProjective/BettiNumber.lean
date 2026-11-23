/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Basic
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

/-!
# The Betti numbers of complex projective space

Over a ring `k` with the strong rank condition, such as a division ring or a nontrivial
commutative ring, the Betti numbers of `CPⁿ` are `bⱼ = 1` for even `j ≤ 2n` and `bⱼ = 0`
otherwise (`TauCeti.bettiNumber_complexProjectiveSpace`). This reads off ranks from Tau Ceti's
computation of the singular homology of `CPⁿ`:
`TauCeti.ComplexProjectiveSpace.singularHomologyIso` in the even degrees up to `2n`, and
`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_odd` and
`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_lt` in the other degrees. The proof
follows that of Tau Ceti's `TauCeti.ComplexProjectiveSpace.finrank_singularCohomology`, with
homology in place of cohomology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, the cellular
  homology of `CPⁿ` after Theorem 2.35.
-/

public section

open Module

namespace TauCeti

/-- **The Betti numbers of complex projective space.** Over a ring `k` with the strong rank
condition, such as a division ring or a nontrivial commutative ring, the `j`-th Betti number of
`CPⁿ` is `1` if `j` is even with `j ≤ 2n`, and `0` otherwise. -/
theorem bettiNumber_complexProjectiveSpace (k : Type) [Ring k] [StrongRankCondition k]
    (n j : ℕ) :
    bettiNumber k (ComplexProjectiveSpace n) j = if Even j ∧ j ≤ 2 * n then 1 else 0 := by
  rw [bettiNumber_def]
  split_ifs with h
  · obtain ⟨⟨i, rfl⟩, hj⟩ := h
    rw [← two_mul] at hj ⊢
    rw [(ComplexProjectiveSpace.singularHomologyIso (ModuleCat.of k k)
      (by omega : i ≤ n)).toLinearEquiv.finrank_eq]
    exact finrank_self k
  · rw [not_and_or, Nat.not_even_iff_odd, not_le] at h
    have := ModuleCat.subsingleton_of_isZero <| h.elim
      (ComplexProjectiveSpace.isZero_singularHomology_of_odd (n := n) (ModuleCat.of k k))
      (ComplexProjectiveSpace.isZero_singularHomology_of_lt (n := n) (ModuleCat.of k k))
    exact finrank_zero_of_subsingleton

end TauCeti

end
