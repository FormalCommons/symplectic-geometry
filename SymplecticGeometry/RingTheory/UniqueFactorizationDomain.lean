/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Zeros of a homomorphism on a product of irreducible factors

For a nonzero `a` in a unique factorization monoid and a homomorphism `φ` of monoids with zero
into a commutative monoid with zero and without zero divisors, `φ a = 0` exactly when `φ p = 0`
for one of the irreducible factors `p ∈ UniqueFactorizationMonoid.factors a`
(`UniqueFactorizationMonoid.map_eq_zero_iff_exists_mem_factors`). For instance, a point is a
zero of a nonzero polynomial over a unique factorization domain exactly when it is a zero of
one of its irreducible factors.
-/

public section

namespace UniqueFactorizationMonoid

variable {α β F : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [CommMonoidWithZero β] [NoZeroDivisors β] [Nontrivial β] [FunLike F α β]
  [MonoidWithZeroHomClass F α β]

/-- A homomorphism of monoids with zero into a monoid with zero without zero divisors vanishes at
a nonzero element of a unique factorization monoid exactly when it vanishes at one of its
irreducible factors. -/
theorem map_eq_zero_iff_exists_mem_factors (φ : F) {a : α} (ha : a ≠ 0) :
    φ a = 0 ↔ ∃ p ∈ factors a, φ p = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨p, hp, hp0⟩ ↦ ?_⟩
  · obtain ⟨u, hu⟩ := factors_prod ha
    rw [← hu, map_mul, map_multiset_prod, mul_eq_zero] at h
    rcases h with h | h
    · obtain ⟨q, hq, hq0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h)
      exact ⟨q, hq, hq0⟩
    · exact absurd h (u.isUnit.map φ).ne_zero
  · exact zero_dvd_iff.1 (hp0 ▸ map_dvd φ (dvd_of_mem_factors hp))

end UniqueFactorizationMonoid

end
