/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convexity of the region above a hyperbola

In a linearly ordered commutative ring `𝕜`, for any constant `C`, the pairs `(p, q)` of
nonnegative elements with `C ≤ p * q` form a convex subset of `𝕜 × 𝕜`: the closed region of the
first quadrant on or above the hyperbola `p q = C`, which is the whole closed first quadrant when
`C ≤ 0`.

## Main results

* `SymplecticGeometry.convex_setOfPred_le_mul`: this region is convex.
-/

public section

namespace SymplecticGeometry

/-- In a linearly ordered commutative ring `𝕜`, for every `C : 𝕜`, the set of pairs `(p, q)` with
`0 ≤ p`, `0 ≤ q` and `C ≤ p * q` is convex. -/
theorem convex_setOfPred_le_mul {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (C : 𝕜) : Convex 𝕜 {z : 𝕜 × 𝕜 | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ C ≤ z.1 * z.2} := by
  rintro ⟨p₁, q₁⟩ ⟨hp₁, hq₁, h₁⟩ ⟨p₂, q₂⟩ ⟨hp₂, hq₂, h₂⟩ a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  refine ⟨by positivity, by positivity, ?_⟩
  rcases lt_or_ge C 0 with hC | hC
  · exact hC.le.trans (by positivity)
  have hprod : C * C ≤ (p₁ * q₂) * (p₂ * q₁) := by
    nlinarith [mul_le_mul h₁ h₂ hC (by positivity)]
  have hcross : 2 * C ≤ p₁ * q₂ + p₂ * q₁ :=
    two_mul_le_add_of_sq_le_mul (mul_nonneg hp₁ hq₂) (mul_nonneg hp₂ hq₁) (by rwa [sq])
  calc C = (a + b) ^ 2 * C := by rw [hab, one_pow, one_mul]
    _ = a ^ 2 * C + b ^ 2 * C + a * b * (2 * C) := by ring
    _ ≤ a ^ 2 * (p₁ * q₁) + b ^ 2 * (p₂ * q₂) + a * b * (p₁ * q₂ + p₂ * q₁) := by gcongr
    _ = (a * p₁ + b * p₂) * (a * q₁ + b * q₂) := by ring

end SymplecticGeometry

end
