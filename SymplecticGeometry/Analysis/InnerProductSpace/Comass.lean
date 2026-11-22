/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.Comass

/-!
# Comass and Hilbert norm of forms, squared

Let `E` be a real inner product space of finite dimension `n`. Tau Ceti's
`ContinuousAlternatingMap.sqrt_alternatingFormInner_self_le` compares the Hilbert norm
`√⟨φ, φ⟩` of a real `k`-form `φ` on `E`, for the pointwise inner product of forms
`TauCeti.alternatingFormInner`, with its comass `‖φ‖`: `√⟨φ, φ⟩ ≤ √(n choose k) ‖φ‖`. This file
states the comparison for the squares, `⟨φ, φ⟩ ≤ (n choose k) ‖φ‖²`, the form in which it bounds
integrands of `L²` norms.

## Main results

* `ContinuousAlternatingMap.alternatingFormInner_self_le`:
  `⟨φ, φ⟩ ≤ (n choose k) * ‖φ‖ ^ 2`.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1.
-/

public section

open Module TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {k : ℕ}

namespace ContinuousAlternatingMap

/-- The pointwise inner product `⟨φ, φ⟩` of a real `k`-form on a space of dimension `n` is at
most `n choose k` times the square of its comass. -/
theorem alternatingFormInner_self_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) :
    alternatingFormInner E k φ φ ≤ (finrank ℝ E).choose k * ‖φ‖ ^ 2 := by
  have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_alternatingFormInner_self_le φ) 2
  rwa [Real.sq_sqrt (alternatingFormInner_self_nonneg φ), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)] at h

end ContinuousAlternatingMap

end
