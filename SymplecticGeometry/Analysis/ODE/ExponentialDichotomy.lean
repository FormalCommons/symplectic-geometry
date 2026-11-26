/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear
import TauCeti.Analysis.ODE.ExponentialDichotomy

/-!
# Exponential dichotomies split the space

If the flow of an operator `A` on a Banach space has an exponential dichotomy, given by an
idempotent `P` commuting with `A` together with forward bounds on the range of `P` and backward
bounds on its kernel, then the stable and unstable subspaces of `A` are complementary. This
follows from Tau Ceti's `ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds` and
`ContinuousLinearMap.range_id_sub_eq_unstableSubspace_of_exponential_bounds`, since the range and
the kernel of an idempotent are complementary.

## Main results

* `ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace_of_exponential_bounds`: the stable
  and unstable subspaces of an operator whose flow has an exponential dichotomy are
  complementary.
-/

public section

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace ContinuousLinearMap

/-- If an idempotent `P` commuting with `A` gives an exponential dichotomy of the flow of `A`
with rate `α > 0`, then the stable and unstable subspaces of `A` are complementary. -/
theorem isCompl_stableSubspace_unstableSubspace_of_exponential_bounds {A P : X →L[ℝ] X}
    {K α : ℝ} (hα : 0 < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) :
    IsCompl A.stableSubspace A.unstableSubspace := by
  have h := LinearMap.IsIdempotentElem.isCompl (IsIdempotentElem.toLinearMap hP)
  rw [LinearMap.IsIdempotentElem.ker_eq_range (IsIdempotentElem.toLinearMap hP)] at h
  rw [← range_eq_stableSubspace_of_exponential_bounds hα hP hAP hs hu,
    ← range_id_sub_eq_unstableSubspace_of_exponential_bounds hα hP hAP hs hu]
  rwa [toLinearMap_sub, coe_id]

end ContinuousLinearMap

end
