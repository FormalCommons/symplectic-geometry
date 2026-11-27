/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic

/-!
# Maps that annihilate the argument of `oneSubExpNegDivSelf`

Tau Ceti's `oneSubExpNegDivSelf 𝕂 a` is the power series `∑ n, (n + 1)!⁻¹ • (-a) ^ n`, which
fills in the removable singularity of `(1 - exp (-a)) / a`. Every term after the constant one has
a factor `a` on the left, so a continuous linear map `f` with `f ∘L a = 0` does not see the
series: `f ∘L oneSubExpNegDivSelf 𝕂 a = f`.

## Main results

* `ContinuousLinearMap.comp_oneSubExpNegDivSelf_of_comp_eq_zero`: if `f ∘L a = 0`, then
  `f ∘L oneSubExpNegDivSelf 𝕂 a = f`.
* `ContinuousLinearMap.apply_oneSubExpNegDivSelf_apply_of_comp_eq_zero`: the same, evaluated at
  a vector.
-/

public section

namespace ContinuousLinearMap

variable {𝕂 E F : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- A continuous linear map that vanishes on the range of `a` is unchanged by composition with
`oneSubExpNegDivSelf 𝕂 a`: if `f ∘L a = 0`, then `f ∘L oneSubExpNegDivSelf 𝕂 a = f`. -/
theorem comp_oneSubExpNegDivSelf_of_comp_eq_zero {f : E →L[𝕂] F} {a : E →L[𝕂] E}
    (h : f ∘L a = 0) : f ∘L oneSubExpNegDivSelf 𝕂 a = f := by
  rw [oneSubExpNegDivSelf_eq_tsum, ← compL_apply,
    (compL 𝕂 E E F f).map_tsum (summable_oneSubExpNegDivSelf (𝕂 := 𝕂) a),
    tsum_eq_single 0 fun n hn ↦ ?_]
  · simp [one_def]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [pow_succ', mul_def, ← comp_assoc, h]

/-- If `f ∘L a = 0`, then `f (oneSubExpNegDivSelf 𝕂 a y) = f y` for every `y`. -/
theorem apply_oneSubExpNegDivSelf_apply_of_comp_eq_zero {f : E →L[𝕂] F} {a : E →L[𝕂] E}
    (h : f ∘L a = 0) (y : E) : f (oneSubExpNegDivSelf 𝕂 a y) = f y :=
  congr($(comp_oneSubExpNegDivSelf_of_comp_eq_zero h) y)

end ContinuousLinearMap

end
