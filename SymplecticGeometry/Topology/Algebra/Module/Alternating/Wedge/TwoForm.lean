/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Basic

/-!
# The first wedge power of a two-form

The first wedge power `ω ^ 1 = 1 ∧ ω` of a real alternating two-form `ω` is `ω` itself
(`ContinuousAlternatingMap.wedgePow_one`). It is the case `k = 2` of Tau Ceti's
`ContinuousAlternatingMap.wedgePow_one_apply`: there `2 * 1` reduces to `2`, the reindexing is
trivial, and the evaluation statement becomes an equality of forms. Together with Tau Ceti's
`ContinuousAlternatingMap.wedgePow_two_eq` it describes the low wedge powers of two-forms; on a
surface the symplectic volume form `σ¹ / 1!` of a two-form `σ` is `σ`.

## Main results

* `ContinuousAlternatingMap.wedgePow_one`: `wedgePow ω 1 = ω` for a two-form `ω`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14 (the wedge product in the determinant normalization).
-/

public section

namespace ContinuousAlternatingMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The first wedge power of a two-form is the form itself. -/
@[simp]
theorem wedgePow_one (ω : E [⋀^Fin 2]→L[ℝ] ℝ) : wedgePow ω 1 = ω := by
  ext v
  simp only [wedgePow_one_apply, Fin.cast_refl, Function.comp_id]

end ContinuousAlternatingMap

end
