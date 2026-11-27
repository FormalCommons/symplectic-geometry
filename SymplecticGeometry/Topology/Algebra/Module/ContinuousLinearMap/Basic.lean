/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Tactic.Abel

/-!
# Gluing two continuous linear maps along an endomorphism

For continuous linear maps `A B : M →L[R] M₂` and an endomorphism `P : M →L[R] M`, the map
`A ∘L P + B ∘L (id - P)` is `A` on the vectors that `P` fixes, and it differs from `B` by
`(A - B) ∘L P`. When `P` is a projection, it is `A` on the image of `P` and `B` on its kernel.

The holonomic approximation over a cube uses it with `A = fderiv ℝ f x`, `B = G x` and `P` the
projection onto the vectors in some of the coordinate directions.

## Main results

* `ContinuousLinearMap.comp_add_comp_id_sub_sub`: the difference with `B` is `(A - B) ∘L P`.-/

public section

namespace ContinuousLinearMap

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  [IsTopologicalAddGroup M₂]

/-- The map `A ∘L P + B ∘L (id - P)` differs from `B` by `(A - B) ∘L P`. -/
theorem comp_add_comp_id_sub_sub (A B : M →L[R] M₂) (P : M →L[R] M) :
    A ∘L P + B ∘L (ContinuousLinearMap.id R M - P) - B = (A - B) ∘L P := by
  rw [comp_sub, comp_id, sub_comp]
  abel

end ContinuousLinearMap

end
