/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Nonnegative bilinear forms from positive definite quadratic forms

If the quadratic form `x ↦ B x x` of a bilinear form `B` is positive definite
(`QuadraticMap.PosDef`), then `B` is nonnegative in the sense of Mathlib's
`LinearMap.BilinForm.IsNonneg`, that is `0 ≤ B x x` for every `x`. This is
`LinearMap.BilinForm.isNonneg_of_posDef`, which turns `QuadraticMap.PosDef.nonneg` into the
structure `IsNonneg`.
-/

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [PartialOrder R] [AddCommMonoid M] [Module R M]

/-- A bilinear form whose associated quadratic form `x ↦ B x x` is positive definite is
nonnegative: `0 ≤ B x x` for every `x`. -/
theorem isNonneg_of_posDef {B : LinearMap.BilinForm R M} (hB : B.toQuadraticMap.PosDef) :
    B.IsNonneg :=
  ⟨fun x ↦ by simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using hB.nonneg x⟩

end LinearMap.BilinForm

end
