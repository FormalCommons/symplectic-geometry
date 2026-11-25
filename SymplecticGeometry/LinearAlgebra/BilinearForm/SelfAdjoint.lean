/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Self-adjoint endomorphisms of a bilinear form

The commutator of two endomorphisms that are self-adjoint for a bilinear form `B` is
skew-adjoint for `B`. This is the self-adjoint counterpart of Mathlib's
`LinearMap.BilinForm.isSkewAdjoint_bracket`, for two skew-adjoint endomorphisms.

The trace criteria for self-adjoint endomorphisms of a symmetric positive-definite form are
Tau Ceti's `LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair` and
`LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair`, applied to the adjoint pair
`(A, A)`.

## Main results

* `LinearMap.BilinForm.isSkewAdjoint_bracket_of_isSelfAdjoint`: the commutator of two
  self-adjoint endomorphisms is skew-adjoint.
-/

public section

namespace LinearMap.BilinForm

/-- The commutator of two endomorphisms that are self-adjoint for a bilinear form `B` is
skew-adjoint for `B`. -/
theorem isSkewAdjoint_bracket_of_isSelfAdjoint {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : LinearMap.BilinForm R M} {f g : Module.End R M}
    (hf : B.IsSelfAdjoint f) (hg : B.IsSelfAdjoint g) : ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule, LinearMap.IsSkewAdjoint, Ring.lie_def,
    ← LinearMap.coe_neg, neg_sub]
  exact (hf.mul hg).sub (hg.mul hf)

end LinearMap.BilinForm

end
