/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint

/-!
# Self-adjoint endomorphisms of a bilinear form

The commutator of two endomorphisms that are self-adjoint for a bilinear form `B` is
skew-adjoint for `B`.

Let `B` be moreover symmetric and positive definite, on a finite-dimensional vector space over
an ordered field. An endomorphism `A` that is self-adjoint for `B` has nonnegative trace of its
square, and positive trace of its square unless it is zero.

These trace results follow from Tau Ceti's public lemmas
`LinearMap.BilinForm.trace_mul_self_nonpos_of_posDef` and
`LinearMap.BilinForm.trace_mul_self_eq_zero_iff_of_posDef` for skew-adjoint endomorphisms
(`TauCeti/LinearAlgebra/BilinearForm/SkewAdjoint.lean`), applied on `V × V` to Tau Ceti's
product form `LinearMap.BilinForm.prod B B` (`TauCeti/LinearAlgebra/BilinearForm/Prod.lean`)
and the endomorphism `(x, y) ↦ (-A y, A x)`, which is skew-adjoint for it and whose
square is `-(A * A)` on each factor.

## Main results

* `LinearMap.BilinForm.isSkewAdjoint_bracket_of_isSelfAdjoint`: the commutator of two
  self-adjoint endomorphisms is skew-adjoint.
* `LinearMap.BilinForm.trace_mul_self_nonneg_of_posDef`: the trace of the square of a
  self-adjoint endomorphism is nonnegative.
* `LinearMap.BilinForm.trace_mul_self_pos_of_posDef`: it is positive unless the endomorphism is
  zero.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Remark 12.2.14, for the trace-square argument in the skew-adjoint case.
-/

public section

open Module

namespace LinearMap.BilinForm

/-- The commutator of two endomorphisms that are self-adjoint for a bilinear form `B` is
skew-adjoint for `B`. -/
theorem isSkewAdjoint_bracket_of_isSelfAdjoint {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : LinearMap.BilinForm R M} {f g : Module.End R M}
    (hf : B.IsSelfAdjoint f) (hg : B.IsSelfAdjoint g) : ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [LinearMap.mem_skewAdjointSubmodule, LinearMap.IsSkewAdjoint, Ring.lie_def,
    ← LinearMap.coe_neg, neg_sub]
  exact (hf.mul hg).sub (hg.mul hf)

variable {F V : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A nonzero endomorphism that is self-adjoint for a symmetric positive-definite bilinear form
has positive trace of its square. -/
theorem trace_mul_self_pos_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) (h0 : A ≠ 0) : 0 < LinearMap.trace F V (A * A) := by
  -- The product form `B.prod B` on `V × V`, and the endomorphism `(x, y) ↦ (-A y, A x)`.
  let X : Module.End F (V × V) := (-(A ∘ₗ snd F V V)).prod (A ∘ₗ fst F V V)
  have hsymm' : (B.prod B).IsSymm := isSymm_prod_iff.mpr ⟨hsymm, hsymm⟩
  have hpos' : (B.prod B).toQuadraticMap.PosDef := by
    rw [toQuadraticMap_prod]
    exact hpos.prod hpos
  have hX : X ∈ (B.prod B).skewAdjointSubmodule := by
    rw [LinearMap.mem_skewAdjointSubmodule]
    intro x y
    simp only [X, BilinForm.prod_apply, LinearMap.prod_apply, Function.prod, fst_apply,
      snd_apply, LinearMap.comp_apply, map_neg, Pi.neg_apply, LinearMap.neg_apply, neg_add_rev]
    rw [hA x.1 y.2, hA x.2 y.1]
    abel
  have hXX : X * X = (-(A * A)).prodMap (-(A * A)) := by
    ext x <;> simp [X]
  have htr : LinearMap.trace F (V × V) (X * X) = -(2 * LinearMap.trace F V (A * A)) := by
    rw [hXX, LinearMap.trace_prodMap']
    rw [map_neg]
    ring
  have hX0 : X ≠ 0 := by
    intro h
    apply h0
    ext v
    simpa [X] using congrArg (fun f ↦ (f (v, 0)).2) h
  have hle := trace_mul_self_nonpos_of_posDef (B.prod B) hsymm' hpos' X hX
  have hne := (trace_mul_self_eq_zero_iff_of_posDef (B.prod B) hsymm' hpos' X hX).not.mpr hX0
  rw [htr] at hle hne
  exact lt_of_le_of_ne (by linarith) fun h ↦ hne (by rw [← h]; ring)

/-- An endomorphism that is self-adjoint for a symmetric positive-definite bilinear form has
nonnegative trace of its square. -/
theorem trace_mul_self_nonneg_of_posDef (B : LinearMap.BilinForm F V)
    (hsymm : B.IsSymm) (hpos : B.toQuadraticMap.PosDef) {A : Module.End F V}
    (hA : B.IsSelfAdjoint A) : 0 ≤ LinearMap.trace F V (A * A) := by
  obtain rfl | h0 := eq_or_ne A 0
  · simp
  · exact (trace_mul_self_pos_of_posDef B hsymm hpos hA h0).le

end LinearMap.BilinForm

end
