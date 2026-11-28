/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart.Basic
import SymplecticGeometry.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# Real-linear maps with dominant complex-linear part, for an almost complex structure

The surjectivity statement `ContinuousLinearMap.surjective_add_of_norm_lt` of
`SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart.Basic`, restated for Tau Ceti's
almost complex structures (`TauCeti.AlmostComplexStructure`, with
`TauCeti.AlmostComplexStructure.ofComplexModule` on the target) and its notions of complex linear
and complex antilinear maps, together with a norm bound for a real-linear form given by an inner
product and an orthogonal almost complex structure. No symplectic form is involved. The kernel
and orientation statements, which need one, are in
`SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart.Symplectic`.

## Main results

* `TauCeti.IsComplexLinear.surjective_of_norm_lt`: for `J` an almost complex structure and
  `A`, `B : V →L[ℝ] W` to a complex line, complex linear and complex antilinear in the sense of
  Tau Ceti's `TauCeti.IsComplexLinear` and `TauCeti.IsComplexAntilinear`, with `‖B‖ < ‖A‖`, the
  sum `A + B` is surjective.
* `TauCeti.AlmostComplexStructure.surjective_of_norm_complexAntilinearPart_lt`: a real-linear map
  `F` from a finite-dimensional `V` to a complex normed space `W` of dimension one whose
  complex-antilinear part (`TauCeti.complexAntilinearPartContinuousLinearMap`, for `J` and
  multiplication by `i`, `Complex.smulIEquiv W`) has smaller norm than its complex-linear part
  (`TauCeti.complexLinearPartContinuousLinearMap`) is surjective. This is the form needed at a
  zero of a section of a Hermitian line bundle, where the derivative takes values in the fibre.
* `TauCeti.AlmostComplexStructure.norm_le_of_re_apply_eq_inner`: on a real inner product space
  with an orthogonal almost complex structure `J`, a real-linear form whose real and imaginary
  parts are `⟪a, ·⟫` and `⟪J a, ·⟫` has norm at most `‖a‖`. It follows from Tau Ceti's
  `TauCeti.AlmostComplexStructure.inner_sq_add_inner_sq_le`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Module Complex

open scoped InnerProductSpace

namespace TauCeti

section Surjective

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] {J : AlmostComplexStructure V}

namespace IsComplexLinear

/-- **A real-linear map to a complex line with dominant complex-linear part is surjective.** Let
`W` be a complex normed space of dimension one, and let `A, B : V →L[ℝ] W` be complex linear and
complex antilinear respectively, for `J` and multiplication by `i` on `W`, with `‖B‖ < ‖A‖`.
Then `A + B` is surjective. -/
theorem surjective_of_norm_lt (hW : finrank ℂ W = 1) {A B : V →L[ℝ] W}
    (hA : IsComplexLinear J.toLinearMap (AlmostComplexStructure.ofComplexModule W).toLinearMap
      (A : V →ₗ[ℝ] W))
    (hB : IsComplexAntilinear J.toLinearMap
      (AlmostComplexStructure.ofComplexModule W).toLinearMap (B : V →ₗ[ℝ] W))
    (h : ‖B‖ < ‖A‖) : Function.Surjective (A + B) :=
  A.surjective_add_of_norm_lt hW
    (fun v ↦ by simpa [AlmostComplexStructure.ofComplexModule_apply] using hA.apply v)
    (fun v ↦ by simpa [AlmostComplexStructure.ofComplexModule_apply] using hB.apply v) h

end IsComplexLinear

namespace AlmostComplexStructure

/-- **A real-linear map to a complex line with dominant complex-linear part is surjective.**
Let `V` be finite-dimensional, let `W` be a complex normed space of dimension one, and let
`F : V →L[ℝ] W` be a real-linear map whose complex-antilinear part, for `J` and multiplication
by `i` on `W`, has smaller operator norm than its complex-linear part. Then `F` is
surjective. -/
theorem surjective_of_norm_complexAntilinearPart_lt [FiniteDimensional ℝ V]
    (hW : finrank ℂ W = 1) {F : V →L[ℝ] W}
    (h : ‖complexAntilinearPartContinuousLinearMap (LinearMap.toContinuousLinearMap J.toLinearMap)
        (smulIEquiv W : W →L[ℝ] W) F‖ <
      ‖complexLinearPartContinuousLinearMap (LinearMap.toContinuousLinearMap J.toLinearMap)
        (smulIEquiv W : W →L[ℝ] W) F‖) :
    Function.Surjective F := by
  have hs := IsComplexLinear.surjective_of_norm_lt hW
    (by
      rw [coe_complexLinearPartContinuousLinearMap_apply, LinearMap.coe_toContinuousLinearMap,
        coe_smulIEquiv_eq_ofComplexModule]
      exact isComplexLinear_complexLinearPart J.square_neg (ofComplexModule W).square_neg _)
    (by
      rw [coe_complexAntilinearPartContinuousLinearMap_apply, LinearMap.coe_toContinuousLinearMap,
        coe_smulIEquiv_eq_ofComplexModule]
      exact isComplexAntilinear_complexAntilinearPart J.square_neg (ofComplexModule W).square_neg _)
    h
  rwa [complexLinearPartContinuousLinearMap_add_complexAntilinearPartContinuousLinearMap_apply]
    at hs

end AlmostComplexStructure

end Surjective

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : AlmostComplexStructure V} {A : V →L[ℝ] ℂ}

/-- A real-linear form `A : V → ℂ` whose real and imaginary parts are `⟪a, ·⟫` and `⟪J a, ·⟫`,
for an orthogonal almost complex structure `J`, has norm at most `‖a‖`. -/
theorem AlmostComplexStructure.norm_le_of_re_apply_eq_inner
    (hJ : ∀ v w, ⟪J v, J w⟫_ℝ = ⟪v, w⟫_ℝ) {a : V}
    (ha : ∀ v, (A v).re = ⟪a, v⟫_ℝ) (him : ∀ v, (A v).im = ⟪J a, v⟫_ℝ) : ‖A‖ ≤ ‖a‖ := by
  refine A.opNorm_le_bound (norm_nonneg _) fun v ↦ ?_
  have h := inner_sq_add_inner_sq_le hJ v a
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [Complex.sq_norm, Complex.normSq_apply, ha, him, real_inner_comm v a, real_inner_comm v (J a),
    mul_pow, ← sq, ← sq]
  linarith

end Inner

end TauCeti
