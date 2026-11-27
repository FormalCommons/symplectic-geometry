/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.Cayley.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint
public import TauCeti.LinearAlgebra.Trace.Complex
import SymplecticGeometry.LinearAlgebra.BilinearForm.SelfAdjoint

/-!
# Tangent spaces to the space of compatible complex structures, as algebra

For an almost complex structure `J` on a real vector space `V`, Tau Ceti's `J.tangentSpace` is
the space of endomorphisms `Y` with `Y J + J Y = 0`, and for a symplectic form `ω`,
`ω.compatibleTangentSpace J` is the subspace of those that are moreover skew-adjoint for `ω`.
For a compatible `J` the latter is the tangent space at `J` to the space of `ω`-compatible
complex structures. This file proves the algebraic identities about these spaces on which the
Kähler structure of that space rests (McDuff–Salamon, Example 4.3.6 and Exercise 4.3.7).
It also describes Tau Ceti's compatible Cayley ball at `J` inside the compatible tangent space.

## Main results

* `TauCeti.AlmostComplexStructure.trace_mul_eq_zero_of_mem_tangentSpace`: a tangent vector `Y`
  at `J` has `trace (Y * Z) = 0` for every `Z` commuting with `J`.
* `TauCeti.AlmostComplexStructure.commute_mul_of_mem_tangentSpace`: the product of two tangent
  vectors at `J` commutes with `J`.
* `TauCeti.AlmostComplexStructure.trace_mul_mul_eq_neg_of_mem_tangentSpace`:
  `trace (Y * J * Z) = -trace (Z * J * Y)` for a tangent vector `Y` at `J`, so that the trace
  of `Y * J * Z` is alternating in `Y` and `Z`.
* `TauCeti.SymplecticForm.Invariant.mul_mem_compatibleTangentSpace`: the compatible tangent
  space at `J` is preserved by composition with `J` on the left.
* `TauCeti.SymplecticForm.mem_compatibleCayleyBall_iff_mem_compatibleTangentSpace`: Tau Ceti's
  compatible Cayley ball of `J` consists of the compatible tangent vectors at `J` that strictly
  contract `v ↦ ω(v, J v)`.
* `TauCeti.SymplecticForm.Compatible.trace_mul_self_pos`: for a compatible `J`, a nonzero
  compatible tangent vector `Y` has `0 < trace (Y * Y)`.
* `TauCeti.SymplecticForm.Compatible.trace_commutator_sq_nonpos`: for a compatible `J` and
  compatible tangent vectors `Y` and `Z`, `trace (⁅Y, Z⁆ * ⁅Y, Z⁆) ≤ 0`.
* `TauCeti.SymplecticForm.IsSymplectomorphism.conj_mem_compatibleTangentSpace_iff`: conjugation
  by a linear symplectomorphism `e` carries the compatible tangent space at `J` onto that at the
  transported structure `J.transport e`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 and Exercise 4.3.7.
-/

public section

namespace TauCeti

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

namespace AlmostComplexStructure

variable {J : AlmostComplexStructure V} {Y : Module.End ℝ V}

/-- A tangent vector `Y` at `J` is trace-orthogonal to every endomorphism `Z` commuting with `J`:
conjugation by `J` changes the sign of `Y` and fixes `Z`. -/
theorem trace_mul_eq_zero_of_mem_tangentSpace (hY : Y ∈ J.tangentSpace) {Z : Module.End ℝ V}
    (hZ : Commute Z J.toLinearMap) : LinearMap.trace ℝ V (Y * Z) = 0 := by
  let := J.complexModule
  have := J.complexModule_isScalarTower
  refine LinearMap.trace_eq_zero_of_map_I_smul_eq_neg _ fun v ↦ ?_
  have hZv : Z (J v) = J (Z v) := congrArg (· v) hZ.eq
  simp only [mul_apply_eq_comp, J.complexModule_I_smul, hZv]
  exact AlmostComplexStructure.mem_tangentSpace_iff_apply.1 hY _

/-- The product of two tangent vectors at `J` commutes with `J`, since each of them anticommutes
with it. -/
theorem commute_mul_of_mem_tangentSpace (hY : Y ∈ J.tangentSpace) {Z : Module.End ℝ V}
    (hZ : Z ∈ J.tangentSpace) : Commute (Y * Z) J.toLinearMap := by
  rw [commute_iff_eq, mul_assoc, eq_neg_of_add_eq_zero_left (mem_tangentSpace.1 hZ), mul_neg,
    ← mul_assoc, eq_neg_of_add_eq_zero_left (mem_tangentSpace.1 hY), neg_mul, neg_neg, mul_assoc]

/-- For a tangent vector `Y` at `J` and any endomorphism `Z`,
`trace (Y * J * Z) = -trace (Z * J * Y)`. -/
theorem trace_mul_mul_eq_neg_of_mem_tangentSpace (hY : Y ∈ J.tangentSpace)
    (Z : Module.End ℝ V) :
    LinearMap.trace ℝ V (Y * J.toLinearMap * Z) =
      -LinearMap.trace ℝ V (Z * J.toLinearMap * Y) := by
  rw [eq_neg_of_add_eq_zero_left (mem_tangentSpace.1 hY), neg_mul, map_neg,
    LinearMap.trace_mul_cycle]

/-- Conjugation by a linear equivalence `e` carries the tangent space at `J` onto the tangent
space at the transported structure `J.transport e`. -/
theorem conj_mem_tangentSpace_transport_iff (e : V ≃ₗ[ℝ] W) :
    e.conj Y ∈ (J.transport e).tangentSpace ↔ Y ∈ J.tangentSpace := by
  rw [mem_tangentSpace_iff_apply, mem_tangentSpace_iff_apply, e.surjective.forall]
  simp only [transport_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact forall_congr' fun v ↦ by rw [← map_neg, e.injective.eq_iff]

end AlmostComplexStructure

namespace SymplecticForm

variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {Y Z : Module.End ℝ V}

/-- A compatible tangent vector at `J` is self-adjoint for the associated form `ω(·, J ·)`. -/
theorem isSelfAdjoint_of_mem_compatibleTangentSpace (hY : Y ∈ ω.compatibleTangentSpace J) :
    (ω.associatedBilinForm J).IsSelfAdjoint Y :=
  (mem_compatibleTangentSpace_iff_isSelfAdjoint (compatibleTangentSpace_le_tangentSpace hY)).1 hY

/-- The compatible Cayley ball of `J` is the set of elements of the compatible tangent space at
`J` that strictly contract the quadratic form `v ↦ ω(v, J v)`: for an endomorphism
anticommuting with `J`, self-adjointness for `ω(·, J ·)` is skew-adjointness for `ω`. -/
theorem mem_compatibleCayleyBall_iff_mem_compatibleTangentSpace {C : Module.End ℝ V} :
    C ∈ ω.compatibleCayleyBall J ↔
      C ∈ ω.compatibleTangentSpace J ∧ ∀ v, v ≠ 0 → ω (C v) (J (C v)) < ω v (J v) := by
  have hT : C ∈ J.tangentSpace ↔ C * J.toLinearMap = -(J.toLinearMap * C) := by
    rw [AlmostComplexStructure.mem_tangentSpace, add_eq_zero_iff_eq_neg]
  rw [mem_compatibleCayleyBall, mem_cayleyBall]
  constructor
  · rintro ⟨⟨hA, hc⟩, hS⟩
    exact ⟨(mem_compatibleTangentSpace_iff_isSelfAdjoint (hT.2 hA)).2 hS, hc⟩
  · rintro ⟨hY, hc⟩
    have hA := hT.1 (compatibleTangentSpace_le_tangentSpace hY)
    exact ⟨⟨hA, hc⟩, (mem_compatibleTangentSpace_iff_isSelfAdjoint (hT.2 hA)).1 hY⟩

/-- For a `J`-invariant `ω`, composing a compatible tangent vector at `J` with `J` on the left
gives a compatible tangent vector at `J`. -/
theorem Invariant.mul_mem_compatibleTangentSpace (h : ω.Invariant J)
    (hY : Y ∈ ω.compatibleTangentSpace J) :
    J.toLinearMap * Y ∈ ω.compatibleTangentSpace J :=
  have h' := h.mul_mem_tangentSpace_and_isSelfAdjoint hY
  (mem_compatibleTangentSpace_iff_isSelfAdjoint h'.1).2 h'.2

/-- Conjugation by a linear symplectomorphism `e` from `(V, ω)` to `(W, ω₂)` carries the
compatible tangent space of `ω` at `J` onto the compatible tangent space of `ω₂` at the
transported structure `J.transport e`. -/
theorem IsSymplectomorphism.conj_mem_compatibleTangentSpace_iff {ω₂ : SymplecticForm W}
    {e : V ≃ₗ[ℝ] W} (he : IsSymplectomorphism ω ω₂ e) :
    e.conj Y ∈ ω₂.compatibleTangentSpace (J.transport e) ↔ Y ∈ ω.compatibleTangentSpace J := by
  have h := AlmostComplexStructure.conj_mem_tangentSpace_transport_iff (J := J) (Y := Y) e
  rw [AlmostComplexStructure.mem_tangentSpace_iff_apply,
    AlmostComplexStructure.mem_tangentSpace_iff_apply] at h
  rw [mem_compatibleTangentSpace, mem_compatibleTangentSpace, h, e.surjective.forall₂]
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, he.apply]

variable [FiniteDimensional ℝ V]

/-- For an `ω`-compatible `J`, a nonzero compatible tangent vector `Y` at `J` has
`0 < trace (Y * Y)`. -/
theorem Compatible.trace_mul_self_pos (hJ : ω.Compatible J)
    (hY : Y ∈ ω.compatibleTangentSpace J) (h0 : Y ≠ 0) :
    0 < LinearMap.trace ℝ V (Y * Y) := by
  have hY' := isSelfAdjoint_of_mem_compatibleTangentSpace hY
  refine (LinearMap.BilinForm.trace_mul_nonneg_of_isAdjointPair _
    hJ.associatedBilinForm_isSymm hJ.positive hY').lt_of_ne fun h ↦ h0 ?_
  exact (LinearMap.BilinForm.trace_mul_eq_zero_iff_of_isAdjointPair _
    hJ.associatedBilinForm_isSymm hJ.positive hY').1 h.symm

/-- For an `ω`-compatible `J` and compatible tangent vectors `Y` and `Z` at `J`, the square of
the commutator `⁅Y, Z⁆` has nonpositive trace: `⁅Y, Z⁆` is skew-adjoint for the inner product
`ω(·, J ·)`. -/
theorem Compatible.trace_commutator_sq_nonpos (hJ : ω.Compatible J)
    (hY : Y ∈ ω.compatibleTangentSpace J) (hZ : Z ∈ ω.compatibleTangentSpace J) :
    LinearMap.trace ℝ V (⁅Y, Z⁆ * ⁅Y, Z⁆) ≤ 0 :=
  LinearMap.BilinForm.trace_mul_self_nonpos_of_posDef _ hJ.associatedBilinForm_isSymm
    hJ.positive _ (LinearMap.BilinForm.isSkewAdjoint_bracket_of_isSelfAdjoint
      (isSelfAdjoint_of_mem_compatibleTangentSpace hY)
      (isSelfAdjoint_of_mem_compatibleTangentSpace hZ))

end SymplecticForm

end TauCeti

end
