/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Basic facts about continuous linear equivalences

General lemmas about `ContinuousLinearEquiv` that Mathlib does not state at the pinned version,
kept in its namespace so that they can move upstream unchanged.

## Main results

* `ContinuousLinearEquiv.toLinearEquiv_refl`: the underlying linear equivalence of the identity
  is the identity, as Mathlib states for `LinearIsometryEquiv.toLinearEquiv_refl`.
* `ContinuousLinearEquiv.smulLeft_symm`, `ContinuousLinearEquiv.smulLeft_symm_apply`: the inverse
  of scalar multiplication by a group element `g` is scalar multiplication by `g⁻¹`.
* `ContinuousLinearEquiv.coe_smulLeft`: as a continuous linear map, scalar multiplication by a
  unit `c` is `c` times the identity.
* `ContinuousLinearEquiv.coe_toUnit`, `ContinuousLinearEquiv.coe_toUnit_inv`,
  `ContinuousLinearEquiv.unitsEquiv_symm_apply`: the unit of the ring of continuous endomorphisms
  given by an automorphism `e` is `e`, with inverse `e.symm`, and it is the image of `e` under the
  inverse of `ContinuousLinearEquiv.unitsEquiv`.
-/

public section

namespace ContinuousLinearEquiv

section Refl

variable (R : Type*) [Semiring R] (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  [Module R M]

/-- The linear equivalence underlying the identity continuous linear equivalence is
`LinearEquiv.refl`. -/
@[simp]
theorem toLinearEquiv_refl :
    (ContinuousLinearEquiv.refl R M).toLinearEquiv = LinearEquiv.refl R M :=
  rfl

end Refl

section DistribMulAction

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {G : Type*} [Group G] [DistribMulAction G M] [ContinuousConstSMul G M] [SMulCommClass G R M]

/-- The inverse of scalar multiplication by a group element `g` is scalar multiplication by
`g⁻¹`. -/
@[simp]
theorem smulLeft_symm_apply (g : G) (x : M) :
    (smulLeft g : M ≃L[R] M).symm x = g⁻¹ • x :=
  (smulLeft g).symm_apply_eq.2 (by simp)

/-- The inverse of scalar multiplication by a group element `g` is scalar multiplication by
`g⁻¹`, as continuous linear equivalences. -/
theorem smulLeft_symm (g : G) : (smulLeft g : M ≃L[R] M).symm = smulLeft g⁻¹ :=
  ext <| funext fun x ↦ by rw [smulLeft_symm_apply, smulLeft_apply_apply]

end DistribMulAction

section Units

variable {R : Type*} [CommSemiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
  [Module R M] [ContinuousConstSMul R M]

/-- Scalar multiplication by a unit `c` of `R`, as a continuous linear map, is `c` times the
identity map. -/
theorem coe_smulLeft (c : Rˣ) :
    ((smulLeft c : M ≃L[R] M) : M →L[R] M) = (c : R) • ContinuousLinearMap.id R M :=
  ContinuousLinearMap.ext fun x ↦ by
    rw [coe_coe, smulLeft_apply_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, Units.smul_def]

end Units

section Aut

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- The unit of the ring of continuous endomorphisms given by an automorphism `e` is `e`. -/
@[simp]
theorem coe_toUnit (e : M ≃L[R] M) : (e.toUnit : M →L[R] M) = e :=
  rfl

/-- The inverse of the unit given by an automorphism `e` is `e.symm`. -/
@[simp]
theorem coe_toUnit_inv (e : M ≃L[R] M) : ((e.toUnit⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) = e.symm :=
  rfl

variable (R M) in
/-- The inverse of `ContinuousLinearEquiv.unitsEquiv` sends an automorphism to the unit of the
ring of continuous endomorphisms that it gives. -/
@[simp]
theorem unitsEquiv_symm_apply (e : M ≃L[R] M) : (unitsEquiv R M).symm e = e.toUnit :=
  rfl

end Aut

end ContinuousLinearEquiv

end
