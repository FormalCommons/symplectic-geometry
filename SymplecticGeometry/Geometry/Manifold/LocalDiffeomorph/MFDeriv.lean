/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The differential of the inverse of a partial diffeomorphism

At a point `y` of the target of a partial diffeomorphism `Φ`, the differential of `Φ.symm` at `y`
and that of `Φ` at `Φ.symm y` are mutually inverse (Tau Ceti's
`PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply` and
`PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`), so together they form one continuous
linear equivalence.

## Main definitions

* `PartialDiffeomorph.mfderivSymmEquiv`: the differential of `Φ.symm` at a point `y` of the target,
  as a continuous linear equivalence whose inverse is the differential of `Φ` at `Φ.symm y`.

## Main results

* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_target`: for `y` in the target of
  `Φ`, `d(Φ⁻¹)_y ∘ dΦ_{Φ⁻¹ y}` is the identity.
-/

public section

open scoped Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

section MFDerivSymmEquiv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- At a point `y` of the target of a partial diffeomorphism `Φ` of nonzero regularity, the
differential of `Φ.symm` at `y` undoes the differential of `Φ` at `Φ.symm y`. -/
theorem mfderiv_symm_apply_mfderiv_apply_of_mem_target (Φ : PartialDiffeomorph I J M N n)
    (hn : n ≠ 0) {y : N} (hy : y ∈ Φ.target) (v : TangentSpace I (Φ.symm y)) :
    mfderiv J I Φ.symm y (mfderiv I J Φ (Φ.symm y) v) = v := by
  have h := Φ.mfderiv_symm_apply_mfderiv_apply hn (Φ.map_target hy) v
  rwa [Φ.right_inv hy] at h

/-- For a point `y` of the target of a partial diffeomorphism `Φ` of nonzero regularity, the
differential of `Φ.symm` at `y`, as a continuous linear equivalence from the tangent space at `y`
to the tangent space at `Φ.symm y`. Its inverse is the differential of `Φ` at `Φ.symm y`
(`PartialDiffeomorph.coe_mfderivSymmEquiv_symm`). -/
noncomputable def mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : TangentSpace J y ≃L[𝕜] TangentSpace I (Φ.symm y) :=
  .ofContinuousLinearMap (mfderiv J I Φ.symm y) (mfderiv I J Φ (Φ.symm y))
    (ContinuousLinearMap.ext (Φ.mfderiv_symm_apply_mfderiv_apply_of_mem_target hn hy))
    (ContinuousLinearMap.ext (Φ.mfderiv_apply_mfderiv_symm_apply hn hy))

@[simp]
theorem coe_mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : ⇑(Φ.mfderivSymmEquiv hn hy) = mfderiv J I Φ.symm y :=
  (rfl)

@[simp]
theorem coe_mfderivSymmEquiv_symm (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {y : N}
    (hy : y ∈ Φ.target) : ⇑(Φ.mfderivSymmEquiv hn hy).symm = mfderiv I J Φ (Φ.symm y) :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_mfderivSymmEquiv (Φ : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    {y : N} (hy : y ∈ Φ.target) :
    (Φ.mfderivSymmEquiv hn hy : TangentSpace J y →L[𝕜] TangentSpace I (Φ.symm y)) =
      mfderiv J I Φ.symm y :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_mfderivSymmEquiv_symm (Φ : PartialDiffeomorph I J M N n)
    (hn : n ≠ 0) {y : N} (hy : y ∈ Φ.target) :
    ((Φ.mfderivSymmEquiv hn hy).symm : TangentSpace I (Φ.symm y) →L[𝕜] TangentSpace J y) =
      mfderiv I J Φ (Φ.symm y) :=
  (rfl)

end MFDerivSymmEquiv

end PartialDiffeomorph
