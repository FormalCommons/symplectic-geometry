/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The differential of the inverse of a partial diffeomorphism

At a point `y` of the target of a partial diffeomorphism `Φ`, the differential of `Φ.symm` at `y`
and that of `Φ` at `Φ.symm y` are mutually inverse (Tau Ceti's
`PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply` and
`PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`), so together they form one continuous
linear equivalence.

For a partial diffeomorphism `Φ` into a normed space `E` and a chart of a manifold modelled on
`E`, the transitions between them, in both directions, are smooth with derivatives of nonzero
determinant on their sources. Smoothness is Tau Ceti's
`OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn`, and the determinants are Tau
Ceti's `TauCeti.det_fderiv_symm_trans_ne_zero`, since `Φ` lies in the maximal atlas of the
manifold.

## Main definitions

* `PartialDiffeomorph.mfderivSymmEquiv`: the differential of `Φ.symm` at a point `y` of the target,
  as a continuous linear equivalence whose inverse is the differential of `Φ` at `Φ.symm y`.

## Main results

* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_target`: for `y` in the target of
  `Φ`, `d(Φ⁻¹)_y ∘ dΦ_{Φ⁻¹ y}` is the identity.
* `PartialDiffeomorph.contDiffOn_symm_trans_chartAt`,
  `PartialDiffeomorph.contDiffOn_chartAt_symm_trans`,
  `PartialDiffeomorph.det_fderiv_symm_trans_chartAt_ne_zero` and
  `PartialDiffeomorph.det_fderiv_chartAt_symm_trans_ne_zero`: the transitions between `Φ` and a
  chart are smooth, with derivatives of nonzero determinant.
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

section ChartTransition

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] {n : WithTop ℕ∞}
  [IsManifold 𝓘(𝕜, E) n M']

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E` and `x : M'`, the transition
`chartAt E x ∘ Φ⁻¹` is `C^n` on its source. -/
theorem contDiffOn_symm_trans_chartAt (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (x : M') :
    ContDiffOn 𝕜 n (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x)
      (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source :=
  OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn contMDiffOn_chart
    Φ.symm.contMDiffOn

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E` and `x : M'`, the transition
`Φ ∘ (chartAt E x)⁻¹` is `C^n` on its source. -/
theorem contDiffOn_chartAt_symm_trans (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (x : M') :
    ContDiffOn 𝕜 n ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph)
      ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source :=
  OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn
    Φ.contMDiffOn (contMDiffOn_chart_symm (x := x))

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E`, `n ≠ 0`, and `x : M'`, the
derivative of the transition `chartAt E x ∘ Φ⁻¹` has nonzero determinant on its source. -/
theorem det_fderiv_symm_trans_chartAt_ne_zero
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (hn : n ≠ 0) (x : M') {z : E}
    (hz : z ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source) :
    (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x) z).det ≠ 0 :=
  TauCeti.det_fderiv_symm_trans_ne_zero hn
    (Φ.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Φ.contMDiffOn Φ.symm.contMDiffOn)
    (IsManifold.chart_mem_maximalAtlas x) hz

/-- For a `C^n` partial diffeomorphism `Φ` from `M'` into `E`, `n ≠ 0`, and `x : M'`, the
derivative of the transition `Φ ∘ (chartAt E x)⁻¹` has nonzero determinant on its source. -/
theorem det_fderiv_chartAt_symm_trans_ne_zero
    (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n) (hn : n ≠ 0) (x : M') {z : E}
    (hz : z ∈ ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source) :
    (fderiv 𝕜 ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph) z).det ≠ 0 :=
  TauCeti.det_fderiv_symm_trans_ne_zero hn (IsManifold.chart_mem_maximalAtlas x)
    (Φ.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Φ.contMDiffOn Φ.symm.contMDiffOn)
    hz

end ChartTransition

end PartialDiffeomorph
