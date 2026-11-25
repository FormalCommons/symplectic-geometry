/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The differential of the inverse of a partial diffeomorphism

At a point `y` of the target of a partial diffeomorphism `Φ`, the differential of `Φ.symm` at `y`
and that of `Φ` at `Φ.symm y` are mutually inverse (Tau Ceti's
`PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply` and
`PartialDiffeomorph.mfderiv_apply_mfderiv_symm_apply`), so together they form one continuous
linear equivalence.

For a partial diffeomorphism `Φ` into a normed space `E` and a chart of a manifold modelled on
`E`, the transitions between them, in both directions, are smooth with derivatives of nonzero
determinant on their sources. They are Tau Ceti's
`OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn` and
`OpenPartialHomeomorph.det_fderiv_ne_zero_of_contDiffOn` applied to `Φ` and the chart.

## Main definitions

* `PartialDiffeomorph.mfderivSymmEquiv`: the differential of `Φ.symm` at a point `y` of the target,
  as a continuous linear equivalence whose inverse is the differential of `Φ` at `Φ.symm y`.

## Main results

* `PartialDiffeomorph.mfderiv_symm_apply_mfderiv_apply_of_mem_target`: for `y` in the target of
  `Φ`, `d(Φ⁻¹)_y ∘ dΦ_{Φ⁻¹ y}` is the identity.
* `PartialDiffeomorph.isOpen_inter_preimage_symm`: `Φ.target ∩ Φ.symm ⁻¹' s` is open for `s` open.
* `PartialDiffeomorph.contDiffOn_symm_trans_chartAt`: the transitions between `Φ` and a chart are
  smooth, with derivatives of nonzero determinant.
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

/-- The preimage under `Φ.symm` of an open set, within the target of a partial diffeomorphism `Φ`,
is open. -/
theorem isOpen_inter_preimage_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] (Φ : PartialDiffeomorph I J M N n)
    {s : Set M} (hs : IsOpen s) : IsOpen (Φ.target ∩ Φ.symm ⁻¹' s) :=
  Φ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage Φ.open_target hs

section ChartTransition

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] {n : WithTop ℕ∞}
  [IsManifold 𝓘(𝕜, E) n M']

/-- Let `Φ` be a `C^n` partial diffeomorphism from `M'` into `E`, `n ≠ 0`, and `x : M'`. The
transition `chartAt E x ∘ Φ⁻¹` is `C^n` on its source, with derivative of nonzero determinant
there, and so is the transition `Φ ∘ (chartAt E x)⁻¹` the other way. -/
theorem contDiffOn_symm_trans_chartAt (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' E n)
    (hn : n ≠ 0) (x : M') :
    (ContDiffOn 𝕜 n (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x)
        (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source ∧
      ∀ z ∈ (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x).source,
        (fderiv 𝕜 (Φ.toOpenPartialHomeomorph.symm ≫ₕ chartAt E x) z).det ≠ 0) ∧
    (ContDiffOn 𝕜 n ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph)
        ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source ∧
      ∀ z ∈ ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph).source,
        (fderiv 𝕜 ((chartAt E x).symm ≫ₕ Φ.toOpenPartialHomeomorph) z).det ≠ 0) := by
  have hΦ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n Φ.toOpenPartialHomeomorph
      Φ.toOpenPartialHomeomorph.source := by
    rw [Φ.toFun'_toOpenPartialHomeomorph, Φ.toOpenPartialHomeomorph_source]
    exact Φ.contMDiffOn
  have hΦs : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n Φ.toOpenPartialHomeomorph.symm
      Φ.toOpenPartialHomeomorph.target := by
    rw [Φ.coe_toOpenPartialHomeomorph_symm, Φ.toOpenPartialHomeomorph_target]
    exact Φ.symm.contMDiffOn
  have hT := OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hΦ hΦs
    contMDiffOn_chart (contMDiffOn_chart_symm (x := x))
  have hS := OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn
    contMDiffOn_chart (contMDiffOn_chart_symm (x := x)) hΦ hΦs
  exact ⟨⟨hT.1, fun z hz ↦
    OpenPartialHomeomorph.det_fderiv_ne_zero_of_contDiffOn _ hT.1 hT.2 hn hz⟩,
    hS.1, fun z hz ↦ OpenPartialHomeomorph.det_fderiv_ne_zero_of_contDiffOn _ hS.1 hS.2 hn hz⟩

end ChartTransition

end PartialDiffeomorph
