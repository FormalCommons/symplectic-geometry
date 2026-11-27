/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The restriction of a two-form to a distribution

A smooth distribution `D` of rank `k` on `M` is a smooth vector bundle with fibre `Fin k → ℝ`
(Tau Ceti's `TauCeti.IsContMDiffDistribution.fiberBundle`, `vectorBundle` and
`contMDiffVectorBundle`). A smooth two-form `τ` on `M` restricts to a smooth two-form on this
bundle, `(u, v) ↦ τ(u, v)` for `u, v ∈ D x`.

## Main definitions

* `TauCeti.IsContMDiffDistribution.restrictTwoForm hD`: the linear map that restricts a smooth
  two-form on `M` to the smooth distribution `D`, as a smooth two-form on the vector bundle `D`.

## Main results

* `TauCeti.IsContMDiffDistribution.bilinFormAt_restrictTwoForm`: at `x`, the restricted form is
  the restriction of `τ_x` to `D x`.
* `TauCeti.IsContMDiffDistribution.isNondegenerate_restrictTwoForm_iff`: the restricted form is
  nondegenerate exactly when `τ_x` is nondegenerate on `D x` at every point.
* `TauCeti.IsContMDiffDistribution.restrictTwoForm_eq_iff`: two forms have the same restriction
  exactly when they agree on pairs of vectors of `D`.

## Implementation notes

The restriction is the pull-back of `τ`, read as a two-form on the tangent bundle by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv`, along Tau Ceti's smooth family of
inclusions `TauCeti.IsContMDiffDistribution.inclusionHom`, by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.compContinuousLinearMap`. The bundle structure of `D`
is the one that `hD` gives, used as local instances.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.IsContMDiffDistribution

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {k : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace IM x)}
  (hD : IsContMDiffDistribution IM ∞ k D)

/-- **The restriction of two-forms to a distribution.** For a smooth distribution `D` of rank
`k`, the linear map that sends a smooth two-form `τ` on `M` to the smooth two-form
`(u, v) ↦ τ_x(u, v)`, `u, v ∈ D x`, on the vector bundle `D` with the smooth structure of `hD`. -/
def restrictTwoForm : letI := hD.fiberBundle; letI := hD.vectorBundle
    SmoothTwoForm IM M →ₗ[ℝ]
      SymplecticGeometry.Bundle.ContMDiffTwoForm IM ⊤ (Fin k → ℝ) (fun x ↦ D x) :=
  letI := hD.fiberBundle; letI := hD.vectorBundle
  (SymplecticGeometry.Bundle.ContMDiffTwoForm.compContinuousLinearMap (fun x ↦ hD.inclusionHom x)
    hD.inclusionHom.contMDiff).comp
    (SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv (I := IM) (M := M)).symm.toLinearMap

/-- The restriction of `τ` to `D` takes on vectors of `D x` the value of `τ` on them. -/
@[simp]
theorem restrictTwoForm_apply (τ : SmoothTwoForm IM M) (x : M) (v : Fin 2 → D x) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    hD.restrictTwoForm τ x v = τ.val x (Subtype.val ∘ v) := by
  let := hD.fiberBundle; let := hD.vectorBundle
  simp only [restrictTwoForm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    SymplecticGeometry.Bundle.ContMDiffTwoForm.compContinuousLinearMap_apply,
    SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv_symm_apply, inclusionHom_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Submodule.coe_subtypeL,
    Submodule.coe_subtype]

/-- At each point `x`, the restriction of `τ` to `D` is the restriction of the bilinear form of
`τ` at `x` to `D x`. -/
@[simp]
theorem bilinFormAt_restrictTwoForm (τ : SmoothTwoForm IM M) (x : M) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).bilinFormAt x = (τ.bilinFormAt x).restrict (D x) := by
  let := hD.fiberBundle; let := hD.vectorBundle
  ext u v
  simp only [restrictTwoForm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    SymplecticGeometry.Bundle.ContMDiffTwoForm.bilinFormAt_compContinuousLinearMap,
    SymplecticGeometry.Bundle.ContMDiffTwoForm.bilinFormAt_tangentEquiv_symm, inclusionHom_apply,
    LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, Submodule.subtypeL_apply]

/-- The restriction of `τ` to `D` is nondegenerate exactly when, at every point `x`, the
bilinear form of `τ` at `x` is nondegenerate on `D x`. -/
theorem isNondegenerate_restrictTwoForm_iff {τ : SmoothTwoForm IM M} :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).IsNondegenerate ↔
      ∀ x, ((τ.bilinFormAt x).restrict (D x)).Nondegenerate := by
  let := hD.fiberBundle; let := hD.vectorBundle
  simp only [SymplecticGeometry.Bundle.ContMDiffTwoForm.isNondegenerate_def,
    bilinFormAt_restrictTwoForm]

/-- Two two-forms have the same restriction to `D` exactly when they agree on every pair of
vectors of `D`. -/
theorem restrictTwoForm_eq_iff {τ τ' : SmoothTwoForm IM M} :
    hD.restrictTwoForm τ = hD.restrictTwoForm τ' ↔
      ∀ x, ∀ u ∈ D x, ∀ v ∈ D x, τ.bilinFormAt x u v = τ'.bilinFormAt x u v := by
  let := hD.fiberBundle; let := hD.vectorBundle
  refine ⟨fun h x u hu v hv ↦ ?_, fun h ↦ ?_⟩
  · have := congr(SymplecticGeometry.Bundle.ContMDiffTwoForm.bilinFormAt $h x ⟨u, hu⟩ ⟨v, hv⟩)
    simpa only [bilinFormAt_restrictTwoForm, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply] using this
  · refine SymplecticGeometry.Bundle.ContMDiffTwoForm.ext_bilinFormAt fun x ↦ ?_
    rw [bilinFormAt_restrictTwoForm, bilinFormAt_restrictTwoForm]
    ext u v
    simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using
      h x u u.property v v.property

end TauCeti.IsContMDiffDistribution

end
