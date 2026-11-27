/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Basic
public import TauCeti.Geometry.Manifold.Distribution.Submersion
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber

/-!
# The vertical bundle of a fibration and the vertical restriction of a two-form

A smooth distribution `D` of rank `k` on `M` is a smooth vector bundle with fibre `Fin k → ℝ`
(Tau Ceti's `TauCeti.IsContMDiffDistribution.fiberBundle`, `vectorBundle` and
`contMDiffVectorBundle`). A smooth two-form `τ` on `M` restricts to a smooth two-form on this
bundle, `(u, v) ↦ τ(u, v)` for `u, v ∈ D x`.

For a map `proj : M → B` with a smooth atlas, the kernels of the derivative of `proj` form such a
distribution, the vertical bundle of `proj`. The restriction of a vertically nondegenerate form to
it is nondegenerate, a symplectic structure on the vertical bundle, and two forms that restrict to
the same form on the fibre along the atlas have the same vertical restriction.

## Main definitions

* `TauCeti.IsContMDiffDistribution.restrictTwoForm hD`: the linear map that restricts a smooth
  two-form on `M` to the smooth distribution `D`, as a smooth two-form on the vector bundle `D`.

## Main results

* `TauCeti.IsContMDiffDistribution.bilinFormAt_restrictTwoForm`: at `x`, the restricted form is
  the restriction of `τ_x` to `D x`.
* `TauCeti.IsContMDiffDistribution.isNondegenerate_restrictTwoForm_iff`: the restricted form is
  nondegenerate exactly when `τ_x` is nondegenerate on `D x` at every point.
* `TauCeti.MapFiber.Atlas.IsContMDiff.isContMDiffDistribution_ker_mfderiv` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiffVectorBundle_ker_mfderiv`: for a smooth atlas, the
  vertical spaces form a smooth vector bundle of rank `dim M - dim B`.
* `TauCeti.SmoothTwoForm.isNondegenerate_restrictTwoForm_ker_iff`: the vertical restriction of
  `τ` is nondegenerate exactly when `τ` is vertically nondegenerate; so a form that restricts to a
  nondegenerate form along a smooth atlas has a nondegenerate vertical restriction
  (`TauCeti.MapFiber.Atlas.RestrictsTo.isNondegenerate_restrictTwoForm`).
* `TauCeti.MapFiber.Atlas.RestrictsTo.restrictTwoForm_eq`: two forms that restrict to the same
  form along a smooth atlas have the same vertical restriction.

## Implementation notes

The restriction is the pull-back of `τ`, read as a two-form on the tangent bundle by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.tangentEquiv`, along Tau Ceti's smooth family of
inclusions `TauCeti.IsContMDiffDistribution.inclusionHom`, by
`SymplecticGeometry.Bundle.ContMDiffTwoForm.compContinuousLinearMap`. The vertical bundle is the
kernel distribution of the submersion `proj`
(`TauCeti.MapFiber.Atlas.IsContMDiff.isSubmersion` and Tau Ceti's
`Manifold.IsSubmersion.isContMDiffDistribution_ker_mfderiv`); it is not built again from local
frames. Its bundle structure is the one that the distribution gives, used as local instances, and
since it depends only on a proof, any two proofs that the vertical spaces form a smooth
distribution give the same bundle.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 and §6.3.
-/

public section

noncomputable section

open Module
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
  have : IsManifold IM (∞ + 1) M := by simpa using (inferInstance : IsManifold IM ∞ M)
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

/-! ### The vertical bundle of a smooth atlas -/

namespace TauCeti.MapFiber.Atlas.IsContMDiff

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [IM.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj}

/-- **The vertical distribution of a smooth atlas.** If `proj : M → B` has a smooth atlas, with
`M` boundaryless and both models finite-dimensional, then the vertical spaces, the kernels of
the derivative of `proj`, form a smooth distribution of rank `dim M - dim B`. -/
theorem isContMDiffDistribution_ker_mfderiv (hA : A.IsContMDiff ∞ IB IF IM) :
    IsContMDiffDistribution IM ∞ (finrank ℝ EM - finrank ℝ EB)
      fun x ↦ (mfderiv IM IB proj x).ker :=
  (hA.isSubmersion (by simp)).isContMDiffDistribution_ker_mfderiv (by simp)

/-- **The vertical bundle of a smooth atlas.** With the bundle structure of
`isContMDiffDistribution_ker_mfderiv`, the vertical spaces of a map with a smooth atlas form a
smooth vector bundle with fibre `Fin (dim M - dim B) → ℝ`. -/
theorem contMDiffVectorBundle_ker_mfderiv (hA : A.IsContMDiff ∞ IB IF IM) :
    letI := hA.isContMDiffDistribution_ker_mfderiv.fiberBundle
    letI := hA.isContMDiffDistribution_ker_mfderiv.vectorBundle
    ContMDiffVectorBundle ∞ (Fin (finrank ℝ EM - finrank ℝ EB) → ℝ)
      (fun x ↦ (mfderiv IM IB proj x).ker) IM :=
  have : IsManifold IM (∞ + 1) M := by simpa using (inferInstance : IsManifold IM ∞ M)
  hA.isContMDiffDistribution_ker_mfderiv.contMDiffVectorBundle

end TauCeti.MapFiber.Atlas.IsContMDiff

/-! ### The vertical restriction of a two-form -/

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M] {proj : M → B} {k : ℕ}

/-- **Nondegeneracy of the vertical restriction.** The restriction of a two-form `τ` to the
vertical bundle of `proj` is nondegenerate exactly when `τ` is vertically nondegenerate. -/
theorem isNondegenerate_restrictTwoForm_ker_iff {τ : SmoothTwoForm IM M}
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).IsNondegenerate ↔ IsVerticallyNondegenerate IB proj τ :=
  hD.isNondegenerate_restrictTwoForm_iff.trans isVerticallyNondegenerate_iff.symm

end TauCeti.SmoothTwoForm

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ τ' : SmoothTwoForm IM M} {k : ℕ}

/-- **The vertical restriction is nondegenerate.** If `τ` restricts to a nondegenerate form `σ`
along a smooth atlas of `proj`, then its restriction to the vertical bundle of `proj` is
nondegenerate. -/
theorem RestrictsTo.isNondegenerate_restrictTwoForm (hA : A.IsContMDiff ∞ IB IF IM)
    (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ)
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    letI := hD.fiberBundle; letI := hD.vectorBundle
    (hD.restrictTwoForm τ).IsNondegenerate :=
  (SmoothTwoForm.isNondegenerate_restrictTwoForm_ker_iff hD).2
    (hτ.isVerticallyNondegenerate hA hσ)

/-- **The vertical restriction does not depend on the form.** Two two-forms that restrict to the
same form `σ` along a smooth atlas of `proj` have the same restriction to the vertical bundle of
`proj`: the vertical space at each point is the image of the tangent space of the fibre. -/
theorem RestrictsTo.restrictTwoForm_eq (hA : A.IsContMDiff ∞ IB IF IM) (hτ : A.RestrictsTo σ τ)
    (hτ' : A.RestrictsTo σ τ')
    (hD : IsContMDiffDistribution IM ∞ k fun x ↦ (mfderiv IM IB proj x).ker) :
    hD.restrictTwoForm τ = hD.restrictTwoForm τ' := by
  refine hD.restrictTwoForm_eq_iff.2 fun x u hu v hv ↦ ?_
  have hb := A.mem_baseSet_trivAt (proj x)
  have h := (A.trivAt (proj x)).apply_eq_of_mpullback_fiberInclusionMap_eq
    (hA.mdifferentiable_trivAt (by simp) _) hb
    ((restrictsTo_iff.1 hτ _ _ hb).trans (restrictsTo_iff.1 hτ' _ _ hb).symm)
    (u := ![u, v]) fun i ↦ by fin_cases i <;> assumption
  simpa [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply] using h

end TauCeti.MapFiber.Atlas

end
