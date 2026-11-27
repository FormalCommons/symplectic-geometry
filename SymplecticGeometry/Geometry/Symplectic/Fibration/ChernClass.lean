/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Basic
public import SymplecticGeometry.Geometry.Manifold.Distribution.TwoForm
import SymplecticGeometry.Geometry.Manifold.FiberBundle.MapFiber

/-!
# The vertical restriction of a two-form

For a map `proj : M → B` with a smooth atlas, the kernels of the derivative of `proj` form a smooth
distribution, the vertical bundle of `proj`
(`TauCeti.MapFiber.Atlas.IsContMDiff.isContMDiffDistribution_ker_mfderiv`), and a smooth two-form
on `M` restricts to it (`TauCeti.IsContMDiffDistribution.restrictTwoForm`). The restriction of a
vertically nondegenerate form to it is nondegenerate, a symplectic structure on the vertical
bundle, and two forms that restrict to the same form on the fibre along the atlas have the same
vertical restriction.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_restrictTwoForm_ker_iff`: the vertical restriction of
  `τ` is nondegenerate exactly when `τ` is vertically nondegenerate; so a form that restricts to a
  nondegenerate form along a smooth atlas has a nondegenerate vertical restriction
  (`TauCeti.MapFiber.Atlas.RestrictsTo.isNondegenerate_restrictTwoForm`).
* `TauCeti.MapFiber.Atlas.RestrictsTo.restrictTwoForm_eq`: two forms that restrict to the same
  form along a smooth atlas have the same vertical restriction.

## Implementation notes

The vertical bundle is taken as any smooth distribution `hD` whose spaces are the kernels of the
derivative of `proj`, with the bundle structure that `hD` gives, used as local instances. Since
this structure depends only on a proof, any two proofs that the vertical spaces form a smooth
distribution give the same bundle.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 and §6.3.
-/

public section

noncomputable section

open scoped Manifold ContDiff

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
