/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import SymplecticGeometry.LinearAlgebra.BilinearForm.Nondegenerate
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Vertically nondegenerate two-forms

A two-form `τ` on `M` is *vertically nondegenerate* for a map `proj : M → B` when it is
nondegenerate on the kernel of the derivative of `proj` at every point. For a trivialization that
is differentiable with differentiable inverse, with `M` finite-dimensional, that kernel is the
image of the tangent space of the fibre, so a form that restricts to a nondegenerate `σ` along a
smooth atlas is vertically nondegenerate, and a vertically nondegenerate form pulls back to a
nondegenerate form along every fibre inclusion of a smooth trivialization.

## Main definitions

* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate IB proj τ`: the form `τ` is nondegenerate on
  the kernel of the derivative of `proj` at every point.

## Main results

* `Bundle.Trivialization.nondegenerate_restrict_ker_mfderiv_iff_separatingLeft`: at a point of a
  fibre of a differentiable trivialization, a two-form is nondegenerate on the kernel of the
  derivative of `proj` exactly when its pull-back to the fibre is nondegenerate there.
* `TauCeti.MapFiber.Atlas.RestrictsTo.isVerticallyNondegenerate`: along a smooth atlas, a form
  that restricts to a nondegenerate form is vertically nondegenerate.
* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusionMap`:
  a vertically nondegenerate form pulls back to a nondegenerate form along the fibre inclusions of
  a smooth trivialization.

## Implementation notes

The results identify the kernel of the derivative of `proj` with the image of the derivative of a
fibre inclusion by `Bundle.Trivialization.range_mfderiv_fiberInclusionMap`, and so assume that
`M` is finite-dimensional.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1.
-/

public section

open Bundle Function Set
open scoped Manifold ContDiff

namespace Bundle.Trivialization

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B}

/-- **Two-forms on the tangent spaces of a fibre.** Let `e` be a trivialization of `proj` that is
differentiable with differentiable inverse, `M` being finite-dimensional. A two-form `τ` on `M` is
nondegenerate on the kernel of the derivative of `proj` at the point `e.fiberInclusionMap hb v`
exactly when its pull-back along the fibre inclusion of `e` over `b` is nondegenerate at `v`. -/
theorem nondegenerate_restrict_ker_mfderiv_iff_separatingLeft [IsManifold IF ∞ F]
    [IsManifold IM ∞ M] [FiniteDimensional ℝ EM] {e : Trivialization F proj}
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) {b : B}
    (hb : b ∈ e.baseSet) (hι : ContMDiff IF IM ∞ (e.fiberInclusionMap hb))
    (τ : TauCeti.SmoothTwoForm IM M) (v : F) :
    ((τ.bilinFormAt (e.fiberInclusionMap hb v)).restrict
        (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker).Nondegenerate ↔
      ((TauCeti.SmoothForm.mpullback (e.fiberInclusionMap hb) hι τ).bilinFormAt
        v).SeparatingLeft := by
  have hrange := e.range_mfderiv_fiberInclusionMap he hb v
  have hpull : ∀ u w,
      (TauCeti.SmoothForm.mpullback (e.fiberInclusionMap hb) hι τ).bilinFormAt v u w =
        τ.bilinFormAt _ (mfderiv IF IM (e.fiberInclusionMap hb) v u)
          (mfderiv IF IM (e.fiberInclusionMap hb) v w) := fun u w ↦ by
    rw [TauCeti.SmoothForm.bilinFormAt_apply, TauCeti.SmoothForm.eval₂_mpullback,
      TauCeti.SmoothForm.bilinFormAt_apply]
  have hrefl : ((τ.bilinFormAt (e.fiberInclusionMap hb v)).restrict
      (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker).IsRefl :=
    (TauCeti.SmoothForm.isAlt_bilinFormAt τ _).isRefl.domRestrict _
  let i := (LinearEquiv.ofInjective _ (e.injective_mfderiv_fiberInclusionMap he hb v)).trans
    (LinearEquiv.ofEq _ _ hrange)
  refine hrefl.nondegenerate_iff_separatingLeft.trans ?_
  rw [← LinearMap.separatingLeft_congr_iff i.symm i.symm]
  convert Iff.rfl
  ext u w
  simp [i, hpull]

end Bundle.Trivialization

/-! ### Vertically nondegenerate two-forms -/

namespace TauCeti.SmoothTwoForm

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold IM ∞ M]
  {proj : M → B} {τ : SmoothTwoForm IM M}

/-- A two-form `τ` on `M` is *vertically nondegenerate* for a map `proj : M → B` when, at every
point `x`, its restriction to the vertical space, the kernel of the derivative of `proj` at `x`,
is nondegenerate. For a map with a smooth atlas and a finite-dimensional `M`, it implies
that `τ` pulls back to a nondegenerate form on every fibre. -/
def IsVerticallyNondegenerate (proj : M → B) (τ : SmoothTwoForm IM M) : Prop :=
  ∀ x, ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).Nondegenerate

variable {IB}

theorem isVerticallyNondegenerate_iff :
    IsVerticallyNondegenerate IB proj τ ↔
      ∀ x, ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).Nondegenerate :=
  Iff.rfl

/-- Vertical nondegeneracy in terms of vectors: a vertical vector on which `τ` pairs to zero with
every vertical vector is zero. One side suffices, since `τ` is alternating. -/
theorem isVerticallyNondegenerate_iff_forall :
    IsVerticallyNondegenerate IB proj τ ↔
      ∀ x, ∀ u ∈ (mfderiv IM IB proj x).ker,
        (∀ w ∈ (mfderiv IM IB proj x).ker, τ.bilinFormAt x u w = 0) → u = 0 :=
  forall_congr' fun x ↦ (SmoothForm.isAlt_bilinFormAt τ x).isRefl.nondegenerate_restrict_iff

/-- **The fibres of a vertically nondegenerate form.** Let `e` be a trivialization of `proj`
that is smooth with smooth inverse, `M` being finite-dimensional. If `τ` is vertically
nondegenerate, then its pull-back along each fibre inclusion of `e` is a nondegenerate form on the
model fibre. -/
theorem IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusionMap
    [FiniteDimensional ℝ EM] (hτ : IsVerticallyNondegenerate IB proj τ)
    {e : Trivialization F proj} (he : ContMDiffOn IM (IB.prod IF) ∞ e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM ∞ e.toOpenPartialHomeomorph.symm e.target) {b : B}
    (hb : b ∈ e.baseSet) :
    IsNondegenerate
      (SmoothForm.mpullback (e.fiberInclusionMap hb)
        (e.contMDiff_fiberInclusionMap he_symm hb) τ) := by
  have hd : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF) :=
    ⟨he.mdifferentiableOn (by simp), he_symm.mdifferentiableOn (by simp)⟩
  rw [isNondegenerate_iff_separatingLeft]
  intro v u hu
  exact (e.nondegenerate_restrict_ker_mfderiv_iff_separatingLeft hd hb _ τ v).1
    (isVerticallyNondegenerate_iff.1 hτ _) u
    fun w ↦ by rw [SmoothForm.bilinFormAt_apply]; exact hu w

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
  {proj : M → B} {A : Atlas F proj} {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}

/-- **Restricting forms are vertically nondegenerate.** If a two-form `τ` restricts to a
nondegenerate form `σ` along a smooth atlas of `proj`, with `M` finite-dimensional, then
`τ` is vertically nondegenerate: the vertical space at each point is the image of the tangent
space of the fibre. -/
theorem RestrictsTo.isVerticallyNondegenerate [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ) :
    SmoothTwoForm.IsVerticallyNondegenerate IB proj τ := by
  refine SmoothTwoForm.isVerticallyNondegenerate_iff.2 fun x ↦ ?_
  have hb := A.mem_baseSet_trivAt (proj x)
  have hx : (A.trivAt (proj x)).fiberInclusionMap hb (A.trivAt (proj x) x).2 = x := by
    rw [Trivialization.fiberInclusionMap_apply,
      (A.trivAt (proj x)).symm_apply_mk_proj ((A.trivAt (proj x)).mem_source.2 hb)]
  have hι := (A.trivAt (proj x)).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm _) hb
  have hpull : SmoothForm.mpullback _ hι τ = σ :=
    Subtype.ext ((SmoothForm.coe_mpullback _ hι τ).trans (restrictsTo_iff.1 hτ _ _ hb))
  refine hx ▸ ((A.trivAt (proj x)).nondegenerate_restrict_ker_mfderiv_iff_separatingLeft
    (hA.mdifferentiable_trivAt (by simp) _) hb hι τ _).2 ?_
  rw [hpull]
  exact fun u hu ↦ SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ _ u
    fun w ↦ by rw [← SmoothForm.bilinFormAt_apply]; exact hu w

end TauCeti.MapFiber.Atlas

end
