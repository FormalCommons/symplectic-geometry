/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.FiberBundle.RestrictsTo
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Vertically nondegenerate two-forms and forms compatible with an oriented atlas

A two-form `τ` on `M` is *vertically nondegenerate* for a map `proj : M → B` when it is
nondegenerate on the kernel of the derivative of `proj` at every point. For a trivialization that
is differentiable with differentiable inverse, with `M` finite-dimensional, that kernel is the
image of the tangent space of the fibre, so a form that restricts to a nondegenerate `σ` along a
smooth atlas is vertically nondegenerate, and a vertically nondegenerate form pulls back to a
nondegenerate form along every fibre inclusion of a smooth trivialization.

For orientations `oB` of the base and `oF` of the model fibre, a symplectic form on `M` is
compatible with an oriented smooth atlas when it pulls back to a nondegenerate form on every
fibre, with symplectic orientation `oF` there, and every chart carries its symplectic orientation
to the product orientation `oB × oF`.

## Main definitions

* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate IB proj τ`: the form `τ` is nondegenerate on
  the kernel of the derivative of `proj` at every point.
* `TauCeti.MapFiber.Atlas.IsOrientedCompatible hA oB oF τ`: the symplectic form `τ` is compatible
  with the smooth atlas `A` and the orientations `oB` of the base and `oF` of the fibre.

## Main results

* `Bundle.Trivialization.nondegenerate_restrict_ker_mfderiv_iff_separatingLeft`: at a point of a
  fibre of a differentiable trivialization, a two-form is nondegenerate on the kernel of the
  derivative of `proj` exactly when its pull-back to the fibre is nondegenerate there.
* `TauCeti.MapFiber.Atlas.RestrictsTo.isVerticallyNondegenerate`: along a smooth atlas, a form
  that restricts to a nondegenerate form is vertically nondegenerate.
* `TauCeti.SmoothTwoForm.IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusionMap`:
  a vertically nondegenerate form pulls back to a nondegenerate form along the fibre inclusions of
  a smooth trivialization, and conversely
  `TauCeti.MapFiber.Atlas.isVerticallyNondegenerate_of_isNondegenerate_mpullback`.
* `TauCeti.MapFiber.Atlas.IsOrientedCompatible.isVerticallyNondegenerate`: a form compatible with
  an oriented atlas is vertically nondegenerate.

## Implementation notes

The results identify the kernel of the derivative of `proj` with the image of the derivative of a
fibre inclusion by `Bundle.Trivialization.range_mfderiv_fiberInclusionMap`, and so assume that
`M` is finite-dimensional.

The symplectic orientations in `IsOrientedCompatible` are Tau Ceti's
`TauCeti.SmoothTwoForm.IsNondegenerate.orientation`, which may be indexed by `Fin k` for any `k`
equal to the dimension. So the orientation of `M` is indexed by `Fin (m + k)`, as the product
orientation is, and no reindexing is needed. The dimension of `M` is then `m + k` wherever a chart
has a point, and the chart condition gives this equation with the orientations.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1 and Definition 6.2.1.
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
        (∀ w ∈ (mfderiv IM IB proj x).ker, τ.bilinFormAt x u w = 0) → u = 0 := by
  refine forall_congr' fun x ↦ ?_
  have hrefl : ((τ.bilinFormAt x).restrict (mfderiv IM IB proj x).ker).IsRefl :=
    (SmoothForm.isAlt_bilinFormAt τ x).isRefl.domRestrict _
  refine hrefl.nondegenerate_iff_separatingLeft.trans ?_
  exact ⟨fun h u hu hw ↦ congrArg Subtype.val (h ⟨u, hu⟩ fun w ↦ hw w w.property),
    fun h u hu ↦ Subtype.ext (h u u.property fun w hw ↦ hu ⟨w, hw⟩)⟩

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

/-- **Forms with nondegenerate fibres are vertically nondegenerate.** Along a smooth atlas of
`proj`, with `M` finite-dimensional, a two-form `τ` whose pull-back to the fibre over each `b`,
read through the chart `A.trivAt b`, is nondegenerate is vertically nondegenerate. This is the
converse of `IsVerticallyNondegenerate.isNondegenerate_mpullback_fiberInclusionMap`. -/
theorem isVerticallyNondegenerate_of_isNondegenerate_mpullback [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM)
    (hτ : ∀ b, SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback
      ((A.trivAt b).fiberInclusionMap (A.mem_baseSet_trivAt b))
      ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b)
        (A.mem_baseSet_trivAt b)) τ)) :
    SmoothTwoForm.IsVerticallyNondegenerate IB proj τ := by
  refine SmoothTwoForm.isVerticallyNondegenerate_iff.2 fun x ↦ ?_
  have hb := A.mem_baseSet_trivAt (proj x)
  have hx : (A.trivAt (proj x)).fiberInclusionMap hb (A.trivAt (proj x) x).2 = x := by
    rw [Trivialization.fiberInclusionMap_apply,
      (A.trivAt (proj x)).symm_apply_mk_proj ((A.trivAt (proj x)).mem_source.2 hb)]
  refine hx ▸ ((A.trivAt (proj x)).nondegenerate_restrict_ker_mfderiv_iff_separatingLeft
    (hA.mdifferentiable_trivAt (by simp) _) hb
    ((A.trivAt (proj x)).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm _) hb) τ _).2
    fun u hu ↦ SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 (hτ (proj x)) _ u
      fun w ↦ by rw [← SmoothForm.bilinFormAt_apply]; exact hu w

/-- **Restricting forms are vertically nondegenerate.** If a two-form `τ` restricts to a
nondegenerate form `σ` along a smooth atlas of `proj`, with `M` finite-dimensional, then
`τ` is vertically nondegenerate: the vertical space at each point is the image of the tangent
space of the fibre. -/
theorem RestrictsTo.isVerticallyNondegenerate [FiniteDimensional ℝ EM]
    (hA : A.IsContMDiff ∞ IB IF IM) (hσ : σ.IsNondegenerate) (hτ : A.RestrictsTo σ τ) :
    SmoothTwoForm.IsVerticallyNondegenerate IB proj τ := by
  refine isVerticallyNondegenerate_of_isNondegenerate_mpullback hA fun b ↦ ?_
  have hpull : SmoothForm.mpullback _ ((A.trivAt b).contMDiff_fiberInclusionMap
      (hA.contMDiffOn_trivAt_symm b) (A.mem_baseSet_trivAt b)) τ = σ :=
    Subtype.ext ((SmoothForm.coe_mpullback _ _ τ).trans (restrictsTo_iff.1 hτ _ _ _))
  rw [hpull]
  exact hσ

/-! ### Symplectic forms compatible with an oriented atlas -/

section Oriented

variable [IsManifold IB ∞ B] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EF]
  [FiniteDimensional ℝ EM] {m k : ℕ}

/-- A two-form `τ` on `M` is *compatible with the oriented atlas* `A` of `proj`, for orientations
`oB` of the base and `oF` of the model fibre, when `τ` is symplectic, its pull-back to every fibre
read through a chart of `A` is a nondegenerate form whose symplectic orientation is `oF`, and every
chart `A.trivAt b` carries the symplectic orientation of `τ` to the product orientation `oB × oF`
at every point of its source. The fibre pull-backs are smooth forms because `A` is smooth (`hA`).
This is Definition 6.2.1 of [McDuffSalamon2017]. -/
structure IsOrientedCompatible (hA : A.IsContMDiff ∞ IB IF IM)
    (oB : TauCeti.Manifold.Orientation IB B (Fin m))
    (oF : TauCeti.Manifold.Orientation IF F (Fin k)) (τ : SmoothTwoForm IM M) : Prop where
  /-- The form is symplectic. -/
  isSymplectic : τ.IsSymplectic
  /-- The pull-back of the form to each fibre, read through a chart, is nondegenerate. -/
  isNondegenerate_mpullback : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
    SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback ((A.trivAt b).fiberInclusionMap hb')
      ((A.trivAt b).contMDiff_fiberInclusionMap (hA.contMDiffOn_trivAt_symm b) hb') τ)
  /-- The symplectic orientation of each fibre pull-back is the orientation `oF` of the fibre. -/
  orientation_mpullback : ∀ b b' (hb' : b' ∈ (A.trivAt b).baseSet),
    (isNondegenerate_mpullback b b' hb').orientation (oF.card_eq.symm.trans (Fintype.card_fin k)) =
      oF
  /-- Each chart preserves orientation, from the symplectic orientation of `M` to the product
  orientation of `B × F`, at every point of its source. -/
  exists_isOrientationPreservingAt : ∀ b, ∀ x ∈ (A.trivAt b).source,
    ∃ hM : Module.finrank ℝ EM = m + k,
      TauCeti.Manifold.Orientation.IsOrientationPreservingAt
        (isSymplectic.isNondegenerate.orientation hM) (oB.prod oF) (A.trivAt b) x

namespace IsOrientedCompatible

variable {hA : A.IsContMDiff ∞ IB IF IM} {oB : TauCeti.Manifold.Orientation IB B (Fin m)}
  {oF : TauCeti.Manifold.Orientation IF F (Fin k)}

/-- Each chart of an oriented atlas preserves orientation, from the symplectic orientation of a
compatible form `τ` to the product orientation `oB × oF`, at every point of its source. -/
theorem isOrientationPreservingAt (h : A.IsOrientedCompatible hA oB oF τ)
    (hM : Module.finrank ℝ EM = m + k) {b : B} {x : M} (hx : x ∈ (A.trivAt b).source) :
    TauCeti.Manifold.Orientation.IsOrientationPreservingAt
      (h.isSymplectic.isNondegenerate.orientation hM) (oB.prod oF) (A.trivAt b) x := by
  obtain ⟨_, hx⟩ := h.exists_isOrientationPreservingAt b x hx
  -- The orientation depends on the dimension equation only through its proof, which is unique.
  exact hx

/-- A form compatible with an oriented atlas is vertically nondegenerate: it is nondegenerate on
the kernel of the derivative of `proj` at every point. -/
theorem isVerticallyNondegenerate (h : A.IsOrientedCompatible hA oB oF τ) :
    SmoothTwoForm.IsVerticallyNondegenerate IB proj τ :=
  isVerticallyNondegenerate_of_isNondegenerate_mpullback hA fun b ↦
    h.isNondegenerate_mpullback b b (A.mem_baseSet_trivAt b)

end IsOrientedCompatible

end Oriented

end TauCeti.MapFiber.Atlas

end
