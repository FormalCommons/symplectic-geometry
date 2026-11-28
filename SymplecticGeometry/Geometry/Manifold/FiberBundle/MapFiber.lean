/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Basic
public import SymplecticGeometry.Topology.FiberBundle.Trivialization
public import TauCeti.Analysis.Normed.Operator.Splitting.Basic
public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Submersion.Split
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth atlases of a map, read pointwise

Let `proj : M → B` be a map between manifolds and `e` a trivialization of `proj` with model
fibre `F`. When `e` and its inverse are smooth, the fibre of `proj` over a point `b` of the base
set of `e`, read through `e` (`Bundle.Trivialization.fiberInclusionMap`), is a smooth map
`F → M` whose derivative is injective with image the vertical space, the kernel of the derivative
of `proj`. The coordinate change between two such trivializations over `b` is a diffeomorphism of
`F`. For Tau Ceti's smooth atlases of a map (`TauCeti.MapFiber.Atlas.IsContMDiff`) this says that
`proj` is a submersion, so its vertical spaces form a vector bundle. Conversely, every smooth
fibre bundle gives a smooth atlas of the projection of its charted total space. Finally, if the
fibre over `b` carries a manifold structure whose inclusion into `M` is a smooth embedding, the
fibre coordinate of `e` is a diffeomorphism from the fibre onto `F`, and its underlying
homeomorphism is `Bundle.Trivialization.mapFiberHomeomorph`. Over the source of a chart `φ` of
`B`, a chart `e` of a smooth atlas gives the map `p ↦ (φ (proj p), (e p).2)` to `EB × F`,
which is smooth with onto derivative.

## Main definitions

* `Bundle.Trivialization.mfderivFiberInclusionMapEquiv`: the derivative of a fibre inclusion, as
  a continuous linear isomorphism from the tangent space of the model fibre onto the vertical
  space.
* `Bundle.Trivialization.coordChangeDiffeomorph`: the coordinate change between two smooth
  trivializations over a point of both base sets, as a diffeomorphism of the model fibre.
* `Bundle.Trivialization.mapFiberDiffeomorph`: the fibre coordinate of a smooth trivialization,
  as a diffeomorphism from a fibre whose inclusion is a smooth embedding onto the model fibre.
* `TauCeti.ManifoldTotalSpace.mapFiberAtlas`: the atlas of the projection of the charted total
  space of a fibre bundle, made of the bundle's trivializations.

## Main results

* `Bundle.Trivialization.contMDiff_fiberInclusionMap`: the fibre inclusion of a trivialization with
  smooth inverse is smooth.
* `Bundle.Trivialization.contMDiff_symm_val_prod`: on an open set `U` of the base set,
  `(b, v) ↦ e⁻¹ (b, v)` is a smooth map `U × F → M`.
* `Bundle.Trivialization.contMDiffOn_snd` and `Bundle.Trivialization.contMDiff_snd_subtypeVal`:
  the fibre coordinate of a trivialization that is smooth on its source is smooth on the source
  and on every open set inside it.
* `Bundle.Trivialization.mfderiv_proj_apply` and
  `Bundle.Trivialization.mfderiv_fiberInclusionMap_apply`: the derivative of `proj` is the first
  coordinate of the derivative of `e`, and the derivative of a fibre inclusion is that of the
  inverse of `e` on the second factor.
* `Bundle.Trivialization.mfderiv_proj_mfderiv_symm_apply`: the derivative of `proj` after that of
  the inverse of `e` is the projection onto the base component.
* `Bundle.Trivialization.isRegularPoint_proj`: `proj` is regular at every point of the source of
  a differentiable trivialization.
* `Bundle.Trivialization.injective_mfderiv_fiberInclusionMap` and
  `Bundle.Trivialization.range_mfderiv_fiberInclusionMap`: the derivative of a fibre inclusion is
  injective, and its range is the kernel of the derivative of `proj`.
* `Bundle.Trivialization.mfderiv_snd_apply_of_mfderiv_proj_eq_zero`: on vertical vectors, the
  derivatives of the fibre coordinates of two trivializations differ by the derivative of their
  coordinate change.
* `Bundle.Trivialization.mfderiv_fiberInclusionMap_mfderiv_snd_apply`: on vertical vectors, the
  derivative of a fibre inclusion inverts that of the fibre coordinate.
* `TauCeti.MapFiber.Atlas.IsContMDiff.surjective_mfderiv` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.isSubmersion`: the map of a smooth atlas has onto
  derivative everywhere, and is a submersion.
* `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiffAt_extChartAt_proj_prodMk_snd` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.surjective_mfderiv_extChartAt_proj_prodMk_snd`: a chart of a
  smooth atlas, read through a chart of the base, is smooth with onto derivative.
* `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiffOn_symm_extChartAt_symm` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiffAt_symm_extChartAt_symm`: conversely, the inverse
  of a chart of a smooth atlas, read through the inverse of a chart of the base, is smooth where
  it is defined; `Bundle.Trivialization.isOpen_extChartAt_target_inter_symm_preimage_baseSet`
  says that this domain is open when the base has no boundary.
* `TauCeti.MapFiber.Atlas.apply_eq_of_mfderiv_eq_zero_of_proj_eq`: over a preconnected model
  fibre, a real function whose derivative vanishes on vertical vectors at every point of a fibre
  takes the same value at any two points of that fibre.
* `TauCeti.MapFiber.Atlas.IsContMDiff.finrank_eq_add` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.finrank_sub_finrank_eq`: for nonempty finite-dimensional
  `M`, a smooth atlas has `dim M = dim B + dim F`, so its fibre has dimension `dim M - dim B`.
* `TauCeti.MapFiber.Atlas.IsContMDiff.isContMDiffDistribution_ker_mfderiv` and
  `TauCeti.MapFiber.Atlas.IsContMDiff.contMDiffVectorBundle_ker_mfderiv`: the vertical spaces of
  a `C^n` atlas form a `C^m` distribution and vector bundle of rank `dim M - dim B` when
  `m + 1 ≤ n`, by Tau Ceti's lemmas for submersions.
* `TauCeti.ManifoldTotalSpace.isContMDiff_mapFiberAtlas` and
  `TauCeti.ManifoldTotalSpace.coordChange_mapFiberAtlas`: the atlas of a smooth fibre bundle is
  smooth, with the bundle's coordinate changes.

## Implementation notes

The submersion property follows from `Bundle.Trivialization.isRegularPoint_proj` at every point,
by Tau Ceti's `ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv`; this is why it assumes
finite dimensions and a boundaryless total space. The range of the derivative of a fibre
inclusion lies in the kernel by Tau Ceti's `TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq`.
The reverse inclusion uses the chain rule and assumes nothing about dimensions: near a point of the
source, `proj` is the first coordinate of `e`, and the fibre inclusion is the inverse of `e`
restricted to `{b} × F`, so a vector killed by the derivative of `proj` is sent by the invertible
derivative of `e` into `0 × EF`. The proof that a coordinate change is smooth, as the fibre
coordinate of one trivialization after the inverse of the other, follows that of Tau Ceti's
`TauCeti.MapFiber.Atlas.contMDiffFiberBundle`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.1.
-/

public section

open Bundle Function Set Filter
open scoped Manifold Topology ContDiff

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} (e e' : Trivialization F proj) {b : B}

/-! ### Fibre inclusions -/

/-- The fibre inclusion `v ↦ e⁻¹ (b, v)` of a trivialization whose inverse is `C^n` on its target
is `C^n`. -/
theorem contMDiff_fiberInclusionMap
    (he : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet) : ContMDiff IF IM n (e.fiberInclusionMap hb) := by
  rw [e.coe_fiberInclusionMap hb]
  exact he.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ e.mem_target.2 hb

/-- On an open set `U` of the base set of `e`, the map `(b, v) ↦ e⁻¹ (b, v)` from `U × F` to `M`
is `C^n` when the inverse of `e` is `C^n` on its target. -/
theorem contMDiff_symm_val_prod
    (he : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
    {U : TopologicalSpace.Opens B} (hU : (U : Set B) ⊆ e.baseSet) :
    ContMDiff (IB.prod IF) IM n fun p : U × F ↦ e.toOpenPartialHomeomorph.symm (p.1, p.2) :=
  he.comp_contMDiff ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)
    fun p ↦ e.mem_target.2 (hU p.1.property)

/-- The fibre coordinate `x ↦ (e x).2` of a trivialization that is `C^n` on its source is `C^n`
on that source. -/
theorem contMDiffOn_snd (he : ContMDiffOn IM (IB.prod IF) n e e.source) :
    ContMDiffOn IM IF n (fun x ↦ (e x).2) e.source :=
  contMDiff_snd.comp_contMDiffOn he

/-- The fibre coordinate `x ↦ (e x).2` of a trivialization that is `C^n` on its source is `C^n`
on every open set `W` of `M` inside that source. -/
theorem contMDiff_snd_subtypeVal (he : ContMDiffOn IM (IB.prod IF) n e e.source)
    {W : TopologicalSpace.Opens M} (hW : (W : Set M) ⊆ e.source) :
    ContMDiff IM IF n fun x : W ↦ (e x).2 :=
  (e.contMDiffOn_snd he).comp_contMDiff contMDiff_subtypeVal fun x ↦ hW x.property

variable {e}

/-- At a point of the source of a trivialization `e` that is differentiable there, the derivative
of `proj` is the first coordinate of the derivative of `e`. -/
theorem mfderiv_proj_apply {x : M} (hx : x ∈ e.source) (he : MDifferentiableAt IM (IB.prod IF) e x)
    (u : TangentSpace IM x) : mfderiv IM IB proj x u = (mfderiv IM (IB.prod IF) e x u).1 := by
  rw [(e.coe_fst_eventuallyEq_proj hx).symm.mfderiv_eq,
    mfderiv_comp (f := (e : M → B × F)) x mdifferentiableAt_fst he, mfderiv_fst,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, tangentSpaceCast_apply]
  -- `ContinuousLinearMap.fst` acts on the tangent spaces of `B` and `F`, which make up the tangent
  -- space of `B × F` only by definition, so `ContinuousLinearMap.comp_apply` does not match.
  rfl

/-- The derivative at `v` of the fibre inclusion over `b` sends `w` to the derivative of the
inverse of `e` at `(b, v)` applied to `(0, w)`, when that inverse is differentiable there. -/
theorem mfderiv_fiberInclusionMap_apply (hb : b ∈ e.baseSet) (v : F)
    (he : MDifferentiableAt (IB.prod IF) IM e.toOpenPartialHomeomorph.symm (b, v))
    (w : TangentSpace IF v) :
    mfderiv IF IM (e.fiberInclusionMap hb) v w =
      mfderiv (IB.prod IF) IM e.toOpenPartialHomeomorph.symm (b, v) (0, w) := by
  rw [e.coe_fiberInclusionMap hb, ← comp_def (e.toOpenPartialHomeomorph.symm),
    mfderiv_comp v he (mdifferentiableAt_const.prodMk mdifferentiableAt_id),
    ContinuousLinearMap.comp_apply, mfderiv_prod_right]
  -- `inr_apply` is stated on `TangentSpace IB b × TangentSpace IF v`, which is the tangent space
  -- of `B × F` at `(b, v)` by definition.
  exact congrArg _ (ContinuousLinearMap.inr_apply (R := 𝕜) w)

/-- A trivialization that is differentiable with differentiable inverse makes `proj` regular at
every point of its source: near such a point, `proj` is the first coordinate of `e`, whose
derivative is invertible. -/
theorem isRegularPoint_proj (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    {x : M} (hx : x ∈ e.source) : TauCeti.IsRegularPoint IM IB proj x := by
  rw [TauCeti.isRegularPoint_iff]
  intro w
  obtain ⟨u, hu⟩ := he.mfderiv_surjective hx (w, 0)
  exact ⟨u, by rw [mfderiv_proj_apply hx (he.mdifferentiableAt hx), ← coe_coe, hu]⟩

/-- The fibre inclusion of a trivialization that is differentiable with differentiable inverse is
differentiable. -/
theorem mdifferentiable_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet) :
    MDifferentiable IF IM (e.fiberInclusionMap hb) := fun v ↦ by
  rw [e.coe_fiberInclusionMap hb]
  exact (he.mdifferentiableAt_symm (e.mem_target.2 hb)).comp v
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)

/-- The fibre inclusion of a trivialization that is differentiable with differentiable inverse has
injective derivative: the fibre coordinate of `e` is a left inverse of it. -/
theorem injective_mfderiv_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) : Injective (mfderiv IF IM (e.fiberInclusionMap hb) v) :=
  TauCeti.mfderiv_injective_of_leftInverse (g := fun x ↦ (e x).2)
    (mdifferentiableAt_snd.comp _ (he.mdifferentiableAt (e.fiberInclusionMap_mem_source hb v)))
    (mdifferentiable_fiberInclusionMap he hb v) (e.leftInverse_snd_fiberInclusionMap hb)

/-- For a trivialization `e` of `proj` that is differentiable with differentiable inverse, a
tangent vector `u` of `M` at `e.fiberInclusionMap hb v` that the derivative of `proj` sends to
zero is the image under the derivative of the fibre inclusion over `b` of the fibre component of
the image of `u` under the derivative of `e`. -/
theorem mfderiv_fiberInclusionMap_snd_mfderiv_apply
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) {u : TangentSpace IM (e.fiberInclusionMap hb v)}
    (hu : mfderiv IM IB proj (e.fiberInclusionMap hb v) u = 0) :
    mfderiv IF IM (e.fiberInclusionMap hb) v
      (mfderiv IM (IB.prod IF) e (e.fiberInclusionMap hb v) u).2 = u := by
  have hv := e.fiberInclusionMap_mem_source hb v
  have hev := e.apply_fiberInclusionMap hb v
  -- `L` is the derivative of `e`, an equivalence onto the tangent space of `B × F`.
  let L := he.mfderiv hv
  rw [mfderiv_proj_apply hv (he.mdifferentiableAt hv)] at hu
  refine (mfderiv_fiberInclusionMap_apply hb v
    (he.mdifferentiableAt_symm (e.mem_target.2 hb : (b, v) ∈ e.target)) _).trans ?_
  conv_rhs => rw [← L.symm_apply_apply u]
  rw [he.coe_mfderiv_symm, he.coe_mfderiv, coe_coe, hev]
  exact congrArg _ (Prod.ext hu.symm rfl)

/-- The derivative of `proj` vanishes on the image of the derivative of the fibre inclusion over
`b`: that inclusion takes values in the fibre over `b`. -/
theorem mfderiv_proj_mfderiv_fiberInclusionMap_apply (hb : b ∈ e.baseSet) (v : F)
    (w : TangentSpace IF v) :
    mfderiv IM IB proj (e.fiberInclusionMap hb v) (mfderiv IF IM (e.fiberInclusionMap hb) v w) =
      0 :=
  TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq
    (.of_forall (e.proj_fiberInclusionMap hb)) ⟨w, rfl⟩

/-- **The tangent spaces of a fibre.** For a trivialization `e` of `proj` that is differentiable
with differentiable inverse, the derivative of the fibre inclusion over `b` at `v` has as range
the vertical space at its image, the kernel of the derivative of `proj` there. -/
theorem range_mfderiv_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    (mfderiv IF IM (e.fiberInclusionMap hb) v).range =
      (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker :=
  le_antisymm (by
    rintro _ ⟨w, rfl⟩
    exact mfderiv_proj_mfderiv_fiberInclusionMap_apply hb v w) fun _ hu ↦
      ⟨_, mfderiv_fiberInclusionMap_snd_mfderiv_apply he hb v hu⟩

/-- For a trivialization `e` of `proj` that is differentiable with differentiable inverse, the
derivative of `proj` paired with the fibre component of the derivative of `e` is invertible at
`e.fiberInclusionMap hb v`: it is the derivative of `e` there. -/
theorem isInvertible_mfderiv_proj_prod_snd_comp_mfderiv
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    ((mfderiv IM IB proj (e.fiberInclusionMap hb v)).prod
      ((ContinuousLinearMap.snd 𝕜 (TangentSpace IB b) (TangentSpace IF v)).comp
        (mfderiv IM (IB.prod IF) e (e.fiberInclusionMap hb v)))).IsInvertible := by
  have hv := e.fiberInclusionMap_mem_source hb v
  exact ⟨he.mfderiv hv, ContinuousLinearMap.ext fun u ↦
    Prod.ext (mfderiv_proj_apply hv (he.mdifferentiableAt hv) u).symm rfl⟩

/-- For a trivialization `e` of `proj` that is differentiable with differentiable inverse, the
derivative at `v` of the fibre inclusion over `b`, as a continuous linear isomorphism from the
tangent space of the model fibre at `v` onto the vertical space at its image, the kernel of the
derivative of `proj` there. Its inverse is the fibre component of the derivative of `e`
(`mfderivFiberInclusionMapEquiv_symm_apply`). -/
noncomputable def mfderivFiberInclusionMapEquiv
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    TangentSpace IF v ≃L[𝕜] (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker :=
  ContinuousLinearMap.kerEquivOfProd _ _ (isInvertible_mfderiv_proj_prod_snd_comp_mfderiv he hb v)

theorem mfderivFiberInclusionMapEquiv_def
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    mfderivFiberInclusionMapEquiv he hb v =
      ContinuousLinearMap.kerEquivOfProd _ _
        (isInvertible_mfderiv_proj_prod_snd_comp_mfderiv he hb v) :=
  (rfl)

/-- `mfderivFiberInclusionMapEquiv he hb v` sends `w` to the image of `w` under the derivative
of the fibre inclusion over `b` at `v`. -/
@[simp]
theorem coe_mfderivFiberInclusionMapEquiv_apply
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) (w : TangentSpace IF v) :
    (mfderivFiberInclusionMapEquiv he hb v w : TangentSpace IM (e.fiberInclusionMap hb v)) =
      mfderiv IF IM (e.fiberInclusionMap hb) v w := by
  have hw := mfderiv_proj_mfderiv_fiberInclusionMap_apply (IM := IM) (IB := IB) (IF := IF) hb v w
  rw [mfderivFiberInclusionMapEquiv_def, ContinuousLinearMap.coe_kerEquivOfProd_apply]
  -- The fibre component of the derivative of `e` sends the image of `w` back to `w`.
  conv_lhs => rw [← injective_mfderiv_fiberInclusionMap he hb v
    (mfderiv_fiberInclusionMap_snd_mfderiv_apply he hb v hw)]
  exact ContinuousLinearMap.kerSection_apply_of_mem_ker
    (isInvertible_mfderiv_proj_prod_snd_comp_mfderiv he hb v) hw

/-- The inverse of `mfderivFiberInclusionMapEquiv he hb v` sends a vertical vector `u` to the
fibre component of its image under the derivative of `e`. -/
@[simp]
theorem mfderivFiberInclusionMapEquiv_symm_apply
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) (u : (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker) :
    (mfderivFiberInclusionMapEquiv he hb v).symm u =
      (mfderiv IM (IB.prod IF) e (e.fiberInclusionMap hb v) u).2 := by
  rw [mfderivFiberInclusionMapEquiv_def, ContinuousLinearMap.kerEquivOfProd_symm_apply]
  -- The inverse is `ContinuousLinearMap.snd` after the derivative of `e`, typed with the tangent
  -- spaces of `B` at `b` and `F` at `v`, which make up that of `B × F` at `e (e.fiberInclusionMap
  -- hb v)` only by definition, so `ContinuousLinearMap.comp_apply` does not match.
  rfl

/-- For a trivialization `e` of `proj` that is differentiable with differentiable inverse, the
derivative of `proj` sends the image of a tangent vector `u` of `B × F` at `(b, v)` under the
derivative of the inverse of `e` to the base component of `u`. -/
theorem mfderiv_proj_mfderiv_symm_apply
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) (u : TangentSpace (IB.prod IF) (b, v)) :
    mfderiv IM IB proj (e.toOpenPartialHomeomorph.symm (b, v))
      (mfderiv (IB.prod IF) IM e.toOpenPartialHomeomorph.symm (b, v) u) = u.1 := by
  have hv := e.fiberInclusionMap_mem_source hb v
  have hev := e.apply_fiberInclusionMap hb v
  let L := he.mfderiv hv
  have h := L.apply_symm_apply u
  rw [he.coe_mfderiv_symm, he.coe_mfderiv, coe_coe, hev] at h
  rw [← e.fiberInclusionMap_apply hb, mfderiv_proj_apply hv (he.mdifferentiableAt hv)]
  exact congrArg Prod.fst h

variable {e'} in
/-- **Vertical vectors under a change of trivialization.** Let `e` and `e'` be trivializations
of `proj` that are differentiable with differentiable inverses, and `b` a point of both base
sets. On a vertical vector `u` at `e⁻¹ (b, v)`, the derivative of the fibre coordinate of `e'` is
the derivative at `v` of the coordinate change from `e` to `e'` over `b`, applied to the image of
`u` under the derivative of the fibre coordinate of `e`. -/
theorem mfderiv_snd_apply_of_mfderiv_proj_eq_zero
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    (he' : e'.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) (v : F) {u : TangentSpace IM (e.fiberInclusionMap hb v)}
    (hu : mfderiv IM IB proj (e.fiberInclusionMap hb v) u = 0) :
    mfderiv IM IF (fun x ↦ (e' x).2) (e.fiberInclusionMap hb v) u =
      mfderiv IF IF (e.coordChange e' b) v
        (mfderiv IM IF (fun x ↦ (e x).2) (e.fiberInclusionMap hb v) u) := by
  have hu' : u ∈ (mfderiv IF IM (e.fiberInclusionMap hb) v).range := by
    rw [range_mfderiv_fiberInclusionMap he hb v]
    exact hu
  obtain ⟨w, rfl⟩ := hu'
  have hι := mdifferentiable_fiberInclusionMap he hb v
  have hsnd {e₀ : Trivialization F proj}
      (he₀ : e₀.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb₀ : b ∈ e₀.baseSet) :
      MDifferentiableAt IM IF (fun x ↦ (e₀ x).2) (e.fiberInclusionMap hb v) :=
    mdifferentiableAt_snd.comp _ (he₀.mdifferentiableAt
      (e₀.mem_source.2 ((e.proj_fiberInclusionMap hb v).symm ▸ hb₀)))
  have hc : (fun x ↦ (e' x).2) ∘ e.fiberInclusionMap hb = e.coordChange e' b := by
    rw [e.coe_fiberInclusionMap_eq_comp_coordChange e' hb hb', ← comp_assoc,
      (e'.leftInverse_snd_fiberInclusionMap hb').comp_eq_id, id_comp]
  rw [ContinuousLinearMap.coe_coe]
  have h₁ := mfderiv_comp_apply v (hsnd he' hb') hι w
  have h₂ := mfderiv_comp_apply v (hsnd he hb) hι w
  rw [hc] at h₁
  rw [(e.leftInverse_snd_fiberInclusionMap hb).comp_eq_id, mfderiv_id,
    ContinuousLinearMap.id_apply] at h₂
  -- `h₂` identifies `w` with its image under the two derivatives; the tangent spaces of `F` at
  -- `v` and at `(e (e.fiberInclusionMap hb v)).2` agree only by definition.
  exact h₁.symm.trans (congrArg _ h₂)

/-- For a trivialization `e` of `proj` that is differentiable with differentiable inverse, the
derivative at `v` of the fibre inclusion over `b` sends the image of a vertical vector `u` at
`e.fiberInclusionMap hb v` under the derivative of the fibre coordinate of `e` back to `u`. -/
theorem mfderiv_fiberInclusionMap_mfderiv_snd_apply
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) {u : TangentSpace IM (e.fiberInclusionMap hb v)}
    (hu : mfderiv IM IB proj (e.fiberInclusionMap hb v) u = 0) :
    mfderiv IF IM (e.fiberInclusionMap hb) v
      (mfderiv IM IF (fun x ↦ (e x).2) (e.fiberInclusionMap hb v) u) = u := by
  have h := (he.mdifferentiableAt (e.fiberInclusionMap_mem_source hb v)).mfderiv_snd_apply u
  -- The tangent spaces of `F` at `v` and at `(e (e.fiberInclusionMap hb v)).2` agree only by
  -- definition, so `h` cannot be rewritten in the goal.
  exact (congrArg _ h).trans (mfderiv_fiberInclusionMap_snd_mfderiv_apply he hb v hu)

/-! ### Coordinate changes -/

variable (e)

/-- The coordinate change from `e` to `e'` over `b` is `C^n` when the inverse of `e` is `C^n` on
its target and `e'` is `C^n` on its source. -/
theorem contMDiff_coordChange
    (he : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn IM (IB.prod IF) n e' e'.source) (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) : ContMDiff IF IF n (e.coordChange e' b) := by
  have h := contMDiff_snd.comp_contMDiffOn he' |>.comp_contMDiff
    (e.contMDiff_fiberInclusionMap he hb) fun v ↦
      e'.mem_source.2 ((e.proj_fiberInclusionMap hb v).symm ▸ hb')
  exact h.congr fun v ↦ by
    rw [comp_apply, fiberInclusionMap_apply, comp_apply, ← e.mk_coordChange e' hb hb' v]

/-- The coordinate change from `e` to `e'` over a point `b` of both base sets, as a `C^n`
diffeomorphism of the model fibre, when both trivializations are `C^n` with `C^n` inverses.
Its underlying homeomorphism is `Bundle.Trivialization.coordChangeHomeomorph`. -/
def coordChangeDiffeomorph (he : ContMDiffOn IM (IB.prod IF) n e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
    (he' : ContMDiffOn IM (IB.prod IF) n e' e'.source)
    (he'_symm : ContMDiffOn (IB.prod IF) IM n e'.toOpenPartialHomeomorph.symm e'.target)
    (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) : F ≃ₘ^n⟮IF, IF⟯ F where
  toEquiv := (e.coordChangeHomeomorph e' hb hb').toEquiv
  contMDiff_toFun := e.contMDiff_coordChange e' he_symm he' hb hb'
  contMDiff_invFun := e'.contMDiff_coordChange e he'_symm he hb' hb

variable (he : ContMDiffOn IM (IB.prod IF) n e e.source)
  (he_symm : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
  (he' : ContMDiffOn IM (IB.prod IF) n e' e'.source)
  (he'_symm : ContMDiffOn (IB.prod IF) IM n e'.toOpenPartialHomeomorph.symm e'.target)
  (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)

@[simp]
theorem coe_coordChangeDiffeomorph :
    ⇑(e.coordChangeDiffeomorph e' he he_symm he' he'_symm hb hb') = e.coordChange e' b :=
  (rfl)

@[simp]
theorem coordChangeDiffeomorph_symm :
    (e.coordChangeDiffeomorph e' he he_symm he' he'_symm hb hb').symm =
      e'.coordChangeDiffeomorph e he' he'_symm he he_symm hb' hb :=
  Diffeomorph.ext fun _ ↦ (rfl)

/-! ### Fibres as manifolds -/

section mapFiberDiffeomorph

variable {EZ : Type*} [NormedAddCommGroup EZ] [NormedSpace 𝕜 EZ] {HZ : Type*}
  [TopologicalSpace HZ] {IZ : ModelWithCorners 𝕜 EZ HZ}
  [ChartedSpace HZ (TauCeti.MapFiber proj b)]

/-- Let `e` be a trivialization of `proj : M → B` with model fibre `F`, `C^n` on its source with
a `C^n` inverse on its target, and let `b` be a point of its base set. If the fibre
`TauCeti.MapFiber proj b` carries a manifold structure for which its inclusion into `M` is a
`C^n` embedding, then the fibre coordinate `x ↦ (e x).2` of `e` is a `C^n` diffeomorphism from
the fibre onto `F`, with inverse `v ↦ e.symm (b, v)`. -/
def mapFiberDiffeomorph (he : ContMDiffOn IM (IB.prod IF) n e e.source)
    (he_symm : ContMDiffOn (IB.prod IF) IM n e.toOpenPartialHomeomorph.symm e.target)
    (hb : b ∈ e.baseSet)
    (hι : Manifold.IsSmoothEmbedding IZ IM n (Subtype.val : TauCeti.MapFiber proj b → M)) :
    TauCeti.MapFiber proj b ≃ₘ^n⟮IZ, IF⟯ F where
  toFun x := (e x).2
  invFun v := ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩
  left_inv x := by simpa using (e.mapFiberHomeomorph hb).symm_apply_apply x
  right_inv v := by simpa using (e.mapFiberHomeomorph hb).apply_symm_apply v
  contMDiff_toFun :=
    (he.comp_contMDiff hι.contMDiff fun x ↦ e.mem_source.2 (x.property.symm ▸ hb)).snd
  contMDiff_invFun := hι.contMDiff_iff_comp.2 <|
    (e.contMDiff_fiberInclusionMap he_symm hb).congr fun v ↦
      (e.fiberInclusionMap_apply hb v).symm

variable (hι : Manifold.IsSmoothEmbedding IZ IM n (Subtype.val : TauCeti.MapFiber proj b → M))

@[simp]
theorem mapFiberDiffeomorph_apply (x : TauCeti.MapFiber proj b) :
    e.mapFiberDiffeomorph he he_symm hb hι x = (e x).2 :=
  (rfl)

@[simp]
theorem mapFiberDiffeomorph_symm_apply (v : F) :
    (e.mapFiberDiffeomorph he he_symm hb hι).symm v =
      ⟨e.toOpenPartialHomeomorph.symm (b, v), e.proj_symm_apply' hb⟩ :=
  (rfl)

/-- The homeomorphism underlying `Bundle.Trivialization.mapFiberDiffeomorph` is
`Bundle.Trivialization.mapFiberHomeomorph`. -/
theorem toHomeomorph_mapFiberDiffeomorph :
    (e.mapFiberDiffeomorph he he_symm hb hι).toHomeomorph = e.mapFiberHomeomorph hb :=
  Homeomorph.ext fun x ↦ (e.mapFiberHomeomorph_apply hb x).symm

end mapFiberDiffeomorph

/-- For a trivialization `e` over a boundaryless base and the extended chart `φ` of `B` at
`b₀`, the points `x` of the target of `φ` with `φ⁻¹ x` in the base set of `e` form an open set
of the model space. -/
theorem isOpen_extChartAt_target_inter_symm_preimage_baseSet [IB.Boundaryless] (b₀ : B) :
    IsOpen ((extChartAt IB b₀).target ∩ (extChartAt IB b₀).symm ⁻¹' e.baseSet) := by
  simpa only [(isOpen_extChartAt_target b₀).interior_eq] using
    e.isOpen_interior_extChartAt_target_inter_symm_preimage_baseSet (IB := IB) b₀

end Bundle.Trivialization

/-! ### Smooth atlases -/

namespace TauCeti.MapFiber.Atlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} {A : Atlas F proj}

/-- The trivializations of a `C^n` atlas, `n ≠ 0`, are differentiable with differentiable
inverses. -/
theorem IsContMDiff.mdifferentiable_trivAt (hA : A.IsContMDiff n IB IF IM) (hn : n ≠ 0)
    (b : B) : (A.trivAt b).toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF) :=
  ⟨(hA.contMDiffOn_trivAt b).mdifferentiableOn hn,
    (hA.contMDiffOn_trivAt_symm b).mdifferentiableOn hn⟩

/-- The map of a `C^n` atlas, `n ≠ 0`, has onto derivative at every point. -/
theorem IsContMDiff.surjective_mfderiv (hA : A.IsContMDiff n IB IF IM) (hn : n ≠ 0) (x : M) :
    Surjective (mfderiv IM IB proj x) :=
  TauCeti.isRegularPoint_iff.1 <| (A.trivAt (proj x)).isRegularPoint_proj
    (hA.mdifferentiable_trivAt hn (proj x))
    ((A.trivAt (proj x)).mem_source.2 (A.mem_baseSet_trivAt (proj x)))

/-- **The dimension count of an atlas.** If `proj : M → B` has a `C^n` atlas with model fibre
`F`, `n ≠ 0`, `M` is finite-dimensional and has a point, then `dim M = dim B + dim F`: the
derivative of a chart at a point of its source identifies the tangent space of `M` with
`EB × EF`. -/
theorem IsContMDiff.finrank_eq_add [FiniteDimensional 𝕜 EM] (hA : A.IsContMDiff n IB IF IM)
    (hn : n ≠ 0) (x : M) :
    Module.finrank 𝕜 EM = Module.finrank 𝕜 EB + Module.finrank 𝕜 EF := by
  -- The tangent spaces of `M` and `B × F` are `EM` and `EB × EF` by definition; the type ascription
  -- states this, so that `Module.finrank_prod` applies.
  let L : EM ≃ₗ[𝕜] EB × EF := ((hA.mdifferentiable_trivAt hn (proj x)).mfderiv
    ((A.trivAt (proj x)).mem_source.2 (A.mem_baseSet_trivAt (proj x)))).toLinearEquiv
  have : Module.Finite 𝕜 (EB × EF) := Module.Finite.equiv L
  have : Module.Finite 𝕜 EB :=
    Module.Finite.of_surjective (LinearMap.fst 𝕜 EB EF) LinearMap.fst_surjective
  have : Module.Finite 𝕜 EF :=
    Module.Finite.of_surjective (LinearMap.snd 𝕜 EB EF) LinearMap.snd_surjective
  rw [← Module.finrank_prod, L.finrank_eq]

/-- **The dimension of the fibre.** If `proj : M → B` has a `C^n` atlas with model fibre `F`,
`n ≠ 0`, and `M` is nonempty and finite-dimensional, then `dim M - dim B = dim F`. -/
theorem IsContMDiff.finrank_sub_finrank_eq [FiniteDimensional 𝕜 EM] [Nonempty M]
    (hA : A.IsContMDiff n IB IF IM) (hn : n ≠ 0) :
    Module.finrank 𝕜 EM - Module.finrank 𝕜 EB = Module.finrank 𝕜 EF := by
  rw [hA.finrank_eq_add hn (Classical.arbitrary M), Nat.add_sub_cancel_left]

/-- The fibre coordinate `y ↦ (A.trivAt b y).2` of a chart of a `C^n` atlas is `C^n` on the
source of the chart. -/
theorem IsContMDiff.contMDiffOn_snd_trivAt (hA : A.IsContMDiff n IB IF IM) (b : B) :
    ContMDiffOn IM IF n (fun y ↦ (A.trivAt b y).2) (A.trivAt b).source :=
  (A.trivAt b).contMDiffOn_snd (hA.contMDiffOn_trivAt b)

/-- The fibre coordinate `y ↦ (A.trivAt b y).2` of a chart of a `C^n` atlas is `C^n` at every
point of `M` over the base set of the chart. -/
theorem IsContMDiff.contMDiffAt_snd_trivAt (hA : A.IsContMDiff n IB IF IM) {b : B} {x : M}
    (hx : proj x ∈ (A.trivAt b).baseSet) :
    ContMDiffAt IM IF n (fun y ↦ (A.trivAt b y).2) x :=
  (hA.contMDiffOn_snd_trivAt b).contMDiffAt
    ((A.trivAt b).open_source.mem_nhds ((A.trivAt b).mem_source.2 hx))

/-- Over the base set of a chart `e = A.trivAt b'` of a `C^n` atlas and the source of the chart
of `B` at `b`, the map `p ↦ (φ (proj p), (e p).2)` to `EB × F`, with `φ` the extended chart of
`B` at `b`, is `C^m` for every `m ≤ n` for which `B` is a `C^m` manifold. -/
theorem IsContMDiff.contMDiffAt_extChartAt_proj_prodMk_snd {m : ℕ∞ω} [IsManifold IB m B]
    (hA : A.IsContMDiff n IB IF IM) (hmn : m ≤ n) {b' b : B} {x : M}
    (hx : proj x ∈ (A.trivAt b').baseSet) (hxb : proj x ∈ (chartAt HB b).source) :
    ContMDiffAt IM (𝓘(𝕜, EB).prod IF) m
      (fun y ↦ (extChartAt IB b (proj y), (A.trivAt b' y).2)) x :=
  ((contMDiffAt_extChartAt' hxb).comp x ((hA.contMDiff_proj x).of_le hmn)).prodMk
    ((hA.contMDiffAt_snd_trivAt hx).of_le hmn)

/-- Over the base set of a chart `e = A.trivAt b'` of a `C^n` atlas, `n ≠ 0`, and the source of
the chart of `B` at `b`, the map `p ↦ (φ (proj p), (e p).2)` to `EB × F`, with `φ` the extended
chart of `B` at `b`, has onto derivative: near `x` it is `e` followed by `Prod.map φ id`, both of
which have invertible derivatives there. -/
theorem IsContMDiff.surjective_mfderiv_extChartAt_proj_prodMk_snd [IsManifold IB 1 B]
    (hA : A.IsContMDiff n IB IF IM) (hn : n ≠ 0) {b' b : B} {x : M}
    (hx : proj x ∈ (A.trivAt b').baseSet) (hxb : proj x ∈ (chartAt HB b).source) :
    Surjective (mfderiv IM (𝓘(𝕜, EB).prod IF)
      (fun y ↦ (extChartAt IB b (proj y), (A.trivAt b' y).2)) x) := by
  set e := A.trivAt b'
  have hxe : x ∈ e.source := e.mem_source.2 hx
  -- Near `x` the map is `Prod.map φ id ∘ e`, since the first coordinate of `e` is `proj`.
  have heq : (fun y ↦ (extChartAt IB b (proj y), (e y).2)) =ᶠ[𝓝 x]
      Prod.map (extChartAt IB b) id ∘ e := by
    filter_upwards [e.open_source.mem_nhds hxe] with y hy
    exact congrArg (fun c ↦ (extChartAt IB b c, (e y).2)) (e.coe_fst hy).symm
  have he := hA.mdifferentiable_trivAt hn b'
  have hex : (e x).1 = proj x := e.coe_fst hxe
  have hψ : MDifferentiableAt IB 𝓘(𝕜, EB) (extChartAt IB b) (e x).1 := by
    rw [hex]
    exact (contMDiffAt_extChartAt' (n := 1) hxb).mdifferentiableAt one_ne_zero
  have hmap : MDifferentiableAt (IB.prod IF) (𝓘(𝕜, EB).prod IF) (Prod.map (extChartAt IB b) id)
      (e x) := hψ.prodMap mdifferentiableAt_id
  rw [heq.mfderiv_eq, mfderiv_comp x hmap (he.mdifferentiableAt hxe),
    mfderiv_prodMap hψ mdifferentiableAt_id, mfderiv_id]
  have hinv := isInvertible_mfderiv_extChartAt (I := IB) (x := b) (y := (e x).1)
    (by rw [hex, extChartAt_source]; exact hxb)
  -- The derivative of `Prod.map φ id` at `e x` is onto, `dφ` being invertible there.
  have hL : Surjective ((mfderiv IB 𝓘(𝕜, EB) (extChartAt IB b) (e x).1).prodMap
      (ContinuousLinearMap.id 𝕜 (TangentSpace IF (e x).2))) :=
    hinv.surjective.prodMap Function.surjective_id
  -- The cast between the tangent spaces at equal points is the identity.
  exact fun q ↦ let ⟨p, hp⟩ := hL.comp (he.mfderiv_surjective hxe) q; ⟨p, hp⟩

/-- For a chart `e = A.trivAt b'` of a `C^n` atlas and the extended chart `φ` of `B` at `b₀`, the
map `q ↦ e⁻¹ (φ⁻¹ q.1, q.2)` is `C^n` on the product with `F` of the set of the points `x` of the
target of `φ` with `φ⁻¹ x` in the base set of `e`. -/
theorem IsContMDiff.contMDiffOn_symm_extChartAt_symm [IsManifold IB n B]
    (hA : A.IsContMDiff n IB IF IM) (b' b₀ : B) :
    ContMDiffOn (𝓘(𝕜, EB).prod IF) IM n
      (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
        ((extChartAt IB b₀).symm q.1, q.2))
      (((extChartAt IB b₀).target ∩ (extChartAt IB b₀).symm ⁻¹' (A.trivAt b').baseSet) ×ˢ
        univ) := by
  refine (hA.contMDiffOn_trivAt_symm b').comp
    (((contMDiffOn_extChartAt_symm b₀).comp contMDiffOn_fst ?_).prodMk contMDiffOn_snd) ?_
  · exact fun _ hq ↦ hq.1.1
  · exact fun _ hq ↦ (A.trivAt b').mem_target.2 hq.1.2

/-- For a chart `e = A.trivAt b'` of a `C^n` atlas over a boundaryless base and the extended chart
`φ` of `B` at `b₀`, the map `q ↦ e⁻¹ (φ⁻¹ q.1, q.2)` is `C^n` at each `q` such that `q.1` lies
in the target of `φ` and `φ⁻¹ q.1` in the base set of `e`. -/
theorem IsContMDiff.contMDiffAt_symm_extChartAt_symm [IB.Boundaryless] [IsManifold IB n B]
    (hA : A.IsContMDiff n IB IF IM) {b' b₀ : B} {q : EB × F}
    (hq : q.1 ∈ (extChartAt IB b₀).target ∩ (extChartAt IB b₀).symm ⁻¹' (A.trivAt b').baseSet) :
    ContMDiffAt (𝓘(𝕜, EB).prod IF) IM n
      (fun q : EB × F ↦ (A.trivAt b').toOpenPartialHomeomorph.symm
        ((extChartAt IB b₀).symm q.1, q.2)) q :=
  (hA.contMDiffOn_symm_extChartAt_symm b' b₀).contMDiffAt
    ((((A.trivAt b').isOpen_extChartAt_target_inter_symm_preimage_baseSet b₀).prod
      isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)

end TauCeti.MapFiber.Atlas

/-! ### Functions constant along fibres -/

namespace TauCeti.MapFiber.Atlas

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B]
  [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {proj : M → B} {A : Atlas F proj} {n : ℕ∞ω}

/-- **Functions constant along a fibre.** Let `A` be a `C^n` atlas of `proj`, `n ≠ 0`, with
preconnected model fibre `F`, and let `g : M → ℝ` be differentiable at every point over `proj x`,
with derivative zero there on every vertical vector. Then `g x = g y` whenever
`proj x = proj y`. -/
theorem apply_eq_of_mfderiv_eq_zero_of_proj_eq [IsManifold IF 1 F] [PreconnectedSpace F]
    (hA : A.IsContMDiff n IB IF IM) (hn : n ≠ 0) {g : M → ℝ} {x y : M} (hxy : proj x = proj y)
    (hg : ∀ z, proj z = proj x → MDifferentiableAt IM 𝓘(ℝ, ℝ) g z)
    (h0 : ∀ z, proj z = proj x → ∀ η : TangentSpace IM z, mfderiv IM IB proj z η = 0 →
      mfderiv IM 𝓘(ℝ, ℝ) g z η = 0) :
    g x = g y := by
  let e := A.trivAt (proj x)
  have hb : proj x ∈ e.baseSet := A.mem_baseSet_trivAt (proj x)
  have hι := e.mdifferentiable_fiberInclusionMap (hA.mdifferentiable_trivAt hn (proj x)) hb
  have hgι : MDifferentiable IF 𝓘(ℝ, ℝ) (g ∘ e.fiberInclusionMap hb) := fun p ↦
    (hg _ (e.proj_fiberInclusionMap hb p)).comp p (hι p)
  have hzero (p : F) : mfderiv IF 𝓘(ℝ, ℝ) (g ∘ e.fiberInclusionMap hb) p = 0 := by
    ext ε
    rw [mfderiv_comp p (hg _ (e.proj_fiberInclusionMap hb p)) (hι p),
      ContinuousLinearMap.comp_apply, zero_apply]
    exact h0 _ (e.proj_fiberInclusionMap hb p) _
      (e.mfderiv_proj_mfderiv_fiberInclusionMap_apply hb p ε)
  have hxι : e.fiberInclusionMap hb (e x).2 = x := e.fiberInclusionMap_snd_apply hb
  have hyι : e.fiberInclusionMap hb (e y).2 = y := by
    rw [e.fiberInclusionMap_apply, hxy, e.symm_apply_mk_proj (e.mem_source.2 (hxy ▸ hb))]
  have h := hgι.apply_eq_of_mfderiv_eq_zero hzero (e x).2 (e y).2
  rwa [Function.comp_apply, Function.comp_apply, hxι, hyι] at h

end TauCeti.MapFiber.Atlas

namespace TauCeti.MapFiber.Atlas.IsContMDiff

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB n B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [FiniteDimensional 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [IM.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM n M] {proj : M → B} {A : Atlas F proj}

/-- **The map of a smooth atlas is a submersion.** If `proj : M → B` has a `C^n` atlas, `1 ≤ n`,
between finite-dimensional manifolds with `M` boundaryless, then `proj` is a `C^n` submersion. -/
theorem isSubmersion (hA : A.IsContMDiff n IB IF IM) (hn : 1 ≤ n) :
    Manifold.IsSubmersion IM IB n proj :=
  (hA.contMDiff_proj.isSubmersionOfComplement_of_surjective_mfderiv hn
    (hA.surjective_mfderiv (ne_of_gt (zero_lt_one.trans_le hn)))).isSubmersion

/-- **The vertical distribution of a smooth atlas.** If `proj : M → B` has a `C^n` atlas, with
`M` boundaryless and both models finite-dimensional, then for `m + 1 ≤ n` the vertical spaces, the
kernels of the derivative of `proj`, form a `C^m` distribution of rank `dim M - dim B`. -/
theorem isContMDiffDistribution_ker_mfderiv [IsManifold IM 1 M] (hA : A.IsContMDiff n IB IF IM)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) :
    TauCeti.IsContMDiffDistribution IM m (Module.finrank 𝕜 EM - Module.finrank 𝕜 EB)
      fun x ↦ (mfderiv IM IB proj x).ker :=
  have hn : 1 ≤ n := le_add_self.trans hmn
  have := FiniteDimensional.completeSpace 𝕜 EM
  (hA.isSubmersion hn).isContMDiffDistribution_ker_mfderiv hmn

/-- **The vertical bundle of a smooth atlas.** With the bundle structure of
`isContMDiffDistribution_ker_mfderiv`, the vertical spaces of a map with a `C^n` atlas form a
`C^m` vector bundle with fibre `Fin (dim M - dim B) → 𝕜`, for `m + 1 ≤ n`. -/
theorem contMDiffVectorBundle_ker_mfderiv [IsManifold IM 1 M] (hA : A.IsContMDiff n IB IF IM)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) :
    letI := (hA.isContMDiffDistribution_ker_mfderiv hmn).fiberBundle
    letI := (hA.isContMDiffDistribution_ker_mfderiv hmn).vectorBundle
    ContMDiffVectorBundle m (Fin (Module.finrank 𝕜 EM - Module.finrank 𝕜 EB) → 𝕜)
      (fun x ↦ (mfderiv IM IB proj x).ker) IM :=
  have : IsManifold IM (m + 1) M := .of_le hmn
  have := FiniteDimensional.completeSpace 𝕜 EM
  (hA.isContMDiffDistribution_ker_mfderiv hmn).contMDiffVectorBundle

end TauCeti.MapFiber.Atlas.IsContMDiff

/-! ### The atlas of a smooth fibre bundle -/

namespace TauCeti.ManifoldTotalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

variable (F E) in
/-- The atlas of the projection of the charted total space of a fibre bundle: at each point `b`
of the base, the bundle's trivialization at `b`, read on the charted total space. -/
def mapFiberAtlas :
    MapFiber.Atlas F (fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj) where
  trivAt b := (trivializationAt F E b).compHomeomorph (homeomorph F E).symm
  mem_baseSet_trivAt b := FiberBundle.mem_baseSet_trivializationAt F E b

theorem trivAt_mapFiberAtlas (b : B) :
    (mapFiberAtlas F E).trivAt b =
      (trivializationAt F E b).compHomeomorph (homeomorph F E).symm :=
  (rfl)

/-- The coordinate changes of the atlas of a fibre bundle are those of the bundle. -/
@[simp]
theorem coordChange_mapFiberAtlas (b b' x : B) :
    ((mapFiberAtlas F E).trivAt b).coordChange ((mapFiberAtlas F E).trivAt b') x =
      (trivializationAt F E b).coordChange (trivializationAt F E b') x := by
  rw [trivAt_mapFiberAtlas, trivAt_mapFiberAtlas, Trivialization.coordChange_compHomeomorph]

/-- **The atlas of a smooth fibre bundle is smooth.** The trivializations of a `C^n` fibre bundle,
read on its charted total space, are `C^n` with `C^n` inverses. -/
theorem isContMDiff_mapFiberAtlas [ContMDiffFiberBundle n F E IB IF] :
    (mapFiberAtlas F E).IsContMDiff n IB IF (IB.prod IF) where
  contMDiffOn_trivAt b := by
    rw [trivAt_mapFiberAtlas]
    exact contMDiffOn_trivialization (trivializationAt F E b)
  contMDiffOn_trivAt_symm b := by
    rw [trivAt_mapFiberAtlas]
    exact contMDiffOn_trivialization_symm (trivializationAt F E b)

end TauCeti.ManifoldTotalSpace

end
