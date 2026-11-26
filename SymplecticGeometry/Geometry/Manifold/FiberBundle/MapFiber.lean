/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.FiberBundle.Basic
public import SymplecticGeometry.Topology.FiberBundle.ChangeModelFiber
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Submersion.Split
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Manifold.IsManifold.Basic

/-!
# Smooth atlases of a map, read pointwise

Let `proj : M → B` be a map between manifolds and `e` a trivialization of `proj` with model
fibre `F`. When `e` and its inverse are smooth, the fibre of `proj` over a point `b` of the base
set of `e`, read through `e` (`Bundle.Trivialization.fiberInclusionMap`), is a smooth map
`F → M` whose derivative is injective with image the vertical space, the kernel of the derivative
of `proj`. The coordinate change between two such trivializations over `b` is a diffeomorphism of
`F`. For Tau Ceti's smooth atlases of a map (`TauCeti.MapFiber.Atlas.IsContMDiff`) this says that
`proj` is a submersion. Conversely, every smooth fibre bundle gives a smooth atlas of the
projection of its charted total space. Finally, if the fibre over `b` carries a manifold structure
whose inclusion into `M` is a smooth embedding, the fibre coordinate of `e` is a diffeomorphism
from the fibre onto `F`, and its underlying homeomorphism is
`Bundle.Trivialization.mapFiberHomeomorph`.

## Main definitions

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
* `TauCeti.MapFiber.Atlas.IsContMDiff.isSubmersion`: the map of a smooth atlas is a submersion.
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

/-- **The tangent spaces of a fibre.** For a trivialization `e` of `proj` that is differentiable
with differentiable inverse, the derivative of the fibre inclusion over `b` at `v` has as range
the vertical space at its image, the kernel of the derivative of `proj` there. -/
theorem range_mfderiv_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    (mfderiv IF IM (e.fiberInclusionMap hb) v).range =
      (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker := by
  have hv := e.fiberInclusionMap_mem_source hb v
  have hev := e.apply_fiberInclusionMap hb v
  -- `L` is the derivative of `e`, an equivalence onto the tangent space of `B × F`.
  let L := he.mfderiv hv
  refine le_antisymm (TauCeti.range_mfderiv_le_ker_mfderiv_of_eventually_eq
    (.of_forall (e.proj_fiberInclusionMap hb))) fun u hu ↦ ⟨(L u).2, ?_⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    mfderiv_proj_apply hv (he.mdifferentiableAt hv)] at hu
  refine (mfderiv_fiberInclusionMap_apply hb v
    (he.mdifferentiableAt_symm (e.mem_target.2 hb : (b, v) ∈ e.target)) _).trans ?_
  conv_rhs => rw [← L.symm_apply_apply u]
  rw [he.coe_mfderiv_symm, he.coe_mfderiv, coe_coe, hev]
  exact congrArg _ (Prod.ext hu.symm rfl)

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

/-- The fibre coordinate `y ↦ (A.trivAt b y).2` of a chart of a `C^n` atlas is `C^n` on the
source of the chart. -/
theorem IsContMDiff.contMDiffOn_snd_trivAt (hA : A.IsContMDiff n IB IF IM) (b : B) :
    ContMDiffOn IM IF n (fun y ↦ (A.trivAt b y).2) (A.trivAt b).source :=
  contMDiff_snd.comp_contMDiffOn (hA.contMDiffOn_trivAt b)

/-- The fibre coordinate `y ↦ (A.trivAt b y).2` of a chart of a `C^n` atlas is `C^n` at every
point of `M` over the base set of the chart. -/
theorem IsContMDiff.contMDiffAt_snd_trivAt (hA : A.IsContMDiff n IB IF IM) {b : B} {x : M}
    (hx : proj x ∈ (A.trivAt b).baseSet) :
    ContMDiffAt IM IF n (fun y ↦ (A.trivAt b y).2) x :=
  (hA.contMDiffOn_snd_trivAt b).contMDiffAt
    ((A.trivAt b).open_source.mem_nhds ((A.trivAt b).mem_source.2 hx))

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
  (hA.contMDiff_proj.isSubmersionOfComplement_of_surjective_mfderiv hn fun x ↦
    TauCeti.isRegularPoint_iff.1 <| Bundle.Trivialization.isRegularPoint_proj
      (hA.mdifferentiable_trivAt (ne_of_gt (zero_lt_one.trans_le hn)) (proj x))
      ((A.trivAt (proj x)).mem_source.2 (A.mem_baseSet_trivAt (proj x)))).isSubmersion

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
