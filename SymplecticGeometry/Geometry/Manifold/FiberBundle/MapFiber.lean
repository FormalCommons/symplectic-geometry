/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import SymplecticGeometry.Topology.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Smooth atlases of a map, read pointwise

Let `proj : M → B` be a map between manifolds and `e` a trivialization of `proj` with model
fibre `F`. When `e` and its inverse are smooth, the fibre of `proj` over a point `b` of the base
set of `e`, read through `e` (`Bundle.Trivialization.fiberInclusionMap`), is a smooth map
`F → M` whose derivative is injective with image the vertical space, the kernel of the derivative
of `proj`. The coordinate change between two such trivializations over `b` is a diffeomorphism of
`F`. For Tau Ceti's smooth atlases of a map (`TauCeti.MapFiber.Atlas.IsContMDiff`) this says that
`proj` is a submersion. Conversely, every smooth fibre bundle gives a smooth atlas of the
projection of its charted total space.

## Main definitions

* `Bundle.Trivialization.coordChangeDiffeomorph`: the coordinate change between two smooth
  trivializations over a point of both base sets, as a diffeomorphism of the model fibre.
* `TauCeti.ManifoldTotalSpace.mapFiberAtlas`: the atlas of the projection of the charted total
  space of a fibre bundle, made of the bundle's trivializations.

## Main results

* `Bundle.Trivialization.contMDiff_fiberInclusionMap`: the fibre inclusion of a trivialization with
  smooth inverse is smooth.
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
inclusion is computed with Tau Ceti's
`TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv`. The proof that a coordinate change is
smooth, as the fibre coordinate of one trivialization after the inverse of the other, follows that
of Tau Ceti's `TauCeti.MapFiber.Atlas.contMDiffFiberBundle`.

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
  rw [show ⇑(e.fiberInclusionMap hb) = fun v ↦ e.toOpenPartialHomeomorph.symm (b, v) from
    funext (e.fiberInclusionMap_apply hb)]
  exact he.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) fun _ ↦ e.mem_target.2 hb

variable {e}

/-- A trivialization that is differentiable with differentiable inverse makes `proj` regular at
every point of its source: near such a point, `proj` is the first coordinate of `e`, whose
derivative is invertible. -/
theorem isRegularPoint_proj (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF))
    {x : M} (hx : x ∈ e.source) : TauCeti.IsRegularPoint IM IB proj x := by
  rw [TauCeti.isRegularPoint_iff, (e.coe_fst_eventuallyEq_proj hx).symm.mfderiv_eq,
    ContinuousLinearMap.coe_comp,
    mfderiv_comp (f := (e : M → B × F)) x mdifferentiableAt_fst (he.mdifferentiableAt hx),
    mfderiv_fst]
  exact (tangentSpaceCast IB _ _).surjective.comp
    (Prod.fst_surjective.comp (he.mfderiv_surjective hx))

/-- The fibre inclusion of a trivialization that is differentiable with differentiable inverse is
differentiable. -/
theorem mdifferentiable_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet) :
    MDifferentiable IF IM (e.fiberInclusionMap hb) := fun v ↦ by
  rw [show ⇑(e.fiberInclusionMap hb) = fun v ↦ e.toOpenPartialHomeomorph.symm (b, v) from
    funext (e.fiberInclusionMap_apply hb)]
  exact (he.mdifferentiableAt_symm (e.mem_target.2 hb)).comp v
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id)

/-- The fibre inclusion of a trivialization that is differentiable with differentiable inverse has
injective derivative: the fibre coordinate of `e` is a left inverse of it. -/
theorem injective_mfderiv_fiberInclusionMap
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) : Injective (mfderiv IF IM (e.fiberInclusionMap hb) v) := by
  have hv : e.fiberInclusionMap hb v ∈ e.source :=
    e.mem_source.2 ((e.proj_fiberInclusionMap hb v).symm ▸ hb)
  refine TauCeti.mfderiv_injective_of_leftInverse (g := fun x ↦ (e x).2)
    (mdifferentiableAt_snd.comp _ (he.mdifferentiableAt hv))
    (mdifferentiable_fiberInclusionMap he hb v) fun w ↦ ?_
  rw [fiberInclusionMap_apply]
  exact congrArg Prod.snd (e.apply_symm_apply' hb)

/-- **The tangent spaces of a fibre.** For a trivialization `e` of `proj` that is differentiable
with differentiable inverse, the derivative of the fibre inclusion over `b` at `v` has as range
the vertical space at its image, the kernel of the derivative of `proj` there. -/
theorem range_mfderiv_fiberInclusionMap [FiniteDimensional 𝕜 EM]
    (he : e.toOpenPartialHomeomorph.MDifferentiable IM (IB.prod IF)) (hb : b ∈ e.baseSet)
    (v : F) :
    (mfderiv IF IM (e.fiberInclusionMap hb) v).range =
      (mfderiv IM IB proj (e.fiberInclusionMap hb v)).ker := by
  have hv : e.fiberInclusionMap hb v ∈ e.source :=
    e.mem_source.2 ((e.proj_fiberInclusionMap hb v).symm ▸ hb)
  -- The derivative of `e` identifies `EM` with `EB × EF`, which fixes the dimensions.
  let L : EM ≃ₗ[𝕜] EB × EF := (he.mfderiv hv).toLinearEquiv
  have : FiniteDimensional 𝕜 (EB × EF) := L.finiteDimensional
  have : FiniteDimensional 𝕜 EB :=
    Module.Finite.of_surjective (LinearMap.fst 𝕜 EB EF) Prod.fst_surjective
  have : FiniteDimensional 𝕜 EF :=
    Module.Finite.of_surjective (LinearMap.snd 𝕜 EB EF) Prod.snd_surjective
  refine TauCeti.IsRegularPoint.range_mfderiv_eq_ker_mfderiv
    (.of_forall (e.proj_fiberInclusionMap hb)) (isRegularPoint_proj he hv)
    (injective_mfderiv_fiberInclusionMap he hb v) ?_
  rw [L.finrank_eq, Module.finrank_prod, add_comm]

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
