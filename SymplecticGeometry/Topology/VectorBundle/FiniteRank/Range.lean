/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.VectorBundle.ConstantRank
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
import SymplecticGeometry.Topology.VectorBundle.FiniteRank.Basic

/-!
# The range core of a bundle map of constant rank

Let `f : A ⟶ D` be a bundle map of real or complex finite-rank cores whose fibre maps all have
rank `r`. Their ranges `fiberRange f x` form a subbundle of `D`, and `range f hr` is the
finite-rank core of rank `r` presenting it, with fibres identified with these ranges by
`rangeFiberEquiv`. It comes with

* `rangeInclusion f hr : range f hr ⟶ D`, injective on every fibre, whose fibrewise image is the
  range of `f.fiberMap x` (`range_fiberMap_rangeInclusion`);
* `rangeLift f hr h hh : C ⟶ range f hr`, the factorization through the range core of a bundle
  map `h : C ⟶ D` with values in the ranges of `f`, with
  `rangeLift f hr h hh ≫ rangeInclusion f hr = h`;
* `rangeRestrict f hr : A ⟶ range f hr`, the corestriction of `f` (the lift of `f` itself),
  surjective on every fibre, with `rangeRestrict f hr ≫ rangeInclusion f hr = f`.

By the fibrewise criteria `mono_of_injective_fiberMap` and `epi_of_surjective_fiberMap`, the
inclusion is a monomorphism and the corestriction an epimorphism, so that Mathlib's `cancel_mono`
and `cancel_epi` apply to them.

For an idempotent endomorphism `P : E ⟶ E` (`P ≫ P = P`) of constant rank, `rangeRestrict P hr`
is the projection onto the range core: `rangeInclusion P hr ≫ rangeRestrict P hr = 𝟙 _`
(`rangeInclusion_rangeRestrict_of_comp_self`), while `rangeRestrict P hr ≫ rangeInclusion P hr = P`.

The range core commutes with pull-back along `g : C(X, B)`: `pullbackRangeIso f hr g` identifies
`(range f hr).pullback g` with the range core of `pullbackMap f g`. Its forward map is the lift of
the pulled-back inclusion, so it is compatible with the inclusions
(`pullbackRangeHom_rangeInclusion`) and with the corestrictions
(`pullbackMap_rangeRestrict_pullbackRangeHom`). It is invertible since it is bijective on every
fibre (Tau Ceti's `TauCeti.FiniteRankBundleCore.isIso_iff_bijective`).

The rank is a hypothesis: in general it is only locally constant, hence constant on a
preconnected base.

The ranges have continuous local frames by Tau Ceti's `TauCeti.hasLocalSubbundleFrames_range`,
applied to the fibre maps of `f`, a continuous section of the Hom bundle. Tau Ceti's
`TauCeti.HasLocalSubbundleFrames.vectorBundle` makes them a vector bundle with model `Fin r → 𝕜`,
for the topology `TauCeti.subbundleTopology` of a subspace of the total space of `D`, and
`TauCeti.FiniteRankBundleCore.ofBundle` presents that bundle as a core. Unlike Tau Ceti's
`TauCeti.rangeVectorBundle`, which concerns idempotents on a trivial bundle, this route needs no
embedding of `D` in a trivial bundle, and so no hypothesis on the base. The construction of the
core and of its inclusion follows that of Tau Ceti's `TauCeti.FiniteRankBundleCore.orthogonal`
and `TauCeti.FiniteRankBundleCore.orthogonalInclusion`.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1.
-/

public section

open Bundle CategoryTheory Function Module

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {A D : FiniteRankBundleCore 𝕜 B} (f : A ⟶ D)

/-- The range of the fibre map of `f` at `x`, as a subspace of the fibre of `D` at `x`. -/
def fiberRange (x : B) : Submodule 𝕜 (D.core.Fiber x) := (f.fiberMap x).range

theorem fiberRange_def (x : B) : fiberRange f x = (f.fiberMap x).range := (rfl)

@[simp] theorem mem_fiberRange_iff {x : B} {w : Fin D.rank → 𝕜} :
    w ∈ fiberRange f x ↔ ∃ v, f.fiberMap x v = w :=
  LinearMap.mem_range (f := (f.fiberMap x : (Fin A.rank → 𝕜) →ₗ[𝕜] (Fin D.rank → 𝕜)))

theorem fiberMap_mem_fiberRange (x : B) (v : Fin A.rank → 𝕜) :
    f.fiberMap x v ∈ fiberRange f x := (mem_fiberRange_iff f).2 ⟨v, rfl⟩

variable [CompleteSpace 𝕜] {r : ℕ} (hr : ∀ x, finrank 𝕜 (f.fiberMap x).range = r)

include hr

/-- The fibrewise ranges of a bundle map of constant rank `r` have continuous local frames with
`r` members near every point. -/
theorem hasLocalSubbundleFrames_fiberRange :
    HasLocalSubbundleFrames (Fin D.rank → 𝕜) (Fin r) (fiberRange f) :=
  hasLocalSubbundleFrames_range (F₁ := Fin A.rank → 𝕜) (E₁ := A.core.Fiber)
    f.continuous_fiberMap hr

variable [IsRCLikeNormedField 𝕜]

/-- The range of a bundle map `f : A ⟶ D` of constant rank `r`, as a finite-rank core of rank
`r`: the subbundle of `D` whose fibre at `x` is the range of `f.fiberMap x`, with the topology of
a subspace of the total space of `D`. -/
-- Expose the rank projection so that the fibre model reduces to `Fin r → 𝕜`.
@[expose, implicit_reducible]
noncomputable def range : FiniteRankBundleCore 𝕜 B :=
  letI := subbundleTopology (Fin D.rank → 𝕜) (F' := Fin r → 𝕜) (fiberRange f)
  letI := (hasLocalSubbundleFrames_fiberRange f hr).fiberBundle
  haveI := (hasLocalSubbundleFrames_fiberRange f hr).vectorBundle
  ofBundle 𝕜 r fun x ↦ fiberRange f x

@[simp] theorem rank_range : (range f hr).rank = r := (rfl)

/-- The fibre of `range f hr` at `x` is identified with the range of `f.fiberMap x`. -/
noncomputable def rangeFiberEquiv (x : B) : (range f hr).core.Fiber x ≃L[𝕜] fiberRange f x :=
  letI := subbundleTopology (Fin D.rank → 𝕜) (F' := Fin r → 𝕜) (fiberRange f)
  letI := (hasLocalSubbundleFrames_fiberRange f hr).fiberBundle
  haveI := (hasLocalSubbundleFrames_fiberRange f hr).vectorBundle
  pointIndexedCoreFiberEquiv 𝕜 (Fin r → 𝕜) (fun x ↦ fiberRange f x) x

/-- The identification `rangeFiberEquiv`, followed by the inclusion of the range in the fibre of
`D`, is continuous on total spaces. -/
theorem continuous_rangeFiberEquiv :
    Continuous fun p : (range f hr).core.TotalSpace ↦
      TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj
        (rangeFiberEquiv f hr p.proj p.snd : D.core.Fiber p.proj) :=
  letI := subbundleTopology (Fin D.rank → 𝕜) (F' := Fin r → 𝕜) (fiberRange f)
  letI := (hasLocalSubbundleFrames_fiberRange f hr).fiberBundle
  haveI := (hasLocalSubbundleFrames_fiberRange f hr).vectorBundle
  (isEmbedding_totalSpace_subbundle (Fin D.rank → 𝕜) (Fin r → 𝕜) (fiberRange f)).continuous.comp
    (pointIndexedCoreHomeomorph 𝕜 (Fin r → 𝕜) (fun x ↦ fiberRange f x)).continuous |>.congr fun p ↦
    congrArg (fun q : TotalSpace (Fin r → 𝕜) (fun x ↦ fiberRange f x) ↦
      (⟨q.proj, q.snd⟩ : D.core.TotalSpace)) (pointIndexedCoreHomeomorph_apply 𝕜 _ _ p)

/-- A continuous map into the total space of `D` whose values lie in the ranges of `f` lifts,
through the inverse of `rangeFiberEquiv`, to a continuous map into the total space of
`range f hr`. -/
theorem continuous_rangeFiberEquiv_symm {Z : Type*} [TopologicalSpace Z]
    {g : Z → D.core.TotalSpace} (hg : Continuous g)
    (hmem : ∀ z, (g z).snd ∈ fiberRange f (g z).proj) :
    Continuous fun z ↦ TotalSpace.mk' (Fin r → 𝕜) (E := (range f hr).core.Fiber) (g z).proj
      ((rangeFiberEquiv f hr (g z).proj).symm ⟨(g z).snd, hmem z⟩) := by
  let := subbundleTopology (Fin D.rank → 𝕜) (F' := Fin r → 𝕜) (fiberRange f)
  let := (hasLocalSubbundleFrames_fiberRange f hr).fiberBundle
  have := (hasLocalSubbundleFrames_fiberRange f hr).vectorBundle
  exact (pointIndexedCoreHomeomorph 𝕜 (Fin r → 𝕜) (fun x ↦ fiberRange f x)).symm.continuous.comp
    (f := fun z ↦
      (⟨(g z).proj, ⟨(g z).snd, hmem z⟩⟩ : TotalSpace (Fin r → 𝕜) fun x ↦ fiberRange f x))
    ((isEmbedding_totalSpace_subbundle (Fin D.rank → 𝕜) (Fin r → 𝕜) (fiberRange f)).continuous_iff.2
      hg) |>.congr fun z ↦ pointIndexedCoreHomeomorph_symm_apply 𝕜 _ _ _

/-- The inclusion of the range core of `f` into `D`. On the fibre at `x` it is the inclusion of
the range of `f.fiberMap x`, read through `rangeFiberEquiv`. -/
noncomputable def rangeInclusion : range f hr ⟶ D :=
  VectorBundleCore.CoordinateHom.ofContinuous
    (fun x ↦ (fiberRange f x).subtypeL.comp (rangeFiberEquiv f hr x).toContinuousLinearMap)
    ((continuous_hom_bundle_iff (E₁ := (range f hr).core.Fiber) (E₂ := D.core.Fiber) _).2
      (continuous_rangeFiberEquiv f hr))

@[simp] theorem fiberMap_rangeInclusion_apply (x : B) (v : Fin r → 𝕜) :
    (rangeInclusion f hr).fiberMap x v = (rangeFiberEquiv f hr x v : D.core.Fiber x) :=
  DFunLike.congr_fun (congrFun (VectorBundleCore.CoordinateHom.fiberMap_ofContinuous _ _) x) v

/-- A vector of the fibre of `range f hr`, read in the fibre of `D` through `rangeFiberEquiv`,
lies in the range of `f`. In simp normal form, this says that the inclusion of the range core
takes values in the ranges of `f`. -/
-- The membership is stated at the type `Fin D.rank → 𝕜` of the values of fibre maps, the form
-- that `simp` reaches from `(rangeInclusion f hr).fiberMap x v ∈ fiberRange f x`; at the type
-- `D.core.Fiber x`, `SetLike.coe_mem` would prove it and it would not fire on that goal.
@[simp] theorem coe_rangeFiberEquiv_mem_fiberRange (x : B) (v : Fin r → 𝕜) :
    @Membership.mem (Fin D.rank → 𝕜) (Submodule 𝕜 (D.core.Fiber x)) _ (fiberRange f x)
      (rangeFiberEquiv f hr x v : D.core.Fiber x) :=
  (rangeFiberEquiv f hr x v).property

section Lift

variable {C : FiniteRankBundleCore 𝕜 B} (h : C ⟶ D)
  (hh : ∀ x (v : Fin C.rank → 𝕜), h.fiberMap x v ∈ fiberRange f x)

/-- The lift through the range core of `f` of a bundle map `h : C ⟶ D` whose values lie in the
ranges of `f`. On the fibre at `x` the lift is `h.fiberMap x`, with values in the range of
`f.fiberMap x`, read through the inverse of `rangeFiberEquiv`. -/
noncomputable def rangeLift : C ⟶ range f hr :=
  VectorBundleCore.CoordinateHom.ofContinuous
    (fun x ↦ (rangeFiberEquiv f hr x).symm.toContinuousLinearMap.comp
      ((h.fiberMap x).codRestrict (fiberRange f x) (hh x)))
    ((continuous_hom_bundle_iff (E₁ := C.core.Fiber) (E₂ := (range f hr).core.Fiber) _).2
      (continuous_rangeFiberEquiv_symm f hr
        ((continuous_hom_bundle_iff (E₁ := C.core.Fiber) (E₂ := D.core.Fiber) _).1
          h.continuous_fiberMap) fun p ↦ hh p.proj p.snd))

theorem fiberMap_rangeLift (x : B) :
    (rangeLift f hr h hh).fiberMap x = (rangeFiberEquiv f hr x).symm.toContinuousLinearMap.comp
      ((h.fiberMap x).codRestrict (fiberRange f x) (hh x)) :=
  congrFun (VectorBundleCore.CoordinateHom.fiberMap_ofContinuous _ _) x

@[simp] theorem rangeFiberEquiv_fiberMap_rangeLift_apply (x : B) (v : Fin C.rank → 𝕜) :
    rangeFiberEquiv f hr x ((rangeLift f hr h hh).fiberMap x v) = ⟨h.fiberMap x v, hh x v⟩ :=
  (congrArg (rangeFiberEquiv f hr x) (DFunLike.congr_fun (fiberMap_rangeLift f hr h hh x) v)).trans
    ((rangeFiberEquiv f hr x).apply_symm_apply _)

/-- The lift of `h` through the range core of `f`, followed by the inclusion, is `h`. -/
@[reassoc (attr := simp)]
theorem rangeLift_rangeInclusion : rangeLift f hr h hh ≫ rangeInclusion f hr = h :=
  hom_ext fun x ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [fiberMap_comp, ContinuousLinearMap.comp_apply, fiberMap_rangeInclusion_apply,
      rangeFiberEquiv_fiberMap_rangeLift_apply]

end Lift

/-- The corestriction of `f` to its range core. On the fibre at `x` it is `f.fiberMap x`, with
values in its range, read through the inverse of `rangeFiberEquiv`. -/
noncomputable def rangeRestrict : A ⟶ range f hr :=
  rangeLift f hr f (fiberMap_mem_fiberRange f)

theorem rangeRestrict_def : rangeRestrict f hr = rangeLift f hr f (fiberMap_mem_fiberRange f) :=
  (rfl)

theorem fiberMap_rangeRestrict (x : B) :
    (rangeRestrict f hr).fiberMap x = (rangeFiberEquiv f hr x).symm.toContinuousLinearMap.comp
      ((f.fiberMap x).codRestrict (fiberRange f x) (fiberMap_mem_fiberRange f x)) := by
  rw [rangeRestrict_def, fiberMap_rangeLift]

@[simp] theorem rangeFiberEquiv_fiberMap_rangeRestrict_apply (x : B) (v : Fin A.rank → 𝕜) :
    rangeFiberEquiv f hr x ((rangeRestrict f hr).fiberMap x v) =
      ⟨f.fiberMap x v, fiberMap_mem_fiberRange f x v⟩ := by
  rw [rangeRestrict_def, rangeFiberEquiv_fiberMap_rangeLift_apply]

/-- `f` factors through its range core: it is its corestriction followed by the inclusion. -/
@[reassoc (attr := simp)]
theorem rangeRestrict_rangeInclusion : rangeRestrict f hr ≫ rangeInclusion f hr = f :=
  rangeLift_rangeInclusion f hr f (fiberMap_mem_fiberRange f)

/-- The inclusion of the range core is injective on every fibre. -/
theorem fiberMap_rangeInclusion_injective (x : B) :
    Injective ((rangeInclusion f hr).fiberMap x) := fun v w h ↦ by
  rw [fiberMap_rangeInclusion_apply, fiberMap_rangeInclusion_apply] at h
  exact (rangeFiberEquiv f hr x).injective (Subtype.ext h)

/-- The corestriction of `f` to its range core is surjective on every fibre. -/
theorem fiberMap_rangeRestrict_surjective (x : B) :
    Surjective ((rangeRestrict f hr).fiberMap x) := fun w ↦ by
  obtain ⟨v, hv⟩ := ((rangeFiberEquiv f hr x) w).property
  refine ⟨v, (rangeFiberEquiv f hr x).injective (Subtype.ext ?_)⟩
  rw [rangeFiberEquiv_fiberMap_rangeRestrict_apply]
  exact hv

instance : Mono (rangeInclusion f hr) :=
  mono_of_injective_fiberMap _ (fiberMap_rangeInclusion_injective f hr)

instance : Epi (rangeRestrict f hr) :=
  epi_of_surjective_fiberMap _ (fiberMap_rangeRestrict_surjective f hr)

/-- The fibrewise image of the inclusion of the range core of `f` is the range of `f`. -/
theorem range_fiberMap_rangeInclusion (x : B) :
    ((rangeInclusion f hr).fiberMap x).range = (f.fiberMap x).range := by
  conv_rhs => rw [← rangeRestrict_rangeInclusion f hr, fiberMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (fiberMap_rangeRestrict_surjective f hr x))]

/-- A vector of the fibre of `D` lies in the image of the inclusion of the range core of `f`
exactly when it lies in the range of `f`. -/
theorem mem_range_fiberMap_rangeInclusion_iff (x : B) (w : Fin D.rank → 𝕜) :
    w ∈ ((rangeInclusion f hr).fiberMap x).range ↔ ∃ v, f.fiberMap x v = w := by
  rw [range_fiberMap_rangeInclusion]
  exact LinearMap.mem_range

omit hr

section Idempotent

variable {E : FiniteRankBundleCore 𝕜 B} {P : E ⟶ E} (hr : ∀ x, finrank 𝕜 (P.fiberMap x).range = r)
  (hP : P ≫ P = P)

include hP

/-- An idempotent endomorphism `P` fixes its range: the inclusion of its range core followed by `P`
is the inclusion. -/
@[reassoc (attr := simp)]
theorem rangeInclusion_comp_of_comp_self : rangeInclusion P hr ≫ P = rangeInclusion P hr :=
  (cancel_epi (rangeRestrict P hr)).1 <| by
    rw [rangeRestrict_rangeInclusion_assoc, hP, rangeRestrict_rangeInclusion]

/-- For an idempotent endomorphism `P`, the corestriction `rangeRestrict P hr` is a projection onto
the range core: it is a left inverse of the inclusion. -/
@[reassoc (attr := simp)]
theorem rangeInclusion_rangeRestrict_of_comp_self :
    rangeInclusion P hr ≫ rangeRestrict P hr = 𝟙 _ :=
  (cancel_mono (rangeInclusion P hr)).1 <| by
    rw [Category.assoc, rangeRestrict_rangeInclusion, rangeInclusion_comp_of_comp_self hr hP,
      Category.id_comp]

end Idempotent

section Pullback

variable {X : Type*} [TopologicalSpace X] (g : C(X, B))

include hr

omit [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] in
/-- The pull-back of a bundle map of constant rank `r` has constant rank `r`. -/
theorem finrank_range_fiberMap_pullbackMap (x : X) :
    finrank 𝕜 ((pullbackMap f g).fiberMap x).range = r := by
  rw [fiberMap_pullbackMap]
  exact hr (g x)

/-- The pulled-back inclusion of the range core of `f` takes values in the ranges of the
pulled-back map. -/
theorem fiberMap_pullbackMap_rangeInclusion_mem_fiberRange (x : X) (v : Fin r → 𝕜) :
    (pullbackMap (rangeInclusion f hr) g).fiberMap x v ∈ fiberRange (pullbackMap f g) x := by
  rw [mem_fiberRange_iff, fiberMap_pullbackMap, fiberMap_pullbackMap]
  exact (mem_range_fiberMap_rangeInclusion_iff f hr (g x) _).1 ⟨v, rfl⟩

/-- The comparison map from the pull-back of the range core of `f` to the range core of the
pull-back of `f`: the pulled-back inclusion, with values in the ranges of the pulled-back map. -/
noncomputable def pullbackRangeHom :
    (range f hr).pullback g ⟶ range (pullbackMap f g) (finrank_range_fiberMap_pullbackMap f hr g) :=
  rangeLift _ _ (pullbackMap (rangeInclusion f hr) g)
    (fiberMap_pullbackMap_rangeInclusion_mem_fiberRange f hr g)

theorem pullbackRangeHom_def : pullbackRangeHom f hr g = rangeLift _ _
    (pullbackMap (rangeInclusion f hr) g)
    (fiberMap_pullbackMap_rangeInclusion_mem_fiberRange f hr g) := (rfl)

/-- The comparison map, followed by the inclusion of the range core of the pulled-back map, is
the pull-back of the inclusion of the range core of `f`. -/
@[reassoc (attr := simp)]
theorem pullbackRangeHom_rangeInclusion :
    pullbackRangeHom f hr g ≫ rangeInclusion (pullbackMap f g) _ =
      pullbackMap (rangeInclusion f hr) g := by
  rw [pullbackRangeHom_def, rangeLift_rangeInclusion]

/-- The comparison map carries the pulled-back corestriction of `f` to the corestriction of the
pulled-back map. -/
@[reassoc (attr := simp)]
theorem pullbackMap_rangeRestrict_pullbackRangeHom :
    pullbackMap (rangeRestrict f hr) g ≫ pullbackRangeHom f hr g =
      rangeRestrict (pullbackMap f g) (finrank_range_fiberMap_pullbackMap f hr g) :=
  (cancel_mono (rangeInclusion (pullbackMap f g) _)).1 <| by
    rw [Category.assoc, pullbackRangeHom_rangeInclusion, ← pullbackMap_comp,
      rangeRestrict_rangeInclusion, rangeRestrict_rangeInclusion]

/-- The comparison map is bijective on every fibre. -/
theorem fiberMap_pullbackRangeHom_bijective (x : X) :
    Bijective ((pullbackRangeHom f hr g).fiberMap x) := by
  have hi : Injective ((pullbackRangeHom f hr g).fiberMap x) := fun v w hvw ↦
    fiberMap_rangeInclusion_injective f hr (g x) <| by
      have h := congrArg (fun u ↦ (rangeInclusion (pullbackMap f g) _).fiberMap x u) hvw
      simpa only [← ContinuousLinearMap.comp_apply, ← fiberMap_comp,
        pullbackRangeHom_rangeInclusion, fiberMap_pullbackMap] using h
  -- Both fibres are `Fin r → 𝕜`, so their finranks agree by `rfl`.
  exact ⟨hi, LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := ((pullbackRangeHom f hr g).fiberMap x).toLinearMap) rfl |>.1 hi⟩

/-- The range core commutes with pull-back: the pull-back along `g` of the range core of `f` is
isomorphic to the range core of the pull-back of `f`, by the comparison map
`pullbackRangeHom`. -/
noncomputable def pullbackRangeIso :
    (range f hr).pullback g ≅ range (pullbackMap f g) (finrank_range_fiberMap_pullbackMap f hr g) :=
  haveI := (isIso_iff_bijective _).2 (fiberMap_pullbackRangeHom_bijective f hr g)
  asIso (pullbackRangeHom f hr g)

@[simp] theorem pullbackRangeIso_hom : (pullbackRangeIso f hr g).hom = pullbackRangeHom f hr g :=
  (rfl)

/-- The inverse of `pullbackRangeIso`, followed by the pulled-back inclusion of the range core of
`f`, is the inclusion of the range core of the pulled-back map. -/
@[reassoc (attr := simp)]
theorem pullbackRangeIso_inv_pullbackMap_rangeInclusion :
    (pullbackRangeIso f hr g).inv ≫ pullbackMap (rangeInclusion f hr) g =
      rangeInclusion (pullbackMap f g) _ := by
  rw [Iso.inv_comp_eq, pullbackRangeIso_hom, pullbackRangeHom_rangeInclusion]

/-- The corestriction of the pulled-back map, followed by the inverse of `pullbackRangeIso`, is
the pull-back of the corestriction of `f`. -/
@[reassoc (attr := simp)]
theorem rangeRestrict_pullbackRangeIso_inv :
    rangeRestrict (pullbackMap f g) (finrank_range_fiberMap_pullbackMap f hr g) ≫
      (pullbackRangeIso f hr g).inv = pullbackMap (rangeRestrict f hr) g := by
  rw [Iso.comp_inv_eq, pullbackRangeIso_hom, pullbackMap_rangeRestrict_pullbackRangeHom]

end Pullback

end TauCeti.FiniteRankBundleCore

end
