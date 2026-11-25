/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.Embedding
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Comap

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The normal bundle of the zero set of a transverse section

Let `s` be a `C^m` section, `m ≠ 0`, of a vector bundle `E' → X` with model fibre `F'`,
transverse to the zero section, and let `f = TauCeti.SmoothEmbedding.ofTransverseSection` be the
inclusion of its zero set `Z`. At `z ∈ Z` the linearization `L_z = D s(z) : T_z X → E'_z` is onto
and its kernel is the tangent space of `Z`
(`SymplecticGeometry.range_mfderiv_coe_transverseZeroSet`), so it descends to an isomorphism
from the normal space of `f` at `z` onto the fibre `E'_z`. These
isomorphisms form an isomorphism of the normal bundle of `Z` with the restriction of `E'` to `Z`:
their total-space map into `E'` is continuous. In this form, a family of fibrewise continuous
linear equivalences over the continuous map `f` with continuous total-space map, they are what
Tau Ceti's `TauCeti.thomPairMapOfFiberwise` and `TauCeti.VectorBundleOrientation.comap` take.
Over the reals, an orientation `o'` of `E'` is carried along them to a normal orientation of `Z`.

The fibrewise isomorphism is Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceEquivOfKer` for the
linearization read in the preferred trivialization of `E'`; it is the analogue for zero sets of
sections of Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel` for level sets.

## Main declarations

* `SymplecticGeometry.tangentRange_ofTransverseSection`: the tangent range of the zero set at `z`
  is the kernel of `L_z`.
* `SymplecticGeometry.normalSpaceEquivOfTransverseSection`: the isomorphism of the normal space
  of the zero set at `z` with `E'_z`, sending the normal class of `v` to `L_z v`
  (`SymplecticGeometry.normalSpaceEquivOfTransverseSection_normalClass`).
* `SymplecticGeometry.continuous_normalSpaceEquivOfTransverseSection`: its total-space map into
  `E'` is continuous for the quotient topology of the normal bundle.
* `SymplecticGeometry.normalOrientationOfSection`: for real bundles, the orientation of the
  normal bundle of the zero set carried from an orientation `o'` of `E'`, characterized by
  `SymplecticGeometry.map_normalOrientationOfSection_apply`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold Topology

open TauCeti

namespace SymplecticGeometry

open SmoothEmbedding

section Equiv

variable {𝕜 V G X F' E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [TopologicalSpace G] {J : ModelWithCorners 𝕜 V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, AddCommGroup (E' x)]
  [∀ x, Module 𝕜 (E' x)] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle 𝕜 F' E']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {m : ℕ∞ω} [IsManifold J m X] [ContMDiffVectorBundle m F' E' J] {s : ∀ x, E' x}

variable (hm : m ≠ 0) (hsm : ContMDiff J (J.prod 𝓘(𝕜, F')) m fun x ↦ TotalSpace.mk' F' x (s x))
  (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x))
  (hE : finrank 𝕜 E + finrank 𝕜 F' = finrank 𝕜 V)

/-- A point of the zero set of a transverse section is a zero of the section. -/
theorem ofTransverseSection_apply_eq_zero (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    s (ofTransverseSection hm hsm hs hE z) = 0 := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have h := mem_range_self (f := ofTransverseSection hm hsm hs hE) z
  rwa [range_ofTransverseSection] at h

/-- **The tangent space of the zero set as a kernel.** The tangent range of the inclusion of the
zero set of a transverse section at `z` is the kernel of the linearization of `s` at `z`. -/
theorem tangentRange_ofTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).tangentRange z hm =
      (sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z)).ker := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  -- `range_mfderiv_coe_transverseZeroSet` is stated for `Subtype.val`, the coercion of `f`.
  have key : ∀ g : ↥{x : X | s x = 0} → X, g = Subtype.val →
      (mfderiv 𝓘(𝕜, E) J g z).range = (sectionLinearization (F := F') J _root_.id s (g z)).ker := by
    rintro g rfl
    exact range_mfderiv_coe_transverseZeroSet hm hsm hs hE z
  ext v
  rw [mem_tangentRange_iff, ← key _ (coe_ofTransverseSection hm hsm hs hE), LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]

/-- **The normal space of the zero set of a transverse section.** At a point `z` of the zero set
of a transverse section `s`, the linearization of `s` at `z` descends to a continuous linear
equivalence from the normal space of the zero set at `z` onto the fibre of `E'` at `z`
(`SymplecticGeometry.normalSpaceEquivOfTransverseSection_normalClass`). -/
noncomputable def normalSpaceEquivOfTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).NormalSpace z hm ≃L[𝕜]
      E' (ofTransverseSection hm hsm hs hE z) :=
  letI := transverseZeroSetChartedSpace hm hsm hs hE
  let f := ofTransverseSection hm hsm hs hE
  let e := (trivializationAt F' E' (f z)).continuousLinearEquivAt 𝕜 (f z)
    (mem_baseSet_trivializationAt F' E' (f z))
  (f.normalSpaceEquivOfKer z hm
    ((e : E' (f z) →L[𝕜] F').comp (sectionLinearization (F := F') J _root_.id s (f z)))
    (fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.map_eq_zero_iff,
        tangentRange_ofTransverseSection hm hsm hs hE z, LinearMap.mem_ker,
        ContinuousLinearMap.coe_coe])
    (by
      have h := f.finrank_normalSpace z hm
      have hV : finrank 𝕜 (TangentSpace J (f z)) = finrank 𝕜 V := rfl
      have hE' : finrank 𝕜 (TangentSpace 𝓘(𝕜, E) z) = finrank 𝕜 E := rfl
      omega)).trans e.symm

/-- The normal-space equivalence of a transverse section sends the normal class of an ambient
tangent vector `v` at `z` to the linearization of `s` at `z` applied to `v`. -/
@[simp]
theorem normalSpaceEquivOfTransverseSection_normalClass (z : ↥{x : X | s x = 0})
    (v : TangentSpace J (ofTransverseSection hm hsm hs hE z)) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    normalSpaceEquivOfTransverseSection hm hsm hs hE z
        ((ofTransverseSection hm hsm hs hE).normalClass z hm v) =
      sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z) v := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [normalSpaceEquivOfTransverseSection, ContinuousLinearEquiv.trans_apply,
    normalSpaceEquivOfKer_normalClass, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse of the normal-space equivalence of a transverse section sends the linearization
of `s` at `z` applied to `v` to the normal class of `v`. -/
@[simp]
theorem normalSpaceEquivOfTransverseSection_symm_apply (z : ↥{x : X | s x = 0})
    (v : TangentSpace J (ofTransverseSection hm hsm hs hE z)) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (normalSpaceEquivOfTransverseSection hm hsm hs hE z).symm
        (sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z) v) =
      (ofTransverseSection hm hsm hs hE).normalClass z hm v := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceEquivOfTransverseSection_normalClass]

/-- **The normal bundle of the zero set is the restriction of the bundle.** The total-space map
`(z, ν) ↦ (z, φ_z ν)` of the normal-space equivalences `φ_z` of a transverse section, over the
inclusion of the zero set, from the normal bundle of the zero set, with its quotient topology, to
`E'`, is continuous. Together with
the fibrewise equivalences, this is the input of `TauCeti.thomPairMapOfFiberwise` and
`TauCeti.VectorBundleOrientation.comap` over the inclusion of the zero set. -/
theorem continuous_normalSpaceEquivOfTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    Continuous fun v : TotalSpace F' fun z ↦ (ofTransverseSection hm hsm hs hE).NormalSpace z hm ↦
      TotalSpace.mk' F' (ofTransverseSection hm hsm hs hE v.proj)
        (normalSpaceEquivOfTransverseSection hm hsm hs hE v.proj v.snd) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  set f := ofTransverseSection hm hsm hs hE
  rw [f.continuous_normalBundle_iff hm]
  -- On an ambient representative `(z, v)` the map is `(z, L_z v)`.
  have hrep : (fun v : TotalSpace F' fun z ↦ f.NormalSpace z hm ↦ TotalSpace.mk' F' (f v.proj)
      (normalSpaceEquivOfTransverseSection hm hsm hs hE v.proj v.snd)) ∘ f.normalQuotientMap hm =
      fun p ↦ TotalSpace.mk' F' (f p.proj)
        (sectionLinearization (F := F') J _root_.id s (f p.proj) p.snd) := by
    funext p
    rw [comp_apply, normalQuotientMap_apply]
    exact congrArg (TotalSpace.mk' F' (f p.proj))
      (normalSpaceEquivOfTransverseSection_normalClass hm hsm hs hE p.proj p.snd)
  rw [hrep, continuous_iff_continuousAt]
  intro p₀
  have hproj : Continuous fun p : TotalSpace V ((f : _ → X) *ᵖ (TangentSpace J)) ↦ f p.proj :=
    (map_continuous f).comp (Pullback.continuous_proj V (TangentSpace J) f)
  refine (FiberBundle.continuousAt_totalSpace F' _).2 ⟨hproj.continuousAt, ?_⟩
  set e := trivializationAt F' E' (f p₀.proj)
  -- In `e`, the fibre coordinate of `L_x v` is the derivative at `x` of the fibre coordinate `g`
  -- of `s`, a `C^m` function on the base set of `e`.
  set g : X → F' := fun y ↦ (e ⟨y, s y⟩).2
  have hg (x : X) (hx : x ∈ e.baseSet) : ContMDiffAt J 𝓘(𝕜, F') m g x :=
    ((e.contMDiffAt_iff (f := fun y ↦ TotalSpace.mk' F' y (s y)) (e.mem_source.2 hx)).1
      (hsm x)).2
  have key (z : ↥{x : X | s x = 0}) (hz : f z ∈ e.baseSet) (w : TangentSpace J (f z)) :
      (e (TotalSpace.mk' F' (f z) (sectionLinearization (F := F') J _root_.id s (f z) w))).2 =
        mfderiv J 𝓘(𝕜, F') g (f z) w := by
    have hL := DFunLike.congr_fun (continuousLinearMapAt_comp_sectionLinearization
      (b := _root_.id) (s := s) continuousAt_id hz ((hg _ hz).mdifferentiableAt hm)
      (ofTransverseSection_apply_eq_zero hm hsm hs hE z)) w
    rwa [ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_apply_of_mem 𝕜 (b := _root_.id (f z)) hz, mvfderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply] at hL
  have heq : (fun p : TotalSpace V ((f : _ → X) *ᵖ (TangentSpace J)) ↦ (e (TotalSpace.mk' F'
      (f p.proj) (sectionLinearization (F := F') J _root_.id s (f p.proj) p.snd))).2) =ᶠ[𝓝 p₀]
      fun p ↦ (tangentMap J 𝓘(𝕜, F') g (Pullback.lift f p)).snd := by
    filter_upwards [(e.open_baseSet.preimage hproj).mem_nhds
      (mem_baseSet_trivializationAt F' E' (f p₀.proj))] with p hp
    exact (key p.proj hp p.snd).trans tangentMap_snd.symm
  refine ContinuousAt.congr ?_ heq.symm
  have hsnd : Continuous fun q : TangentBundle 𝓘(𝕜, F') F' ↦ q.snd := by
    have h := continuous_snd.comp (tangentBundleModelSpaceHomeomorph 𝓘(𝕜, F')).continuous
    rw [tangentBundleModelSpaceHomeomorph_coe] at h
    exact h
  exact hsnd.continuousAt.comp
    (((hg _ (mem_baseSet_trivializationAt F' E' _)).continuousAt_tangentMap
    (ENat.one_le_iff_ne_zero_withTop.mpr hm)).comp (Pullback.continuous_lift V _ _).continuousAt)

end Equiv

section Orientation

variable {V G X F' E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace G X]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : X → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ x, AddCommGroup (E' x)]
  [∀ x, Module ℝ (E' x)] [∀ x, TopologicalSpace (E' x)] [FiberBundle F' E']
  [VectorBundle ℝ F' E']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ∞ω} [IsManifold J m X] [ContMDiffVectorBundle m F' E' J] {s : ∀ x, E' x}
  (hm : m ≠ 0) (hsm : ContMDiff J (J.prod 𝓘(ℝ, F')) m fun x ↦ TotalSpace.mk' F' x (s x))
  (hs : ∀ x, s x = 0 → Surjective (sectionLinearization (F := F') J _root_.id s x))
  (hE : finrank ℝ E + finrank ℝ F' = finrank ℝ V)
  {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F')

/-- **The normal orientation of the zero set of a transverse section.** For a real vector bundle
`E'` with an orientation `o'` and a transverse section `s`, the orientation of the normal bundle
of the zero set (with model fibre `F'`) whose fibre at `z` is carried by the normal-space
equivalence `SymplecticGeometry.normalSpaceEquivOfTransverseSection` to `o'` at `z`
(`SymplecticGeometry.map_normalOrientationOfSection_apply`). -/
noncomputable def normalOrientationOfSection (o' : VectorBundleOrientation F' E' ι) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
      .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    VectorBundleOrientation F' (fun z ↦ (ofTransverseSection hm hsm hs hE).NormalSpace z hm) ι :=
  letI := transverseZeroSetChartedSpace hm hsm hs hE
  haveI := isManifold_transverseZeroSet hm hsm hs hE
  haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  o'.comap (g := (ofTransverseSection hm hsm hs hE).toContinuousMap) hι
    (continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE)

/-- The normal-space equivalence of a transverse section carries the normal orientation
`SymplecticGeometry.normalOrientationOfSection` at `z` to the orientation `o'` at `z`. -/
@[simp]
theorem map_normalOrientationOfSection_apply (o' : VectorBundleOrientation F' E' ι)
    (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
      .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    Orientation.map ι (normalSpaceEquivOfTransverseSection hm hsm hs hE z).toLinearEquiv
        (normalOrientationOfSection hm hsm hs hE hι o' z) =
      o' (ofTransverseSection hm hsm hs hE z) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  have := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  exact VectorBundleOrientation.map_comap_apply
    (g := (ofTransverseSection hm hsm hs hE).toContinuousMap)
    hι o'
    (continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE) z

/-- Reversing the orientation of `E'` reverses the normal orientation of the zero set. -/
@[simp]
theorem normalOrientationOfSection_neg (o' : VectorBundleOrientation F' E' ι) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
      .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    normalOrientationOfSection hm hsm hs hE hι (-o') =
      -normalOrientationOfSection hm hsm hs hE hι o' := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  have := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  exact VectorBundleOrientation.comap_neg hι o'
    (continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE)

end Orientation

end SymplecticGeometry

end
