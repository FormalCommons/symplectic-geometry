/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Orientation.NormalOrientation
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ZeroSet.Embedding
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Comap

import SymplecticGeometry.Geometry.Manifold.VectorBundle.Section.Linearization

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

The fibrewise isomorphism is Tau Ceti's `Manifold.IsImmersion.normalSpaceEquivOfKer` for the
linearization read in the preferred trivialization of `E'`; it is the analogue for zero sets of
sections of Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceEquivOfLevel` for level sets.
Its continuity is `SymplecticGeometry.continuous_sectionLinearization_pullback`, read through the
quotient map of the normal bundle.

The orientation `SymplecticGeometry.normalOrientationOfSection` and its two lemmas,
`SymplecticGeometry.map_normalOrientationOfSection_apply` and
`SymplecticGeometry.normalOrientationOfSection_neg`, follow Tau Ceti's
`TauCeti.SmoothEmbedding.diagonalNormalOrientation`,
`TauCeti.SmoothEmbedding.diagonalNormalOrientation_map` and
`TauCeti.SmoothEmbedding.diagonalNormalOrientation_neg`: the normal bundle structure of Tau Ceti's
`normalSpaceFiberBundle` and `normalSpaceVectorBundle` is installed in the statement, and the
orientation is pulled back by `TauCeti.VectorBundleOrientation.comap`.

## Main declarations

* `TauCeti.SmoothEmbedding.tangentRange_ofTransverseSection`: the tangent range of the zero set
  at `z` is the kernel of `L_z`.
* `SymplecticGeometry.tangentSpaceEquivKerOfTransverseSection`: the differential of the inclusion,
  as an isomorphism of the tangent space of the zero set at `z` with the kernel of `L_z`.
* `SymplecticGeometry.normalSpaceEquivOfTransverseSection`: the isomorphism of the normal space
  of the zero set at `z` with `E'_z`, sending the normal class of `v` to `L_z v`
  (`SymplecticGeometry.normalSpaceEquivOfTransverseSection_normalClass`).
* `SymplecticGeometry.continuous_normalSpaceEquivOfTransverseSection`: its total-space map into
  `E'` is continuous for the quotient topology of the normal bundle.
* `SymplecticGeometry.normalOrientationOfSection`: for real bundles, the orientation of the
  normal bundle of the zero set carried from an orientation `o'` of `E'`, characterized by
  `SymplecticGeometry.map_normalOrientationOfSection_apply`.
* `SymplecticGeometry.normalOrientation_ofTransverseSection_eq_normalOrientationOfSection_iff`:
  the normal orientation induced by orientations of `X` and of the zero set is
  `normalOrientationOfSection o'` exactly when, at each `z`, the orientation of the zero set
  carried to `ker L_z`, followed by `o'` at `z`, gives the orientation of `X`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold Topology

open TauCeti

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

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry

/-- **The tangent space of the zero set as a kernel.** The tangent range of the inclusion of the
zero set of a transverse section at `z` is the kernel of the linearization of `s` at `z`. -/
theorem tangentRange_ofTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).isImmersion.tangentRange z hm =
      (sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z)).ker := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  -- `range_mfderiv_coe_transverseZeroSet` is stated for `Subtype.val`, the coercion of `f`.
  have key : ∀ g : ↥{x : X | s x = 0} → X, g = Subtype.val →
      (mfderiv 𝓘(𝕜, E) J g z).range = (sectionLinearization (F := F') J _root_.id s (g z)).ker := by
    rintro g rfl
    exact range_mfderiv_coe_transverseZeroSet hm hsm hs hE z
  ext v
  rw [Manifold.IsImmersion.mem_tangentRange_iff, ← key _ (coe_ofTransverseSection hm hsm hs hE),
      LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]

end TauCeti.SmoothEmbedding

namespace SymplecticGeometry

open SmoothEmbedding

/-- **The normal space of the zero set of a transverse section.** At a point `z` of the zero set
of a transverse section `s`, the linearization of `s` at `z` descends to a continuous linear
equivalence from the normal space of the zero set at `z` onto the fibre of `E'` at `z`
(`SymplecticGeometry.normalSpaceEquivOfTransverseSection_normalClass`). -/
noncomputable def normalSpaceEquivOfTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (ofTransverseSection hm hsm hs hE).isImmersion.NormalSpace z hm ≃L[𝕜]
      E' (ofTransverseSection hm hsm hs hE z) :=
  letI := transverseZeroSetChartedSpace hm hsm hs hE
  let f := ofTransverseSection hm hsm hs hE
  let e := (trivializationAt F' E' (f z)).continuousLinearEquivAt 𝕜 (f z)
    (mem_baseSet_trivializationAt F' E' (f z))
  (f.isImmersion.normalSpaceEquivOfKer z hm
    ((e : E' (f z) →L[𝕜] F').comp (sectionLinearization (F := F') J _root_.id s (f z)))
    (fun v ↦ by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.map_eq_zero_iff,
        tangentRange_ofTransverseSection hm hsm hs hE z, LinearMap.mem_ker,
        ContinuousLinearMap.coe_coe])
    (by
      have h := f.isImmersion.finrank_normalSpace z hm
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
        ((ofTransverseSection hm hsm hs hE).isImmersion.normalClass z hm v) =
      sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z) v := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [normalSpaceEquivOfTransverseSection, ContinuousLinearEquiv.trans_apply,
    Manifold.IsImmersion.normalSpaceEquivOfKer_normalClass, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- The inverse of the normal-space equivalence of a transverse section sends the linearization
of `s` at `z` applied to `v` to the normal class of `v`. -/
@[simp]
theorem normalSpaceEquivOfTransverseSection_symm_apply (z : ↥{x : X | s x = 0})
    (v : TangentSpace J (ofTransverseSection hm hsm hs hE z)) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (normalSpaceEquivOfTransverseSection hm hsm hs hE z).symm
        (sectionLinearization (F := F') J _root_.id s (ofTransverseSection hm hsm hs hE z) v) =
      (ofTransverseSection hm hsm hs hE).isImmersion.normalClass z hm v := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [ContinuousLinearEquiv.symm_apply_eq, normalSpaceEquivOfTransverseSection_normalClass]

/-- **The tangent space of the zero set as the kernel of the linearization.** At a point `z` of
the zero set of a transverse section `s`, the differential of the inclusion of the zero set at `z`
is a linear equivalence from the tangent space of the zero set at `z` onto the kernel of the
linearization of `s` at `z`
(`SymplecticGeometry.coe_tangentSpaceEquivKerOfTransverseSection_apply`). -/
noncomputable def tangentSpaceEquivKerOfTransverseSection (z : ↥{x : X | s x = 0}) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    TangentSpace 𝓘(𝕜, E) z ≃ₗ[𝕜] LinearMap.ker (sectionLinearization (F := F') J _root_.id s
      (ofTransverseSection hm hsm hs hE z)).toLinearMap :=
  letI := transverseZeroSetChartedSpace hm hsm hs hE
  ((ofTransverseSection hm hsm hs hE).isImmersion.tangentSpaceEquivTangentRange z
      hm).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (by simpa using tangentRange_ofTransverseSection hm hsm hs hE z))

/-- The equivalence `SymplecticGeometry.tangentSpaceEquivKerOfTransverseSection` sends a tangent
vector `v` of the zero set at `z` to its image under the differential of the inclusion. -/
@[simp]
theorem coe_tangentSpaceEquivKerOfTransverseSection_apply (z : ↥{x : X | s x = 0})
    (v : letI := transverseZeroSetChartedSpace hm hsm hs hE; TangentSpace 𝓘(𝕜, E) z) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    (tangentSpaceEquivKerOfTransverseSection hm hsm hs hE z v :
        TangentSpace J (ofTransverseSection hm hsm hs hE z)) =
      mfderiv 𝓘(𝕜, E) J (ofTransverseSection hm hsm hs hE) z v := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  rw [tangentSpaceEquivKerOfTransverseSection, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    Manifold.IsImmersion.coe_tangentSpaceEquivTangentRange_apply]

/-- **The normal bundle of the zero set is the restriction of the bundle.** The total-space map
`(z, ν) ↦ (z, φ_z ν)` of the normal-space equivalences `φ_z` of a transverse section, over the
inclusion of the zero set, from the normal bundle of the zero set, with its quotient topology, to
`E'`, is continuous. Together with
the fibrewise equivalences, this is the input of `TauCeti.thomPairMapOfFiberwise` and
`TauCeti.VectorBundleOrientation.comap` over the inclusion of the zero set. -/
theorem continuous_normalSpaceEquivOfTransverseSection :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    Continuous fun v : TotalSpace F' fun z ↦ (ofTransverseSection hm hsm hs
        hE).isImmersion.NormalSpace z hm ↦
      TotalSpace.mk' F' (ofTransverseSection hm hsm hs hE v.proj)
        (normalSpaceEquivOfTransverseSection hm hsm hs hE v.proj v.snd) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  set f := ofTransverseSection hm hsm hs hE
  rw [f.continuous_normalBundle_iff hm]
  -- On an ambient representative `(z, v)` the map is `(z, L_z v)`.
  have hrep : (fun v : TotalSpace F' fun z ↦ f.isImmersion.NormalSpace z hm ↦ TotalSpace.mk' F'
      (f v.proj)
      (normalSpaceEquivOfTransverseSection hm hsm hs hE v.proj v.snd)) ∘ f.normalQuotientMap hm =
      fun p ↦ TotalSpace.mk' F' (f p.proj)
        (sectionLinearization (F := F') J _root_.id s (f p.proj) p.snd) := by
    funext p
    rw [comp_apply, normalQuotientMap_apply]
    exact congrArg (TotalSpace.mk' F' (f p.proj))
      (normalSpaceEquivOfTransverseSection_normalClass hm hsm hs hE p.proj p.snd)
  rw [hrep]
  exact continuous_sectionLinearization_pullback (ENat.one_le_iff_ne_zero_withTop.mpr hm) hsm
    (map_continuous f) (ofTransverseSection_apply_eq_zero hm hsm hs hE)

end SymplecticGeometry

end Equiv

namespace SymplecticGeometry

open SmoothEmbedding

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
    VectorBundleOrientation F' (fun z ↦ (ofTransverseSection hm hsm hs hE).isImmersion.NormalSpace z
        hm) ι :=
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

/-- **Comparing normal orientations of the zero set.** Orient `X` by `oX` and the zero set `Z`
of the transverse section `s`, of dimension `k`, by `oZ`, and let `o'` be an orientation of
`E'`. The normal orientation of `Z` induced by `oX` and `oZ`
(`TauCeti.SmoothEmbedding.normalOrientation`) is the one carried from `o'`
(`SymplecticGeometry.normalOrientationOfSection`) if and only if, at each `z ∈ Z`, the orientation
of `T_z X` induced through `0 → ker L_z → T_z X → E'_z → 0` (`Orientation.ofExact`, kernel first)
by the orientation of `T_z Z` carried to `ker L_z`
(`SymplecticGeometry.tangentSpaceEquivKerOfTransverseSection`) and by `o'` at `z` is `oX` at
`z`, where `L_z` is the linearization of `s` at `z`. -/
theorem normalOrientation_ofTransverseSection_eq_normalOrientationOfSection_iff {k : ℕ}
    (hk : finrank ℝ E = k) (oX : Manifold.Orientation J X (Fin (k + finrank ℝ F')))
    (oZ : letI := transverseZeroSetChartedSpace hm hsm hs hE
      Manifold.Orientation 𝓘(ℝ, E) ↥{x : X | s x = 0} (Fin k))
    (o' : VectorBundleOrientation F' E' (Fin (finrank ℝ F'))) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
      .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI (x : X) : FiniteDimensional ℝ (E' x) := VectorBundle.finiteDimensional ℝ F' E' x
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    (ofTransverseSection hm hsm hs hE).normalOrientation hm (Nat.eq_sub_of_add_eq' hE) oX oZ =
        normalOrientationOfSection hm hsm hs hE (Fintype.card_fin _) o' ↔
      ∀ z : ↥{x : X | s x = 0},
        Orientation.ofExact (LinearMap.ker (sectionLinearization (F := F') J _root_.id s
            (ofTransverseSection hm hsm hs hE z)).toLinearMap).injective_subtype
          (LinearMap.exact_subtype_ker_map _)
          (hs _ (ofTransverseSection_apply_eq_zero hm hsm hs hE z))
          (Orientation.map (Fin k) (tangentSpaceEquivKerOfTransverseSection hm hsm hs hE z)
            (oZ.orientationAt z))
          (o' (ofTransverseSection hm hsm hs hE z))
          ((tangentSpaceEquivKerOfTransverseSection hm hsm hs hE z).finrank_eq.symm.trans hk)
          (VectorBundle.finrank_eq ℝ F' E' _) =
        oX.orientationAt (ofTransverseSection hm hsm hs hE z) := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  have (x : X) : FiniteDimensional ℝ (E' x) := VectorBundle.finiteDimensional ℝ F' E' x
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  have := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  rw [VectorBundleOrientation.ext_iff]
  refine forall_congr' fun z ↦ ?_
  have hr := (ofTransverseSection hm hsm hs hE).finrank_normalSpace_eq (P := F') hm
    (Nat.eq_sub_of_add_eq' hE) z
  rw [SmoothEmbedding.normalOrientation_eq_iff _ _ _ _ _ z _ hk hr]
  set f := ofTransverseSection hm hsm hs hE
  -- The differential of `f`, the identity and the normal-space equivalence carry the tangent
  -- sequence of `f` at `z` onto `0 → ker L_z → T_z X → E'_z → 0`.
  have key := Orientation.map_ofExact (f.isImmersion.mfderiv_injective hm z)
    (f.isImmersion.exact_mfderiv_normalClass z hm) (f.isImmersion.normalClass_surjective z hm)
    (LinearMap.ker _).injective_subtype (LinearMap.exact_subtype_ker_map _)
    (hs _ (ofTransverseSection_apply_eq_zero hm hsm hs hE z))
    (tangentSpaceEquivKerOfTransverseSection hm hsm hs hE z) (LinearEquiv.refl ℝ _)
    (normalSpaceEquivOfTransverseSection hm hsm hs hE z).toLinearEquiv
    (fun v ↦ (coe_tangentSpaceEquivKerOfTransverseSection_apply hm hsm hs hE z v).symm)
    (fun v ↦ normalSpaceEquivOfTransverseSection_normalClass hm hsm hs hE z v)
    (oZ.orientationAt z) (normalOrientationOfSection hm hsm hs hE (Fintype.card_fin _) o' z) hk hr
  rw [Orientation.map_refl, Equiv.refl_apply, map_normalOrientationOfSection_apply] at key
  rw [key]

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

/-- Reindexing the orientation of `E'` reindexes the normal orientation of the zero set. -/
@[simp]
theorem normalOrientationOfSection_reindex {ι' : Type*} [Fintype ι'] (e : ι ≃ ι')
    (hι' : Fintype.card ι' = finrank ℝ F') (o' : VectorBundleOrientation F' E' ι) :
    letI := transverseZeroSetChartedSpace hm hsm hs hE
    haveI := isManifold_transverseZeroSet hm hsm hs hE
    haveI : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
      .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    haveI : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    letI := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
      (Nat.eq_sub_of_add_eq' hE)
    normalOrientationOfSection hm hsm hs hE hι' (VectorBundleOrientation.reindex e o') =
      VectorBundleOrientation.reindex e (normalOrientationOfSection hm hsm hs hE
        ((Fintype.card_congr e).trans hι') o') := by
  let := transverseZeroSetChartedSpace hm hsm hs hE
  have := isManifold_transverseZeroSet hm hsm hs hE
  have : IsManifold 𝓘(ℝ, E) 1 ↥{x : X | s x = 0} :=
    .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  have : IsManifold J 1 X := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hm)
  let := (ofTransverseSection hm hsm hs hE).normalSpaceFiberBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  have := (ofTransverseSection hm hsm hs hE).normalSpaceVectorBundle (P := F') hm
    (Nat.eq_sub_of_add_eq' hE)
  exact VectorBundleOrientation.comap_reindex (o := o')
    (hφ := continuous_normalSpaceEquivOfTransverseSection hm hsm hs hE) e hι'

end Orientation

end SymplecticGeometry

end
