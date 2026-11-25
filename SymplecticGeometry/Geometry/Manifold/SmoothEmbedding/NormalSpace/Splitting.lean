/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Compactness.Paracompact
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Topology
public import TauCeti.Topology.VectorBundle.Pullback
import Mathlib.Topology.PartitionOfUnity
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Complement
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Exact
import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.PartitionOfUnity.Basic
import SymplecticGeometry.Topology.FiberBundle.Pullback
import SymplecticGeometry.Topology.VectorBundle.Section

/-!
# Splitting the tangent bundle along an embedding

Let `f : M → N` be an embedding of positive regularity into a finite-dimensional manifold
over `𝕜`, and `ν` its normal bundle, with fibres `ν_x = T_{f x} N ⧸ df_x (T_x M)` (Tau Ceti's
`TauCeti.SmoothEmbedding.NormalSpace`). This file splits the short exact sequence
`0 → TM → f^* TN → ν → 0` of bundles over `M`.

* A fibrewise linear right inverse `r` of the normal class map, whose map of total spaces is
  continuous, exists when `M` is normal and paracompact and `𝕜` is `ℝ` or `ℂ`:
  `TauCeti.SmoothEmbedding.normalRightInverse`. Near each point, a fixed complement of the image
  of the differential in a tangent chart of `N` gives such a right inverse
  (Tau Ceti's `TauCeti.SmoothEmbedding.normalSpaceEquivOfComplement`); a partition of unity
  glues these, since a combination of right inverses with real coefficients of sum one is again
  one.
* For any fibrewise linear right inverse `r`, the maps `(u, a) ↦ df u + r a` form an isomorphism
  `TM ×ᵇ ν ≃ f^* TN`: `TauCeti.SmoothEmbedding.tangentNormalEquiv`, the inverse of the
  splitting that Mathlib's `Function.Exact.splitSurjectiveEquiv` gives in each fibre. Its map of
  total spaces is continuous when that of `r` is, and so is the inverse, by Tau Ceti's
  `TauCeti.continuous_bundle_symm`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalRightInverse`: a fibrewise right inverse of the normal class
  map, continuous on total spaces.
* `TauCeti.SmoothEmbedding.tangentNormalEquiv`: the isomorphism `TM ×ᵇ ν ≃ f^* TN` given by a
  fibrewise right inverse of the normal class map.

## Main results

* `TauCeti.SmoothEmbedding.normalClass_normalRightInverse`,
  `TauCeti.SmoothEmbedding.continuous_normalRightInverse`.
* `TauCeti.SmoothEmbedding.tangentNormalEquiv_apply`,
  `TauCeti.SmoothEmbedding.continuous_tangentNormalEquiv`,
  `TauCeti.SmoothEmbedding.continuous_tangentNormalEquiv_symm`.

## Implementation notes

The gluing follows the proof of Tau Ceti's
`TauCeti.exists_continuous_section_forall_mem_convex_of_local`, with the sum taken over the finite
support of the partition of unity at each point. It is carried out on the total space of
`f^* TN`, through the normal class map, which is a quotient map onto the total space of `ν`
(`TauCeti.SmoothEmbedding.continuous_normalBundle_iff`).

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Chapter 3, for splitting off a sub-bundle
  by a complement.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the normal bundle before
  Theorem 6.24.
-/

public section

noncomputable section

open Bundle Set Topology Filter
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

/-! ### The isomorphism given by a right inverse -/

section Equiv

variable (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
  (r : ∀ x, f.NormalSpace x hn →L[𝕜] TangentSpace J (f x))
  (hr : ∀ x a, f.normalClass x hn (r x a) = a)

/-- The isomorphism `T_x M × ν_x ≃ T_{f x} N`, `(u, a) ↦ df u + r a`, given by a fibrewise right
inverse `r` of the normal class map. -/
def tangentNormalEquiv (x : M) :
    (TangentSpace I ×ᵇ fun x ↦ f.NormalSpace x hn) x ≃L[𝕜]
      ((f : M → N) *ᵖ (TangentSpace J)) x :=
  haveI : T2Space (((f : M → N) *ᵖ (TangentSpace J)) x) := inferInstanceAs (T2Space V)
  haveI : FiniteDimensional 𝕜 (((f : M → N) *ᵖ (TangentSpace J)) x) :=
    inferInstanceAs (FiniteDimensional 𝕜 V)
  haveI : T2Space ((TangentSpace I ×ᵇ fun x ↦ f.NormalSpace x hn) x) :=
    inferInstanceAs (T2Space (E × f.NormalSpace x hn))
  ((exact_mfderiv_normalClass f x hn).splitSurjectiveEquiv
      (f.isImmersion.mfderiv_injective hn x) ⟨(r x).toLinearMap, LinearMap.ext (hr x)⟩).val
    |>.toContinuousLinearEquiv.symm

/-- The isomorphism given by a right inverse `r` sends `(u, a)` to `df u + r a`. -/
@[simp]
theorem tangentNormalEquiv_apply (x : M) (p : (TangentSpace I ×ᵇ fun x ↦ f.NormalSpace x hn) x) :
    f.tangentNormalEquiv hn r hr x p = mfderiv I J f x p.1 + r x p.2 :=
  (rfl)

/-- The normal component of the inverse of the isomorphism is the normal class. -/
@[simp]
theorem snd_tangentNormalEquiv_symm_apply (x : M) (v : TangentSpace J (f x)) :
    ((f.tangentNormalEquiv hn r hr x).symm v).2 = f.normalClass x hn v := by
  conv_rhs => rw [← (f.tangentNormalEquiv hn r hr x).apply_symm_apply v]
  rw [tangentNormalEquiv_apply, map_add, normalClass_mfderiv, zero_add, hr]

/-- The tangential component of the inverse of the isomorphism is carried by `df` to
`v - r [v]`. -/
theorem mfderiv_fst_tangentNormalEquiv_symm_apply (x : M)
    (v : TangentSpace J (f x)) :
    mfderiv I J f x ((f.tangentNormalEquiv hn r hr x).symm v).1 =
      v - r x (f.normalClass x hn v) := by
  have h := (f.tangentNormalEquiv hn r hr x).apply_symm_apply v
  rw [tangentNormalEquiv_apply, snd_tangentNormalEquiv_symm_apply] at h
  exact eq_sub_of_add_eq h

variable [IsManifold I 1 M] [IsManifold J 1 N] {P : Type*}

/-- If the map of total spaces of a right inverse `r` is continuous, so is that of the
isomorphism `TM ×ᵇ ν ≃ f^* TN` it gives. -/
theorem continuous_tangentNormalEquiv
    (hrc : Continuous fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj (r p.proj p.snd)) :
    Continuous fun p : TotalSpace (E × P) (TangentSpace I ×ᵇ fun x ↦ f.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (f.tangentNormalEquiv hn r hr p.proj p.snd) := by
  have hd := (FiberBundle.Prod.isInducing_diag E (TangentSpace I) P
    (fun x ↦ f.NormalSpace x hn)).continuous
  -- The differential, as a map from the total space of `TM` to that of `f^* TN`.
  have hdf : Continuous fun p : TangentBundle I M ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (mfderiv I J f p.proj p.snd) :=
    Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj E (TangentSpace I),
      f.contMDiff.continuous_tangentMap (ENat.one_le_iff_ne_zero_withTop.mpr hn)⟩
  have h := (hdf.comp (continuous_fst.comp hd)).add_totalSpace 𝕜 (hrc.comp (continuous_snd.comp hd))
  exact h.congr fun p ↦ (congrArg (TotalSpace.mk p.proj)
    (f.tangentNormalEquiv_apply hn r hr p.proj p.snd)).symm

/-- If the map of total spaces of a right inverse `r` is continuous, so is that of the inverse
of the isomorphism `TM ×ᵇ ν ≃ f^* TN` it gives. -/
theorem continuous_tangentNormalEquiv_symm [FiniteDimensional 𝕜 E] [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (hrc : Continuous fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj (r p.proj p.snd)) :
    Continuous fun p : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
      TotalSpace.mk' (E × P) (E := TangentSpace I ×ᵇ fun x ↦ f.NormalSpace x hn) p.proj
        ((f.tangentNormalEquiv hn r hr p.proj).symm p.snd) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  exact TauCeti.continuous_bundle_symm _ (f.continuous_tangentNormalEquiv hn r hr hrc)

end Equiv

/-! ### A continuous right inverse of the normal class map -/

section RightInverse

variable [IsManifold I 1 M] [IsManifold J 1 N] (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)

/-- Near each point `x₀`, a complement of the image of the differential at `x₀`, fixed in the
tangent chart of `N` at `f x₀`, gives over a neighbourhood `U` of `x₀` a right inverse of the
normal class map whose composite with the normal class map is continuous on total spaces. -/
private theorem exists_local_rightInverse_normalClass (x₀ : M) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ s : ∀ x, f.NormalSpace x hn →L[𝕜] TangentSpace J (f x),
        (∀ x ∈ U, ∀ a, f.normalClass x hn (s x a) = a) ∧
        ∀ v : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)), v.proj ∈ U →
          ContinuousAt (fun v : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
            TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) v.proj
              (s v.proj (f.normalClass v.proj hn v.snd))) v := by
  have : CompleteSpace V := FiniteDimensional.completeSpace 𝕜 V
  have : IsManifold I 0 M := .of_le (n := 1) zero_le_one
  obtain ⟨Q, -, U, hU, hxU, hsub, hInv, hcont⟩ :=
    f.exists_contMDiffOn_inTangentCoordinates_quotientRangeCoordinate (m := 0)
      (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) (by simp) x₀
  set e := trivializationAt V (TangentSpace J) (f x₀)
  have he {x : M} (hx : x ∈ U) : f x ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (hsub hx).2
  classical
  let s : ∀ x, f.NormalSpace x hn →L[𝕜] TangentSpace J (f x) := fun x ↦
    if h : x ∈ U then (e.symmL 𝕜 (f x)).comp (Q.subtypeL.comp
      (f.normalSpaceEquivOfComplement hn (hsub h).1 (hsub h).2 Q.subtypeL (hInv x h) :
        f.NormalSpace x hn →L[𝕜] Q)) else 0
  -- On a normal class, `s` is the fixed complementary component in the chart.
  have hs {x : M} (h : x ∈ U) (v : TangentSpace J (f x)) :
      s x (f.normalClass x hn v) = e.symm (f x) (Q.subtypeL
        ((inTangentCoordinates I J _root_.id (f : M → N) (mfderiv I J (f : M → N)) x₀ x
          ).quotientRangeCoordinate Q.subtypeL (e ⟨f x, v⟩).2)) := by
    simp only [s, h, ↓reduceDIte, e, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      normalSpaceEquivOfComplement_normalClass, e.symmL_apply (he h)]
  refine ⟨U, hU, hxU, s, fun x h a ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := (f.normalSpaceEquivOfComplement hn (hsub h).1 (hsub h).2 Q.subtypeL
      (hInv x h)).symm.surjective a
    simp only [s, h, ↓reduceDIte, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [e.symmL_apply (he h), normalSpaceEquivOfComplement_symm_apply]
  -- The coordinate of the complementary component is continuous near `v`.
  have hb : f v.proj ∈ e.baseSet := he hv
  have hproj := (FiberBundle.continuous_proj V ((f : M → N) *ᵖ (TangentSpace J))).continuousAt
    (x := v)
  have hcoord : ContinuousAt (fun w : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
      Q.subtypeL ((inTangentCoordinates I J _root_.id (f : M → N) (mfderiv I J (f : M → N)) x₀
        w.proj).quotientRangeCoordinate Q.subtypeL (e (Pullback.lift f w)).2)) v :=
    Q.subtypeL.continuous.continuousAt.comp
      (((hcont.continuousOn.continuousAt (hU.mem_nhds hv)).comp hproj).clm_apply
        (continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt
          (e.open_source.mem_nhds (e.mem_source.2 hb))).comp
            (Pullback.continuous_lift V (TangentSpace J) (f : M → N)).continuousAt)))
  have hf : ContinuousAt (fun w : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
      f w.proj) v := f.contMDiff.continuous.continuousAt.comp hproj
  have hsymm := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds
    (e.mem_target.2 hb))).comp (hf.prodMk hcoord)
  have hg : ContinuousAt (fun w : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) w.proj (e.symm (f w.proj)
        (Q.subtypeL ((inTangentCoordinates I J _root_.id (f : M → N) (mfderiv I J (f : M → N)) x₀
          w.proj).quotientRangeCoordinate Q.subtypeL (e (Pullback.lift f w)).2)))) v := by
    exact Pullback.continuousAt_iff.2 ⟨hproj, hsymm⟩
  refine hg.congr ?_
  filter_upwards [hproj.preimage_mem_nhds (hU.mem_nhds hv)] with w hw
  exact congrArg (TotalSpace.mk w.proj) (hs hw w.snd).symm

variable [IsRCLikeNormedField 𝕜] [_root_.NormalSpace M] [ParacompactSpace M]

/-- Over a normal paracompact manifold, the normal class map of an embedding over `ℝ` or `ℂ`
has a fibrewise linear right inverse whose composite with the normal class map is continuous on
total spaces. -/
theorem exists_rightInverse_normalClass :
    ∃ r : ∀ x, f.NormalSpace x hn →L[𝕜] TangentSpace J (f x),
      (∀ x a, f.normalClass x hn (r x a) = a) ∧
      Continuous fun v : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J)) ↦
        TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) v.proj
          (r v.proj (f.normalClass v.proj hn v.snd)) := by
  let := IsRCLikeNormedField.rclike 𝕜
  choose U hU hxU s hs hsc using f.exists_local_rightInverse_normalClass hn
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU
    fun x _ ↦ mem_iUnion.2 ⟨x, hxU x⟩
  refine ⟨fun x ↦ ∑ i ∈ ρ.finsupport x, (ρ i x : 𝕜) • s i x, fun x a ↦ ?_, ?_⟩
  · -- A combination of right inverses with coefficients of sum one is a right inverse.
    rw [_root_.sum_apply, map_sum, Finset.sum_congr rfl fun i hi ↦ by
      rw [_root_.smul_apply, map_smul,
        hs i x (hρ.mem_of_mem_finsupport hi) a], ← Finset.sum_smul,
      ← RCLike.ofReal_sum, ρ.sum_finsupport (mem_univ x), RCLike.ofReal_one, one_smul]
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  have hproj := (FiberBundle.continuous_proj V ((f : M → N) *ᵖ (TangentSpace J))).continuousAt
    (x := v)
  -- The normal class of a vector of `f^* TN`, named so that rewriting sees no fibre cast.
  let a (w : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))) : f.NormalSpace w.proj hn :=
    f.normalClass w.proj hn w.snd
  -- Near `v`, only the finitely many `i` with `v.proj` in the closed support of `ρ i` contribute,
  -- and each of their terms is continuous at `v`.
  have key := ContinuousAt.sum_totalSpace 𝕜 (F := V) (E := (f : M → N) *ᵖ (TangentSpace J))
    (ρ.fintsupport v.proj) hproj
    (s := fun i (w : TotalSpace V ((f : M → N) *ᵖ (TangentSpace J))) ↦
      (ρ i w.proj : 𝕜) • s i w.proj (a w))
    fun i hi ↦ (RCLike.continuous_ofReal.continuousAt.comp
      ((ρ i).continuous.continuousAt.comp hproj)).smul_totalSpace
        (hsc i v (hρ i ((ρ.mem_fintsupport_iff v.proj i).1 hi)))
  refine key.congr ?_
  filter_upwards [hproj.preimage_mem_nhds (ρ.eventually_finsupport_subset v.proj)] with w hw
  refine congrArg (TotalSpace.mk w.proj) ?_
  rw [_root_.sum_apply]
  exact (Finset.sum_subset (f := fun j ↦ ((ρ j w.proj : 𝕜) • s j w.proj) (a w)) hw
    fun i _ hi ↦ by rw [Function.notMem_support.1 ((ρ.mem_finsupport w.proj).not.1 hi),
      RCLike.ofReal_zero, zero_smul, _root_.zero_apply]).symm

/-- A fibrewise linear right inverse of the normal class map `T_{f x} N → ν_x` of an embedding,
over a normal paracompact manifold and over `ℝ` or `ℂ`, whose map of total spaces is
continuous (`TauCeti.SmoothEmbedding.continuous_normalRightInverse`). -/
def normalRightInverse (x : M) : f.NormalSpace x hn →L[𝕜] TangentSpace J (f x) :=
  (f.exists_rightInverse_normalClass hn).choose x

/-- `normalRightInverse` is a right inverse of the normal class map. -/
@[simp]
theorem normalClass_normalRightInverse (x : M) (a : f.NormalSpace x hn) :
    f.normalClass x hn (f.normalRightInverse hn x a) = a :=
  (f.exists_rightInverse_normalClass hn).choose_spec.1 x a

/-- The map of total spaces of `normalRightInverse`, from the normal bundle to `f^* TN`, is
continuous. -/
theorem continuous_normalRightInverse {P : Type*} :
    Continuous fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
      TotalSpace.mk' V (E := (f : M → N) *ᵖ (TangentSpace J)) p.proj
        (f.normalRightInverse hn p.proj p.snd) :=
  (f.continuous_normalBundle_iff hn).2 <|
    (f.exists_rightInverse_normalClass hn).choose_spec.2.congr fun v ↦ by
      -- `normalRightInverse` is the chosen right inverse, by definition.
      rw [Function.comp_apply, normalQuotientMap_apply]
      rfl

end RightInverse

end TauCeti.SmoothEmbedding

end
