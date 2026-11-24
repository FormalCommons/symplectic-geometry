/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Foliation.LeafSpace.Basic
public import TauCeti.Geometry.Manifold.Gluing.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The smooth leaf space of a regular foliation

Let `𝓕` be a smooth foliation of rank `k` of a boundaryless finite-dimensional manifold `M`
modelled on `E`, and suppose that `𝓕` is regular: every point lies on a slice
(`TauCeti.Foliation.IsRegular`). This file makes the leaf space `𝓕.LeafSpace` a smooth manifold
modelled on `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`, for which the projection
`𝓕.leafSpaceMk` is a smooth submersion whose fibres are the leaves and whose vertical spaces are
the tangent spaces of `𝓕`.

The charts are the inverses of the open embeddings `𝓕.leafSpaceMk ∘ s` given by the slices `s` of
`𝓕` (`TauCeti.Foliation.IsSlice.isOpenEmbedding_leafSpaceMk_comp`), glued by Tau Ceti's
`TauCeti.chartedSpaceOfIsOpenEmbedding`. The gluing condition is that two slices through one leaf
are related near that leaf by a smooth map
(`TauCeti.Foliation.IsSlice.exists_contMDiffAt_transition`): transport along the leaf from the
first slice (`TauCeti.Foliation.SameLeaf.exists_transport`), followed by the retraction onto
the second (`TauCeti.Foliation.IsSlice.exists_retraction`). Near a point of a slice `s`, the
projection is the retraction onto `s` followed by `𝓕.leafSpaceMk ∘ s`, a local diffeomorphism,
which gives its smoothness, the surjectivity of its differential and the kernel of its
differential. This is the construction of the quotient of a regular foliation of
Lee, Chapter 19, and of the reduced space of McDuff–Salamon, §5.4.

Since the smooth structure depends on the proof of regularity, it is a definition
(`TauCeti.Foliation.leafSpaceChartedSpace`), not an instance, and the results are stated under
`letI := leafSpaceChartedSpace h`.

## Main definitions

* `TauCeti.Foliation.leafSpaceChartedSpace`: the charted space on the leaf space of a regular
  foliation.

## Main results

* `TauCeti.Foliation.IsSlice.exists_contMDiffAt_transition`: smooth transitions between slices
  through one leaf.
* `TauCeti.Foliation.isManifold_leafSpace`: the leaf space is a smooth manifold.
* `TauCeti.Foliation.IsSlice.isLocalDiffeomorph_leafSpaceMk_comp`: a slice followed by the
  projection is a local diffeomorphism.
* `TauCeti.Foliation.contMDiff_leafSpaceMk`, `TauCeti.Foliation.isSubmersion_leafSpaceMk`: the
  projection is a smooth submersion.
* `TauCeti.Foliation.ker_mfderiv_leafSpaceMk`: the kernel of the differential of the projection
  is the tangent space of `𝓕`.
* `TauCeti.Foliation.contMDiff_comp_leafSpaceMk_iff`: a map out of the leaf space is smooth
  exactly when its composition with the projection is.
* `TauCeti.Foliation.isRegular_ofSubmodule`: the foliation of a finite-dimensional space by the
  translates of a subspace is regular; `TauCeti.Foliation.t2Space_leafSpace_ofSubmodule`: its leaf
  space is Hausdorff.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  and Chapter 19
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.4
-/

public section

noncomputable section

open Set Function Manifold Module TopologicalSpace Topology TauCeti.Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace Foliation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (∞ + 1) M] [BoundarylessManifold I M] {k : ℕ}
  {𝓕 : Foliation I ∞ M k}

/-- **Transitions between slices.** If two slices `s₁`, `s₂` of a smooth foliation of a
boundaryless manifold meet one leaf at `s₁ u` and `s₂ v`, there is a map `T` from the domain of
`s₁` to that of `s₂`, smooth at `u`, such that `s₂ (T w)` lies on the leaf of `s₁ w` for all `w`
near `u`. -/
theorem IsSlice.exists_contMDiffAt_transition
    {U₁ U₂ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - k)))} {s₁ : U₁ → M} {s₂ : U₂ → M}
    (hs₁ : 𝓕.IsSlice s₁) (hs₂ : 𝓕.IsSlice s₂) {u : U₁} {v : U₂}
    (huv : 𝓕.leafSpaceMk (s₁ u) = 𝓕.leafSpaceMk (s₂ v)) :
    ∃ T : U₁ → U₂, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) ∞ T u ∧
      𝓕.leafSpaceMk ∘ s₂ ∘ T =ᶠ[𝓝 u] 𝓕.leafSpaceMk ∘ s₁ := by
  obtain ⟨V, hV, φ, hφ, hφu, hφl⟩ := (leafSpaceMk_eq_leafSpaceMk_iff.1 huv).exists_transport
  obtain ⟨r, hr, -, hrl, -⟩ := hs₂.exists_retraction v
  have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I ∞ (fun w ↦ φ (s₁ w)) u :=
    (hφ.contMDiffAt hV).comp u (hs₁.contMDiff u)
  refine ⟨fun w ↦ r (φ (s₁ w)), hr.comp_of_eq hc hφu, ?_⟩
  have h₁ : ∀ᶠ w in 𝓝 u, s₁ w ∈ V := hs₁.contMDiff.continuous.continuousAt.preimage_mem_nhds hV
  have h₂ : ∀ᶠ w in 𝓝 u, 𝓕.SameLeaf (φ (s₁ w)) (s₂ (r (φ (s₁ w)))) := by
    have hc' := hc.continuousAt
    simp only [ContinuousAt, hφu] at hc'
    exact hc'.eventually hrl
  filter_upwards [h₁, h₂] with w hw₁ hw₂
  exact leafSpaceMk_eq_leafSpaceMk_iff.2 ((hφl _ hw₁).trans hw₂).symm

variable (𝓕) in
/-- The slices of `𝓕`, which index the charts of its leaf space. -/
private structure SliceIndex where
  /-- The domain of the slice. -/
  U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
  /-- The slice. -/
  s : U → M
  isSlice : 𝓕.IsSlice s

private theorem isOpenEmbedding_sliceIndex (j : SliceIndex 𝓕) :
    IsOpenEmbedding (𝓕.leafSpaceMk ∘ j.s) :=
  j.isSlice.isOpenEmbedding_leafSpaceMk_comp

private theorem IsRegular.exists_sliceIndex (h : 𝓕.IsRegular) (q : 𝓕.LeafSpace) :
    ∃ (j : SliceIndex 𝓕) (u : j.U), (𝓕.leafSpaceMk ∘ j.s) u = q := by
  obtain ⟨U, s, hs, -, u, hu⟩ := h.exists_isOpenEmbedding q
  exact ⟨⟨U, s, hs⟩, u, hu⟩

private theorem sliceIndex_transition {n : ℕ∞ω} (hn : n ≤ ∞) (j j' : SliceIndex 𝓕) (u : j.U)
    (v : j'.U) (huv : (𝓕.leafSpaceMk ∘ j.s) u = (𝓕.leafSpaceMk ∘ j'.s) v) :
    ∃ T : j.U → j'.U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) n T u ∧
      (𝓕.leafSpaceMk ∘ j'.s) ∘ T =ᶠ[𝓝 u] 𝓕.leafSpaceMk ∘ j.s := by
  obtain ⟨T, hT, hTe⟩ := j.isSlice.exists_contMDiffAt_transition j'.isSlice huv
  exact ⟨T, hT.of_le hn, hTe⟩

/-- The charted space on the leaf space of a regular foliation `𝓕` of rank `k` of a manifold
modelled on `E`, modelled on `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`: its charts are the inverses
of the compositions `𝓕.leafSpaceMk ∘ s` of the slices `s` of `𝓕` with the projection, followed
by the charts of the domains of the slices. -/
@[instance_reducible]
def leafSpaceChartedSpace (h : 𝓕.IsRegular) :
    ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.LeafSpace :=
  chartedSpaceOfIsOpenEmbedding (U := fun j : SliceIndex 𝓕 ↦ j.U)
    (φ := fun j ↦ 𝓕.leafSpaceMk ∘ j.s) isOpenEmbedding_sliceIndex h.exists_sliceIndex

/-- **The leaf space of a regular foliation is a smooth manifold.** -/
theorem isManifold_leafSpace (h : 𝓕.IsRegular) :
    letI := leafSpaceChartedSpace h
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) ∞ 𝓕.LeafSpace :=
  isManifold_chartedSpaceOfIsOpenEmbedding _ _ (sliceIndex_transition le_rfl)

/-- A slice of a regular foliation, followed by the projection, is a local diffeomorphism onto the
leaf space. -/
theorem IsSlice.isLocalDiffeomorph_leafSpaceMk_comp (h : 𝓕.IsRegular)
    {U : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - k)))} {s : U → M} (hs : 𝓕.IsSlice s) :
    letI := leafSpaceChartedSpace h
    IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) ∞ (𝓕.leafSpaceMk ∘ s) :=
  isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding _ _ (sliceIndex_transition le_rfl)
    (⟨U, s, hs⟩ : SliceIndex 𝓕)

/-- The projection onto the leaf space of a regular foliation is smooth. -/
theorem contMDiff_leafSpaceMk (h : 𝓕.IsRegular) :
    letI := leafSpaceChartedSpace h
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) ∞ 𝓕.leafSpaceMk := by
  let := leafSpaceChartedSpace h
  intro x
  obtain ⟨U, s, hs, u, rfl⟩ := isRegular_def.1 h x
  obtain ⟨r, hr, -, hrl, -⟩ := hs.exists_retraction u
  refine (((hs.isLocalDiffeomorph_leafSpaceMk_comp h) (r (s u))).contMDiffAt.comp (s u) hr)
    |>.congr_of_eventuallyEq ?_
  filter_upwards [hrl] with z hz
  exact leafSpaceMk_eq_leafSpaceMk_iff.2 hz

/-- The differential of the projection onto the leaf space of a regular foliation is surjective,
and its kernel is the tangent space of the foliation. -/
private theorem surjective_mfderiv_leafSpaceMk_and_ker (h : 𝓕.IsRegular) (x : M) :
    letI := leafSpaceChartedSpace h
    Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.leafSpaceMk x) ∧
      LinearMap.ker
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.leafSpaceMk x).toLinearMap =
        𝓕.distribution x := by
  let := leafSpaceChartedSpace h
  obtain ⟨U, s, hs, u, rfl⟩ := isRegular_def.1 h x
  obtain ⟨r, hr, hrs, hrl, hrd⟩ := hs.exists_retraction u
  have hL := (hs.isLocalDiffeomorph_leafSpaceMk_comp h) (r (s u))
  have hrx : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (s u) :=
    hr.mdifferentiableAt (by simp)
  -- Near `s u`, the projection is the retraction followed by `𝓕.leafSpaceMk ∘ s`.
  have he : 𝓕.leafSpaceMk =ᶠ[𝓝 (s u)] (𝓕.leafSpaceMk ∘ s) ∘ r := by
    filter_upwards [hrl] with z hz
    exact leafSpaceMk_eq_leafSpaceMk_iff.2 hz
  have hd : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.leafSpaceMk (s u) =
      (mfderiv 𝓘(ℝ, _) 𝓘(ℝ, _) (𝓕.leafSpaceMk ∘ s) (r (s u))).comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (s u)) := by
    rw [he.mfderiv_eq]
    exact mfderiv_comp (s u) (hL.contMDiffAt.mdifferentiableAt (by simp)) hrx
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hD := hL.mfderivToContinuousLinearEquiv_coe hn
  -- The retraction is a left inverse of the slice, so its differential is surjective.
  have hrsurj :
      Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (s u)) := by
    intro w
    have hsx : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I s u :=
      (hs.contMDiff u).mdifferentiableAt (by simp)
    have hrs' : r ∘ s =ᶠ[𝓝 u] id := hrs
    have hid := ((hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))) u)
      |>.congr_of_eventuallyEq hrs').mfderiv
    refine ⟨mfderiv 𝓘(ℝ, _) I s u w, ?_⟩
    exact congrArg (· w) ((mfderiv_comp u hrx hsx).symm.trans hid)
  refine ⟨?_, ?_⟩
  · rw [hd, ← hD]
    exact (hL.mfderivToContinuousLinearEquiv hn).surjective.comp hrsurj
  · have hker : LinearMap.ker
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.leafSpaceMk (s u)).toLinearMap =
        LinearMap.ker
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (s u)).toLinearMap := by
      rw [hd, ← hD]
      ext v
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact (hL.mfderivToContinuousLinearEquiv hn).map_eq_zero_iff
    rw [hker]
    refine (Submodule.eq_of_le_of_finrank_eq (fun v hv ↦ hrd v hv) ?_).symm
    have hrk := LinearMap.finrank_range_add_finrank_ker
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) r (s u)).toLinearMap
    rw [LinearMap.range_eq_top.2 hrsurj, finrank_top] at hrk
    have hk : k ≤ finrank ℝ E := 𝓕.finrank_distribution (s u) ▸ Submodule.finrank_le _
    have hE : finrank ℝ (TangentSpace I (s u)) = finrank ℝ E := rfl
    have hG : finrank ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (r (s u))) =
        finrank ℝ E - k := finrank_euclideanSpace_fin
    rw [𝓕.finrank_distribution]
    rw [hE, hG] at hrk
    omega

/-- **The projection onto the leaf space is a submersion.** -/
theorem isSubmersion_leafSpaceMk [I.Boundaryless] (h : 𝓕.IsRegular) :
    letI := leafSpaceChartedSpace h
    IsSubmersion I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) ∞ 𝓕.leafSpaceMk := by
  let := leafSpaceChartedSpace h
  have : IsManifold I ∞ M := .of_le (n := ∞ + 1) le_self_add
  have := isManifold_leafSpace h
  exact ((contMDiff_leafSpaceMk h).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    fun x ↦ (surjective_mfderiv_leafSpaceMk_and_ker h x).1).isSubmersion

/-- The kernel of the differential at `x` of the projection onto the leaf space of a regular
foliation `𝓕` is the tangent space of `𝓕` at `x`. -/
theorem ker_mfderiv_leafSpaceMk (h : 𝓕.IsRegular) (x : M) :
    letI := leafSpaceChartedSpace h
    LinearMap.ker
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) 𝓕.leafSpaceMk x).toLinearMap =
      𝓕.distribution x :=
  (surjective_mfderiv_leafSpaceMk_and_ker h x).2

/-- **Smooth maps out of the leaf space.** A map out of the leaf space of a regular foliation is
`C^m`, for `m ≤ ∞`, exactly when its composition with the projection is. -/
theorem contMDiff_comp_leafSpaceMk_iff (h : 𝓕.IsRegular) {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {m : ℕ∞ω}
    (hm : m ≤ ∞) {g : 𝓕.LeafSpace → N} :
    letI := leafSpaceChartedSpace h
    ContMDiff I I' m (g ∘ 𝓕.leafSpaceMk) ↔
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I' m g := by
  let := leafSpaceChartedSpace h
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.comp ((contMDiff_leafSpaceMk h).of_le hm)⟩
  exact (contMDiff_iff_chartedSpaceOfIsOpenEmbedding (n := m) _ _
    (sliceIndex_transition hm)).2 fun j ↦ hg.comp (j.isSlice.contMDiff.of_le hm)

section ofSubmodule

variable (S : Submodule ℝ E)

/-- The foliation of a finite-dimensional space `E` by the translates of a subspace `S` is
regular: through `x`, the translate by `x` of a complement of `S`, parametrized linearly, is a
slice. -/
theorem isRegular_ofSubmodule (hn : (1 : ℕ∞ω) ≤ ∞) : (ofSubmodule S hn).IsRegular := by
  refine isRegular_def.2 fun x ↦ ?_
  obtain ⟨C, hSC⟩ := S.exists_isCompl
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S))) = finrank ℝ C := by
    rw [finrank_euclideanSpace_fin, ← Submodule.finrank_add_eq_of_isCompl hSC]
    omega
  set e := ContinuousLinearEquiv.ofFinrankEq hdim
  set L : EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S)) →L[ℝ] E :=
    C.subtypeL.comp e.toContinuousLinearMap
  set f : EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S)) → E := fun u ↦ x + L u
  have hf : ContDiff ℝ ∞ f := contDiff_const.add L.contDiff
  have hm (u : (⊤ : Opens (EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S)))))
      (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S))) u) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S))) 𝓘(ℝ, E)
        (f ∘ Subtype.val) u v = L v :=
    (mfderiv_comp_subtype_val_apply v).trans
      (by
        have hd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S))) 𝓘(ℝ, E) f u =
            L :=
          (L.hasFDerivAt.const_add x).hasMFDerivAt.mfderiv
        exact congrArg (fun A ↦ A v) hd)
  refine ⟨⊤, f ∘ Subtype.val, ⟨hf.contMDiff.comp contMDiff_subtypeVal, fun u ↦ ?_, ?_⟩,
    ⟨⟨0, trivial⟩, by simp [f]⟩⟩
  · rw [ofSubmodule_distribution]
    suffices hR : LinearMap.range
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ S))) 𝓘(ℝ, E)
          (f ∘ Subtype.val) u).toLinearMap = C by
      rw [hR]
      exact hSC.symm
    ext w
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩
      exact Eq.mpr (congrArg (· ∈ C) (hm u v)) (e v).property
    · intro hw
      exact ⟨e.symm ⟨w, hw⟩, (hm u _).trans (by simp [L])⟩
  · intro u v huv
    rw [sameLeaf_ofSubmodule_iff] at huv
    have h0 : (e v : E) - e u = 0 := by
      have hC : (e v : E) - e u ∈ C := sub_mem (e v).property (e u).property
      simp only [comp_apply, f, add_sub_add_left_eq_sub] at huv
      exact (Submodule.disjoint_def.1 hSC.disjoint) _ huv hC
    exact Subtype.ext (e.injective (Subtype.ext (sub_eq_zero.1 h0))).symm

/-- The leaf space of the foliation of a finite-dimensional space by the translates of a subspace
is Hausdorff: a projection along the subspace onto a complement separates the leaves. -/
instance t2Space_leafSpace_ofSubmodule (hn : (1 : ℕ∞ω) ≤ ∞) :
    T2Space (ofSubmodule S hn).LeafSpace := by
  obtain ⟨C, hSC⟩ := S.exists_isCompl
  refine T2Space.of_injective_continuous
    (f := LeafSpace.lift (Submodule.projectionOnto C S hSC.symm) fun y z hyz ↦ ?_) ?_
    (LeafSpace.continuous_lift
      (Submodule.projectionOnto C S hSC.symm).continuous_of_finiteDimensional)
  · rw [sameLeaf_ofSubmodule_iff] at hyz
    rw [← sub_eq_zero, ← map_sub, Submodule.projectionOnto_apply_eq_zero_iff]
    simpa using S.neg_mem hyz
  · intro q q' hqq'
    induction q using LeafSpace.ind with | h y => ?_
    induction q' using LeafSpace.ind with | h z => ?_
    simp only [LeafSpace.lift_leafSpaceMk] at hqq'
    rw [leafSpaceMk_eq_leafSpaceMk_iff, sameLeaf_ofSubmodule_iff,
      ← Submodule.projectionOnto_apply_eq_zero_iff hSC.symm, map_sub, hqq', sub_self]

end ofSubmodule

end Foliation

end TauCeti

end
