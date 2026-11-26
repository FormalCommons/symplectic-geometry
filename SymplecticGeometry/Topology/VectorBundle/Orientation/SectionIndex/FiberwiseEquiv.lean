/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Topology.VectorBundle.Orientation.FiberwiseEquiv
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex

/-!
# Local indices of sections along fibrewise isomorphisms

Let `φ x : E'_x ≃ E_x` be a fibrewise isomorphism of real vector bundles of rank `n + 1` over a
manifold `M` of dimension `n + 1`, carrying an orientation `o'` of `E'` to an orientation `o` of
`E`. Then the local index of a section `s` of `E'` at any point is the local index of the section
`x ↦ φ x (s x)` of `E` there
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`). Both indices are Kronecker
pairings with pull-backs of Thom classes, and the map of Thom pairs of `φ` pulls the Thom class of
`(E, o)` back to that of `(E', o')`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass`).

More generally, let `φ x : E₁_x ≃ E_{j x}` be such an isomorphism over an open embedding
`j : M₁ → M`, and orient `M₁` by pulling back the orientation of `M`
(`TauCeti.HomologicalOrientation.comap`). If `φ` carries a section `s₁` of `E₁` to a section `s` of
`E` along `j`, the local index of `s₁` at `z` is the local index of `s` at `j z`
(`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`). An isolating neighbourhood
`U` of `z` maps onto the isolating neighbourhood `j(U)` of `j z`, and `j` carries the local
orientation of `U` at `z` to that of `j(U)` at `j z`
(`Topology.IsOpenEmbedding.localHomologyMap_restrict_localOrientationEquiv_symm`, which
generalizes Tau Ceti's `IsOpen.localHomologyMap_inclusion_localOrientationEquiv_symm`, the case of
the identity map; its proof composes open embeddings with Tau Ceti's
`IsOpenEmbedding.localOrientationEquiv_trans`, as Tau Ceti's proof of
`TauCeti.HomologicalOrientation.localIndex_comap` does). The rest of the proof follows the step of
Tau Ceti's proof of
`TauCeti.VectorBundleOrientation.sectionIndex_eq` that shrinks an isolating neighbourhood.

## Main results

* `Topology.IsOpenEmbedding.localHomologyMap_restrict_localOrientationEquiv_symm`: the restriction
  `U → V` of an open embedding `j` to open sets carries corresponding local orientations to
  corresponding local orientations.
* `TauCeti.VectorBundleOrientation.sectionIndex_eq_of_fiberwise`: orientation-preserving
  fibrewise isomorphisms preserve local indices of sections.
* `TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`: so do orientation-preserving
  fibrewise isomorphisms over open embeddings, for the pulled-back orientation of the base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (bundle maps and orientations) and §11 (the Euler class and sections).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set

universe w

namespace Topology.IsOpenEmbedding

open TauCeti

variable {M N : Type w} [TopologicalSpace M] [T1Space M] [TopologicalSpace N] [T1Space N]
  {j : M → N}

/-- Let `j : M → N` be an open embedding that maps an open set `U` of `M` into an open set `V` of
`N`. The map of local homology induced by the restriction `U → V` of `j` carries the local
orientation of `U` at `x` corresponding (through `j`) to a local orientation `z` of `N` at `j x` to
the local orientation of `V` at `j x` corresponding to `z`. -/
lemma localHomologyMap_restrict_localOrientationEquiv_symm (hj : IsOpenEmbedding j) {U : Set M}
    {V : Set N} (hU : IsOpen U) (hV : IsOpen V) (hUV : MapsTo j U V) (x : U) {d : ℕ}
    (z : LocalOrientation N (j x) d)
    (h : ContinuousMap.mk (hUV.restrict j U V) (hj.continuous.restrict hUV) ⁻¹'
      {Subtype.mk (j x) (hUV x.property)} ⊆ {x}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
        (ContinuousMap.mk (hUV.restrict j U V) (hj.continuous.restrict hUV)) h d
        ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv x d).symm
          ((hj.localOrientationEquiv x d).symm z)).val =
      ((hV.isOpenEmbedding_subtypeVal.localOrientationEquiv (Subtype.mk (j x) (hUV x.property))
        d).symm z).val := by
  have hk : IsOpenEmbedding (hUV.restrict j U V) :=
    (IsOpenEmbedding.of_comp_iff _ hV.isOpenEmbedding_subtypeVal).1
      (hj.comp hU.isOpenEmbedding_subtypeVal)
  -- Both local orientations of `U` come from `z` through composites of the same open
  -- embeddings, `j ∘ Subtype.val = Subtype.val ∘ restrict`.
  have e : (hU.isOpenEmbedding_subtypeVal.localOrientationEquiv x d).symm
        ((hj.localOrientationEquiv x d).symm z) =
      (hk.localOrientationEquiv x d).symm
        ((hV.isOpenEmbedding_subtypeVal.localOrientationEquiv _ d).symm z) := by
    rw [← Equiv.symm_trans_apply, IsOpenEmbedding.localOrientationEquiv_trans]
    exact (congrArg (fun e ↦ e.symm z) (IsOpenEmbedding.localOrientationEquiv_trans hk
      hV.isOpenEmbedding_subtypeVal x d)).symm
  rw [e]
  exact hk.localHomologyMap_localOrientationEquiv_symm x _ h

end Topology.IsOpenEmbedding

namespace TauCeti

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1))
  {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E₁ : M → Type}
  [TopologicalSpace (TotalSpace F' E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F' E₁] [VectorBundle ℝ F' E₁]
  (o' : VectorBundleOrientation F' E₁ (Fin (n + 1))) (hF' : finrank ℝ F' = n + 1)

/-- **Local indices along fibrewise isomorphisms over open embeddings.** Let `j : M₁ → M` be an
open embedding, `oM.comap hj` the orientation of `M₁` pulled back from `oM`, and
`φ x : E₁_x ≃ E_{j x}` a fibrewise isomorphism over `j`, with continuous total-space map, carrying
the orientation `o₁` of `E₁` to the orientation `o` of `E`. If `φ` carries a section `s₁` of `E₁`
to a section `s` of `E` along `j`, then the local index of `s₁` at `z` is the local index of `s`
at `j z`. -/
theorem sectionIndex_comap_eq_of_fiberwise {M₁ : Type} [TopologicalSpace M₁] [T2Space M₁]
    [ChartedSpace E' M₁] {F₁ : Type} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] {E₁ : M₁ → Type}
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module ℝ (E₁ x)]
    [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
    (o₁ : VectorBundleOrientation F₁ E₁ (Fin (n + 1))) (hF₁ : finrank ℝ F₁ = n + 1)
    {j : C(M₁, M)} (hj : Topology.IsOpenEmbedding j) {φ : ∀ x, E₁ x ≃L[ℝ] E (j x)}
    (hφ : Continuous fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F (j v.proj) (φ v.proj v.snd))
    (ho : ∀ x, Orientation.map (Fin (n + 1)) (φ x).toLinearEquiv (o₁ x) = o (j x))
    {s₁ : ∀ x, E₁ x} (hs₁ : Continuous fun x ↦ TotalSpace.mk' F₁ x (s₁ x))
    {s : ∀ x, E x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (hss : ∀ x, φ x (s₁ x) = s (j x)) (z : M₁) :
    o₁.sectionIndex hF₁ (oM.comap hj) hs₁ z = o.sectionIndex hF oM hs (j z) := by
  have hzero : ∀ x, s (j x) = 0 ↔ s₁ x = 0 := fun x ↦ by rw [← hss, (φ x).map_eq_zero_iff]
  by_cases h : ∃ U, IsOpen U ∧ z ∈ U ∧ ∀ x ∈ U, s₁ x = 0 → x = z
  · obtain ⟨U, hU, hz, hUz⟩ := h
    -- The image `j(U)` isolates `j z`, and `j` restricts to a map `k : U → j(U)`.
    have hV : IsOpen (j '' U) := hj.isOpenMap U hU
    have hjz : j z ∈ j '' U := mem_image_of_mem j hz
    have hVz : ∀ y ∈ j '' U, s y = 0 → y = j z := by
      rintro _ ⟨x, hx, rfl⟩ h0
      rw [hUz x hx ((hzero x).1 h0)]
    let k : C(U, j '' U) :=
      ContinuousMap.mk ((mapsTo_image j U).restrict j U (j '' U)) (hj.continuous.restrict _)
    have hkz : k ⁻¹' {⟨j z, hjz⟩} ⊆ {⟨z, hz⟩} := fun x hx ↦
      Subtype.ext (hj.injective (congrArg Subtype.val hx :))
    -- `k` carries the local orientation of `U` at `z` to that of `j(U)` at `j z`.
    have hexc : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) k hkz (n + 1)
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM.comap hj z).val) =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hV.isOpenEmbedding_subtypeVal ⟨j z, hjz⟩ (n + 1)).inv (oM (j z)).val := by
      have := hj.localHomologyMap_restrict_localOrientationEquiv_symm hU hV (mapsTo_image j U)
        ⟨z, hz⟩ (oM (j z)) hkz
      rwa [← HomologicalOrientation.comap_apply,
        Topology.IsOpenEmbedding.coe_localOrientationEquiv_symm,
        Topology.IsOpenEmbedding.coe_localOrientationEquiv_symm] at this
    rw [sectionIndex_eq o₁ hF₁ _ hs₁ hU hz hUz, sectionIndex_eq o hF oM hs hV hjz hVz, ← hexc,
      ← singularCohomologyMap_thomPairMapOfFiberwise_thomClass o hF o₁ hF₁ hφ ho,
      ← TopPair.singularCohomologyMap_comp_apply,
      thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_comp_eq _ _ hφ
        (f' := ⟨fun x : U ↦ TotalSpace.mk' F (j x.val) (s (j x.val)),
          (hs.comp j.continuous).comp continuous_subtypeVal⟩)
        (ContinuousMap.ext fun x ↦ by simp [hss])
        (fun x hx h0 ↦ hx (Subtype.ext (hUz x.val x.property ((hzero x.val).1 h0)))),
      ← ofSubsetMap_comp_thomPairMapOfNeZero_of_comp_eq
        ⟨fun x : j '' U ↦ TotalSpace.mk' F x.val (s x.val), hs.comp continuous_subtypeVal⟩
        (S := {⟨j z, hjz⟩}) (fun x hx h0 ↦ hx (Subtype.ext (hVz x.val x.property h0))) k
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 hkz))
        (f' := ⟨fun x : U ↦ TotalSpace.mk' F (j x.val) (s (j x.val)),
          (hs.comp j.continuous).comp continuous_subtypeVal⟩) (rfl),
      TopPair.singularCohomologyMap_comp_apply, TopPair.singularKronecker_naturality,
      localHomologyMap_def]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  · rw [sectionIndex_of_not_isolated _ _ _ _ h, sectionIndex_of_not_isolated]
    rintro ⟨V, hV, hz, hVz⟩
    exact h ⟨j ⁻¹' V, hV.preimage j.continuous, hz, fun x hx h0 ↦
      hj.injective (hVz (j x) hx ((hzero x).2 h0))⟩

/-- **Local indices along fibrewise isomorphisms.** Let `φ x : E₁_x ≃ E_x` be a fibrewise
isomorphism, with continuous total-space map, that carries the orientation `o'` of `E₁` to the
orientation `o` of `E`. Then the local index of a section `s` of `E₁` at `z` is the local index of
the section `x ↦ φ x (s x)` of `E` at `z`. -/
theorem sectionIndex_eq_of_fiberwise {φ : ∀ x, E₁ x ≃L[ℝ] E x}
    (hφ : Continuous fun v : TotalSpace F' E₁ ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd))
    (ho : ∀ x, Orientation.map (Fin (n + 1)) (φ x).toLinearEquiv (o' x) = o x)
    {s : ∀ x, E₁ x} (hs : Continuous fun x ↦ TotalSpace.mk' F' x (s x)) (z : M) :
    o'.sectionIndex hF' oM hs z =
      o.sectionIndex hF oM (s := fun x ↦ φ x (s x)) (hφ.comp hs) z := by
  have h := sectionIndex_comap_eq_of_fiberwise o hF oM o' hF' (j := ContinuousMap.id M)
    Topology.IsOpenEmbedding.id hφ ho hs (hφ.comp hs) (fun _ ↦ rfl) z
  convert h using 2
  · exact (HomologicalOrientation.comap_id oM).symm
  · exact (ContinuousMap.id_apply z).symm

end VectorBundleOrientation

end TauCeti

end
