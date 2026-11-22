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
orientation of `U` at `z` to that of `j(U)` at `j z`; this step adapts the one in Tau Ceti's proof
of `TauCeti.VectorBundleOrientation.sectionIndex_eq` that shrinks an isolating neighbourhood.

## Main results

* `TauCeti.thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq`: a map into the Thom pair of
  `E'`, followed by the map of Thom pairs of `φ`, is the map into the Thom pair of `E` of the
  composite.
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

namespace TauCeti

section ThomPair

variable {B : Type w} [TopologicalSpace B] {F : Type*} {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] {B' : Type w} [TopologicalSpace B'] {F' : Type*}
  {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)]
  [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)] {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')} {X : Type w} [TopologicalSpace X]

/-- A map `f : X → E'` that is nonzero off `S`, as a map of pairs into the Thom pair of `E'`,
followed by the map of Thom pairs of a fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}`, is the
map of pairs into the Thom pair of `E` given by `x ↦ φ (f x)`. -/
theorem thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq (f : C(X, TotalSpace F' E'))
    {S : Set X} (h : ∀ x ∉ S, (f x).snd ≠ 0)
    (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))
    {f' : C(X, TotalSpace F E)}
    (hf' : ∀ x, f' x = TotalSpace.mk' F (g (f x).proj) (φ (f x).proj (f x).snd))
    (h' : ∀ x ∉ S, (f' x).snd ≠ 0) :
    thomPairMapOfNeZero f h ≫ thomPairMapOfFiberwise hφ = thomPairMapOfNeZero f' h' := by
  refine TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ ?_)
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  -- The source of the pair is `X` only after unfolding `TopPair.ofSubset`.
  erw [thomPairMapOfNeZero_fst_apply, thomPairMapOfFiberwise_fst_apply,
    thomPairMapOfNeZero_fst_apply, hf']

end ThomPair

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
    let k : C(U, j '' U) := ⟨fun x ↦ ⟨j x.val, mem_image_of_mem j x.property⟩,
      (j.continuous.comp continuous_subtypeVal).subtype_mk _⟩
    have hkz : k ⁻¹' {⟨j z, hjz⟩} ⊆ {⟨z, hz⟩} := fun x hx ↦
      Subtype.ext (hj.injective (congrArg Subtype.val hx :))
    -- `k` carries the local orientation of `U` at `z` to that of `j(U)` at `j z`.
    have hexc : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) k hkz (n + 1)
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩ (n + 1)).inv (oM.comap hj z).val) =
        (localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          hV.isOpenEmbedding_subtypeVal ⟨j z, hjz⟩ (n + 1)).inv (oM (j z)).val := by
      -- Both sides map to `oM (j z)` under the excision isomorphism of `j(U)`, which is injective.
      refine (ConcreteCategory.bijective_of_isIso (localHomologyIsoOfIsOpenEmbedding
        (ModuleCat.of ℤ (ULift.{0} ℤ)) hV.isOpenEmbedding_subtypeVal ⟨j z, hjz⟩
        (n + 1)).hom).1 ?_
      have h₁ : (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M₁)) ⁻¹' {z} ⊆ {⟨z, hz⟩} :=
        fun x hx ↦ Subtype.ext hx
      have h₂ : j ⁻¹' {j z} ⊆ {z} := fun x hx ↦ hj.injective hx
      rw [Iso.inv_hom_id_apply, localHomologyIsoOfIsOpenEmbedding_hom,
        ← ConcreteCategory.comp_apply, localHomologyMap_comp,
        localHomologyMap_congr _ (show (⟨Subtype.val, continuous_subtypeVal⟩ : C(j '' U, M)).comp k
          = j.comp ⟨Subtype.val, continuous_subtypeVal⟩ from rfl),
        ← localHomologyMap_comp _ (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M₁)) j h₁ h₂,
        ConcreteCategory.comp_apply,
        ← localHomologyIsoOfIsOpenEmbedding_hom _ hU.isOpenEmbedding_subtypeVal ⟨z, hz⟩,
        Iso.inv_hom_id_apply,
        HomologicalOrientation.comap_apply]
      exact hj.localHomologyMap_localOrientationEquiv_symm z (oM (j z)) h₂
    rw [sectionIndex_eq o₁ hF₁ _ hs₁ hU hz hUz, sectionIndex_eq o hF oM hs hV hjz hVz, ← hexc,
      ← singularCohomologyMap_thomPairMapOfFiberwise_thomClass o hF o₁ hF₁ hφ ho,
      ← TopPair.singularCohomologyMap_comp_apply,
      thomPairMapOfNeZero_comp_thomPairMapOfFiberwise_of_eq _ _ hφ
        (f' := ⟨fun x : U ↦ TotalSpace.mk' F (j x.val) (s (j x.val)),
          (hs.comp j.continuous).comp continuous_subtypeVal⟩) (fun x ↦ by simp [hss])
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
