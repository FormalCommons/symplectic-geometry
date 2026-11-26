/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict
public import TauCeti.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Topology.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# A chart of the total space at a point of the zero section

Let `E → B` be a real vector bundle with model fibre `P`, `e` a linear trivialization of it and
`c : B → Q` a chart of the base with `c b = 0`. For an open set `S` of the target of `c` that
contains `0` and that `c.symm` carries into the base set of `e`, the map
`Bundle.Trivialization.localChart`, `(v, q) ↦ e.symm (c.symm q, v)` on `P × S`, is an open
embedding into the total space. It puts the fibre coordinate first: a trivialization puts the
base first, so the exchange of the two factors happens in this map. It sends the origin to the
point `0_b` of the zero section, the points of `{0} × S` to the zero section, and `P × {0}` onto
the fibre `E_b`; read in the chart, the projection of the bundle is the second projection.

So it identifies the local homology of `P × Q` at the origin with that of the total space at
`0_b` (`Bundle.Trivialization.localChartLocalHomologyIso`), and the local homology of `P × Q`
along `P × {0}` with that of the total space along `E_b`
(`Bundle.Trivialization.localChartFiberLocalHomologyIso`), each through excision to the open set
`P × S` (`TauCeti.localHomologyIsoOfIsOpenEmbeddingOfPreimage`, and at a point
`TauCeti.localHomologyIsoOfIsOpenEmbedding`). The second isomorphism restricts to the first, and
it carries the map induced by the projection of the bundle, read through `c`, to the map induced
by the second projection.

## Main results

* `Bundle.Trivialization.localChart`: the chart, and
  `Bundle.Trivialization.isOpenEmbedding_localChart`: it is an open embedding.
* `Bundle.Trivialization.localChart_zero`,
  `Bundle.Trivialization.localChart_preimage_singleton_zeroSection`,
  `Bundle.Trivialization.localChart_mem_range_zeroSection_iff`,
  `Bundle.Trivialization.localChart_preimage_zeroSectionCompl`,
  `Bundle.Trivialization.localChart_preimage_proj_preimage`,
  `Bundle.Trivialization.proj_comp_localChart`: where the chart sends the origin, which points it
  sends to the zero section and to the fibre over `b`, and how it meets the projection.
* `Bundle.Trivialization.localChartLocalHomologyIso` and
  `Bundle.Trivialization.localChartFiberLocalHomologyIso`: the isomorphisms of local homology at
  the origin and along `P × {0}`, characterized by
  `Bundle.Trivialization.localChartLocalHomologyIso_hom` and
  `Bundle.Trivialization.localChartFiberLocalHomologyIso_hom`;
  `Bundle.Trivialization.localHomologyPointClass_comp_localChartLocalHomologyIso_hom`: the first
  carries the class of the origin to the class of `0_b`.
* `Bundle.Trivialization.localChartFiberLocalHomologyIso_hom_comp_localHomologyRestriction`: the
  isomorphism along the fibre restricts to the isomorphism at the point.
* `Bundle.Trivialization.localHomologyMap_localChart_comp_localHomologyMap_proj` and
  `Bundle.Trivialization.localChartFiberLocalHomologyIso_hom_comp_localHomologyMap_proj`: the
  square with the projection of the bundle and the second projection, on `P × S` and through
  the isomorphism along the fibre.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  homology, computed by excision in a neighbourhood.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (the Thom class, computed in a local trivialization).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology TauCeti

universe w v u

namespace Bundle.Trivialization

variable {B : Type w} [TopologicalSpace B] {P : Type w} [TopologicalSpace P]
  {E : B → Type w} [TopologicalSpace (TotalSpace P E)]
  (e : Trivialization P (π P E)) {Q : Type w} [TopologicalSpace Q]
  (c : OpenPartialHomeomorph B Q) (S : Set Q)

/-- The chart of the total space of a bundle built from a trivialization `e` and a chart `c` of
the base: on the open set `P × S` of `P × Q`, the map `(v, q) ↦ e.symm (c.symm q, v)`. Its first
factor is the model fibre and its second the chart of the base; `e` takes the factors in the
other order, and the map exchanges them. -/
def localChart (x : (univ ×ˢ S : Set (P × Q))) : TotalSpace P E :=
  e.toOpenPartialHomeomorph.symm (c.symm x.val.2, x.val.1)

theorem localChart_def (x : (univ ×ˢ S : Set (P × Q))) :
    e.localChart c S x = e.toOpenPartialHomeomorph.symm (c.symm x.val.2, x.val.1) :=
  (rfl)

variable {e c S}

/-- The chart lies over `c.symm` of its second coordinate. -/
@[simp]
theorem proj_localChart (hSe : MapsTo c.symm S e.baseSet) (x : (univ ×ˢ S : Set (P × Q))) :
    (e.localChart c S x).proj = c.symm x.val.2 :=
  e.proj_symm_apply' (hSe x.property.2)

/-- Read in the chart, the projection of the bundle is `c.symm` of the second projection. -/
theorem proj_comp_localChart (hSe : MapsTo c.symm S e.baseSet) :
    π P E ∘ e.localChart c S = c.symm ∘ Prod.snd ∘ Subtype.val :=
  funext (proj_localChart hSe)

/-- The chart is an open embedding. -/
theorem isOpenEmbedding_localChart (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) : IsOpenEmbedding (e.localChart c S) := by
  -- The chart is the restriction of a composite of partial homeomorphisms to an open set of its
  -- source.
  let Φ := ((Homeomorph.prodComm P Q).toOpenPartialHomeomorph.trans
    (c.symm.prod (OpenPartialHomeomorph.refl P))).trans e.toOpenPartialHomeomorph.symm
  have hW : univ ×ˢ S ⊆ Φ.source := by
    rintro ⟨v, q⟩ ⟨-, hq : q ∈ S⟩
    have h₁ : q ∈ c.target := hSc hq
    have h₂ : c.symm q ∈ e.baseSet := hSe hq
    simp [Φ, e.target_eq, h₁, h₂]
  have hΦ : e.localChart c S = (univ ×ˢ S).domRestrict Φ := by
    funext x
    simp [localChart_def, Φ]
  rw [hΦ]
  exact Φ.isOpenEmbedding_domRestrict (isOpen_univ.prod hS) hW

section Linear

variable [∀ b, AddCommMonoid (E b)]

/-- Over the base set of `e`, the chart sends `(v, q)` to the vector `e.symm (c.symm q) v` over
`c.symm q`. -/
theorem localChart_apply (hSe : MapsTo c.symm S e.baseSet) (x : (univ ×ˢ S : Set (P × Q))) :
    e.localChart c S x = ⟨c.symm x.val.2, e.symm (c.symm x.val.2) x.val.1⟩ := by
  rw [localChart_def, e.mk_symm (hSe x.property.2)]

variable [AddCommMonoid P] [Module ℝ P] [∀ b, Module ℝ (E b)] [e.IsLinear ℝ]

/-- The chart sends a point to the zero section exactly when its first coordinate, the one in the
model fibre, is `0`. -/
theorem localChart_snd_eq_zero_iff (hSe : MapsTo c.symm S e.baseSet)
    (x : (univ ×ˢ S : Set (P × Q))) : (e.localChart c S x).snd = 0 ↔ x.val.1 = 0 := by
  rw [localChart_apply hSe]
  exact not_iff_not.1 (e.symm_apply_ne_zero_iff ℝ (hSe x.property.2))

/-- The chart sends a point into the zero section exactly when its first coordinate is `0`. -/
theorem localChart_mem_range_zeroSection_iff (hSe : MapsTo c.symm S e.baseSet)
    (x : (univ ×ˢ S : Set (P × Q))) :
    e.localChart c S x ∈ range (zeroSection P E) ↔ x.val.1 = 0 := by
  rw [← localChart_snd_eq_zero_iff hSe]
  exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ rfl, fun h ↦ ⟨_, TotalSpace.ext rfl (heq_of_eq h.symm)⟩⟩

/-- The chart pulls the nonzero vectors back to the points whose first coordinate, the one in the
model fibre, is nonzero. -/
theorem localChart_preimage_zeroSectionCompl (hSe : MapsTo c.symm S e.baseSet) :
    e.localChart c S ⁻¹' zeroSectionCompl P E = Subtype.val ⁻¹' (Prod.fst ⁻¹' {0}ᶜ) :=
  ext fun x ↦ mem_zeroSectionCompl.trans (localChart_snd_eq_zero_iff hSe x).not

end Linear

variable [Zero Q] {b : B}

/-- The chart sends a point to the fibre over `b` exactly when its second coordinate, the one in
the chart of the base, is `0`. -/
theorem proj_localChart_eq_iff (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet)
    (hb : b ∈ c.source) (hcb : c b = 0) (x : (univ ×ˢ S : Set (P × Q))) :
    (e.localChart c S x).proj = b ↔ x.val.2 = 0 := by
  have h0 : (0 : Q) ∈ c.target := hcb ▸ c.map_source hb
  rw [proj_localChart hSe, ← c.symm.injOn.eq_iff (hSc x.property.2) h0, ← hcb, c.left_inv hb]

/-- The preimage of the fibre over `b` under the chart is `P × {0}`. -/
theorem localChart_preimage_proj_preimage (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet)
    (hb : b ∈ c.source) (hcb : c b = 0) :
    e.localChart c S ⁻¹' (π P E ⁻¹' {b}) = Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}) :=
  ext fun x ↦ proj_localChart_eq_iff hSc hSe hb hcb x

/-- The chart covers the fibre over `b`. -/
theorem proj_preimage_subset_range_localChart (hSe : MapsTo c.symm S e.baseSet)
    (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S) :
    π P E ⁻¹' {b} ⊆ range (e.localChart c S) := by
  obtain rfl : c.symm 0 = b := by rw [← hcb, c.left_inv hb]
  intro v (hv : v.proj = c.symm 0)
  refine ⟨⟨((e v).2, 0), mk_mem_prod (mem_univ _) h0⟩, ?_⟩
  rw [localChart_def, ← hv]
  exact e.symm_apply_mk_proj (e.mem_source.2 (hv ▸ hSe h0))

section FiberLocalHomology

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) [T1Space Q]
  [T1Space B] [∀ b, TopologicalSpace (E b)] [FiberBundle P E]

/-- **The chart identifies the local homology along `P × {0}` with that along the fibre `E_b`.**
Excision to the open set `P × S` followed by the chart `Bundle.Trivialization.localChart`
identifies `Hₖ(P × Q, P × Q ∖ (P × {0}))` with `Hₖ(E, E ∖ E_b)`, the model fibre first. -/
def localChartFiberLocalHomologyIso (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (k : ℕ) :
    localHomology R (Prod.snd ⁻¹' {0} : Set (P × Q)) k ≅ localHomology R (π P E ⁻¹' {b}) k :=
  (localHomologyIsoOfIsOpenEmbeddingOfPreimage R
      ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)) rfl
      (isClosed_singleton.preimage continuous_snd)
      ((preimage_mono (singleton_subset_iff.2 h0)).trans
        (univ_prod.symm.subset.trans Subtype.range_coe.superset)) k).symm ≪≫
    localHomologyIsoOfIsOpenEmbeddingOfPreimage R (isOpenEmbedding_localChart hS hSc hSe)
      (localChart_preimage_proj_preimage hSc hSe hb hcb)
      (isClosed_singleton.preimage (FiberBundle.continuous_proj P E))
      (proj_preimage_subset_range_localChart hSe hb hcb h0) k

/-- The isomorphism `Bundle.Trivialization.localChartFiberLocalHomologyIso` is the inverse of
excision to `P × S` followed by the map induced by the chart. -/
theorem localChartFiberLocalHomologyIso_hom (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (h : e.localChart c S ⁻¹' (π P E ⁻¹' {b}) ⊆ Subtype.val ⁻¹' (Prod.snd ⁻¹' {0})) (k : ℕ) :
    (localChartFiberLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom =
      (localHomologyIsoOfIsOpenEmbeddingOfPreimage R
          ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)) rfl
          (isClosed_singleton.preimage continuous_snd)
          ((preimage_mono (singleton_subset_iff.2 h0)).trans
        (univ_prod.symm.subset.trans Subtype.range_coe.superset)) k).inv ≫
        localHomologyMap R
          (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous) h k := by
  rw [localChartFiberLocalHomologyIso, Iso.trans_hom, Iso.symm_hom,
    localHomologyIsoOfIsOpenEmbeddingOfPreimage_hom]

omit [T1Space Q] in
/-- **Read in the charts, the projection of the bundle is the second projection.** On `P × S`, the
map `Hₖ(P × S, P × S ∖ (P × {0})) ⟶ Hₖ(B, B ∖ {b})` induced by the chart of the total space and
then the projection, followed by the reading of local homology at `b` in the chart `c` (excision
to the source of `c`, then `c`), is the map to `Hₖ(Q, Q ∖ {0})` induced by the inclusion in
`P × Q` and then the second projection. -/
theorem localHomologyMap_localChart_comp_localHomologyMap_proj (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (k : ℕ) :
    localHomologyMap R (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous)
        (localChart_preimage_proj_preimage hSc hSe hb hcb).subset k ≫
        localHomologyMap R (.mk (π P E) (FiberBundle.continuous_proj P E))
          (T := {((⟨b, hb⟩ : c.source) : B)}) subset_rfl k ≫
        (localHomologyIsoOfIsOpenEmbedding R c.open_source.isOpenEmbedding_subtypeVal
          (⟨b, hb⟩ : c.source) k).inv ≫
        localHomologyMap R c.sourceRestrict
          (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) k =
      localHomologyMap R (ContinuousMap.subtypeVal (univ ×ˢ S : Set (P × Q)))
          (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k ≫
        localHomologyMap R (.mk Prod.snd continuous_snd) (T := {(0 : Q)}) subset_rfl k := by
  rw [localHomologyMap_comp_assoc, localHomologyMap_comp]
  -- Read in the chart, the projection of the bundle factors through the source of `c`.
  let γ : C((univ ×ˢ S : Set (P × Q)), c.source) :=
    ⟨fun x ↦ ⟨c.symm x.val.2, c.map_target (hSc x.property.2)⟩,
      (c.continuousOn_symm.comp_continuous (continuous_snd.comp continuous_subtypeVal)
        fun x ↦ hSc x.property.2).subtype_mk _⟩
  have hγ : γ ⁻¹' {⟨b, hb⟩} ⊆ Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}) := fun x hx ↦
    (proj_localChart_eq_iff hSc hSe hb hcb x).1
      ((proj_localChart hSe x).trans (congrArg Subtype.val hx))
  have key : localHomologyMap R ((ContinuousMap.mk (π P E) (FiberBundle.continuous_proj P E)).comp
      (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous))
        (T := {((⟨b, hb⟩ : c.source) : B)})
        ((preimage_mono subset_rfl).trans (localChart_preimage_proj_preimage hSc hSe hb hcb).subset)
        k =
      localHomologyMap R γ hγ k ≫ (localHomologyIsoOfIsOpenEmbedding R
        c.open_source.isOpenEmbedding_subtypeVal (⟨b, hb⟩ : c.source) k).hom := by
    rw [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyMap_comp]
    exact localHomologyMap_congr R (ContinuousMap.ext fun x ↦ proj_localChart hSe x) _ k
  rw [key, Category.assoc, Iso.hom_inv_id_assoc, localHomologyMap_comp]
  refine localHomologyMap_congr R (ContinuousMap.ext fun x ↦ ?_) _ k
  rw [ContinuousMap.comp_apply, c.sourceRestrict_apply]
  exact c.right_inv (hSc x.property.2)

/-- **The chart carries the projection of the bundle to the second projection.** The isomorphism
`Bundle.Trivialization.localChartFiberLocalHomologyIso`, followed by the map
`Hₖ(E, E ∖ E_b) ⟶ Hₖ(B, B ∖ {b})` induced by the projection and by the reading of local homology
at `b` in the chart `c` (excision to the source of `c`, then `c`), is the map
`Hₖ(P × Q, P × Q ∖ (P × {0})) ⟶ Hₖ(Q, Q ∖ {0})` induced by the second projection. -/
theorem localChartFiberLocalHomologyIso_hom_comp_localHomologyMap_proj (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) (k : ℕ) :
    (localChartFiberLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom ≫
        localHomologyMap R (.mk (π P E) (FiberBundle.continuous_proj P E))
          (T := {((⟨b, hb⟩ : c.source) : B)}) subset_rfl k ≫
        (localHomologyIsoOfIsOpenEmbedding R c.open_source.isOpenEmbedding_subtypeVal
          (⟨b, hb⟩ : c.source) k).inv ≫
        localHomologyMap R c.sourceRestrict
          (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) k =
      localHomologyMap R (.mk Prod.snd continuous_snd) (T := {(0 : Q)})
        (S := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k := by
  rw [localChartFiberLocalHomologyIso_hom _ _ _ _ _ _ _
      (localChart_preimage_proj_preimage hSc hSe hb hcb).subset, Category.assoc, Iso.inv_comp_eq,
    localHomologyIsoOfIsOpenEmbeddingOfPreimage_hom]
  exact localHomologyMap_localChart_comp_localHomologyMap_proj R hS hSc hSe hb hcb k

end FiberLocalHomology

variable [∀ b, AddCommMonoid (E b)] [AddCommMonoid P] [Module ℝ P] [∀ b, Module ℝ (E b)]
  [e.IsLinear ℝ]

/-- The chart sends the origin to the point `0_b` of the zero section. -/
theorem localChart_zero (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) :
    e.localChart c S ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ = zeroSection P E b := by
  obtain rfl : c.symm 0 = b := by rw [← hcb, c.left_inv hb]
  rw [localChart_apply hSe]
  exact TotalSpace.ext rfl (heq_of_eq ((not_iff_not.1 (e.symm_apply_ne_zero_iff ℝ (hSe h0))).2 rfl))

/-- The origin is the only point that the chart sends to the point `0_b` of the zero section. -/
theorem localChart_preimage_singleton_zeroSection (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S) :
    e.localChart c S ⁻¹' {zeroSection P E b} = {⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩} := by
  rw [← localChart_zero hSe hb hcb h0, ← image_singleton,
    (isOpenEmbedding_localChart hS hSc hSe).injective.preimage_image]

section LocalHomology

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) [T1Space P]
  [T1Space Q]

/-- **The chart identifies the local homology at the origin with that at `0_b`.** Excision to the
open set `P × S` followed by the chart `Bundle.Trivialization.localChart` identifies
`Hₖ(P × Q, P × Q ∖ {(0, 0)})` with `Hₖ(E, E ∖ {0_b})`, the model fibre first. -/
def localChartLocalHomologyIso [T1Space (TotalSpace P E)] (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (k : ℕ) : localHomology R {((0, 0) : P × Q)} k ≅ localHomology R {zeroSection P E b} k :=
  (localHomologyIsoOfIsOpenEmbedding R
      ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q))
      ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ k).symm ≪≫
    localHomologyIsoOfIsOpenEmbedding R (isOpenEmbedding_localChart hS hSc hSe) _ k ≪≫
    eqToIso (by rw [localChart_zero hSe hb hcb h0])

/-- The isomorphism `Bundle.Trivialization.localChartLocalHomologyIso` is the inverse of excision
to `P × S` followed by the map induced by the chart. -/
theorem localChartLocalHomologyIso_hom [T1Space (TotalSpace P E)] (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S)
    (h : e.localChart c S ⁻¹' {zeroSection P E b} ⊆
      {(⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ : (univ ×ˢ S : Set (P × Q)))})
    (k : ℕ) :
    (localChartLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom =
      (localHomologyIsoOfIsOpenEmbedding R
          ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q))
          ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ k).inv ≫
        localHomologyMap R
          (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous)
          (T := {zeroSection P E b}) h k := by
  -- The chart sends the origin to `0_b`; stated for any point `z` in place of `0_b`, the
  -- equation follows by `subst`.
  have key : ∀ {z : TotalSpace P E}
      (_ : e.localChart c S ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ = z)
      (h' : e.localChart c S ⁻¹' {z} ⊆ {⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩})
      (p : localHomology R {e.localChart c S ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩} k =
        localHomology R {z} k),
      (localHomologyIsoOfIsOpenEmbedding R (isOpenEmbedding_localChart hS hSc hSe)
          ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ k).hom ≫ eqToHom p =
        localHomologyMap R
          (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous)
          (S := {⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩}) (T := {z}) h' k := by
    rintro z rfl h' p
    rw [eqToHom_refl, Category.comp_id, localHomologyIsoOfIsOpenEmbedding_hom]
  rw [localChartLocalHomologyIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    key (localChart_zero hSe hb hcb h0) h]

/-- The isomorphism `Bundle.Trivialization.localChartLocalHomologyIso` carries the class of the
origin of `P × Q` in degree zero to the class of the point `0_b` of the zero section. -/
@[reassoc, elementwise]
theorem localHomologyPointClass_comp_localChartLocalHomologyIso_hom [T1Space (TotalSpace P E)]
    (hS : IsOpen S) (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source)
    (hcb : c b = 0) (h0 : (0 : Q) ∈ S) :
    localHomologyPointClass R {((0, 0) : P × Q)} (0, 0) ≫
        (localChartLocalHomologyIso R hS hSc hSe hb hcb h0 0).hom =
      localHomologyPointClass R {zeroSection P E b} (zeroSection P E b) := by
  rw [localChartLocalHomologyIso_hom _ _ _ _ _ _ _
      (localChart_preimage_singleton_zeroSection hS hSc hSe hb hcb h0).subset,
    ← localHomologyPointClass_comp_localHomologyIsoOfIsOpenEmbedding_hom R
      ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q))
      ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩,
    Category.assoc, Iso.hom_inv_id_assoc, localHomologyPointClass_map, ContinuousMap.coe_mk,
    localChart_zero hSe hb hcb h0]

/-- **The isomorphism along the fibre restricts to the isomorphism at the point.** Restricting
`Bundle.Trivialization.localChartFiberLocalHomologyIso` from the fibre `E_b` to its point `0_b` is
restricting from `P × {0}` to the origin followed by
`Bundle.Trivialization.localChartLocalHomologyIso`. -/
theorem localChartFiberLocalHomologyIso_hom_comp_localHomologyRestriction [T1Space B]
    [T1Space (TotalSpace P E)] [∀ b, TopologicalSpace (E b)] [FiberBundle P E] (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) (k : ℕ) :
    (localChartFiberLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom ≫
        localHomologyRestriction R
          (singleton_subset_iff.2 (zeroSection_proj P E b : _ ∈ π P E ⁻¹' {b})) k =
      localHomologyRestriction R
          (singleton_subset_iff.2 (rfl : ((0, 0) : P × Q).2 = 0)) k ≫
        (localChartLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom := by
  have hpt := (localChart_preimage_singleton_zeroSection hS hSc hSe hb hcb h0).subset
  rw [localChartFiberLocalHomologyIso_hom _ _ _ _ _ _ _
      (localChart_preimage_proj_preimage hSc hSe hb hcb).subset,
    localChartLocalHomologyIso_hom _ _ _ _ _ _ _ hpt, Category.assoc,
    localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap R _ (singleton_subset_iff.2 rfl) hpt k,
    Iso.inv_comp_eq, localHomologyIsoOfIsOpenEmbeddingOfPreimage_hom,
    localHomologyMap_comp_localHomologyRestriction_singleton_assoc R
      ((isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)) _
      (x := ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩) rfl, Iso.hom_inv_id_assoc]

end LocalHomology

end Bundle.Trivialization

end
