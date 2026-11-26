/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Topology.VectorBundle.Trivialization

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
`P × S` (`TauCeti.isIso_localHomologyMap`). The second isomorphism restricts to the first, and
it carries the map induced by the projection of the bundle, read through `c`, to the map induced
by the second projection.

## Main results

* `Bundle.Trivialization.localChart`: the chart, and
  `Bundle.Trivialization.isOpenEmbedding_localChart`: it is an open embedding.
* `Bundle.Trivialization.localChart_zero`,
  `Bundle.Trivialization.localChart_mem_range_zeroSection_iff`,
  `Bundle.Trivialization.localChart_preimage_proj_preimage`,
  `Bundle.Trivialization.proj_comp_localChart`: where the chart sends the origin, which points it
  sends to the zero section and to the fibre over `b`, and how it meets the projection.
* `Bundle.Trivialization.localChartLocalHomologyIso` and
  `Bundle.Trivialization.localChartFiberLocalHomologyIso`: the isomorphisms of local homology at
  the origin and along `P × {0}`, characterized by
  `Bundle.Trivialization.localHomologyMap_comp_localChartLocalHomologyIso_hom` and
  `Bundle.Trivialization.localHomologyMap_comp_localChartFiberLocalHomologyIso_hom`.
* `Bundle.Trivialization.localChartFiberLocalHomologyIso_hom_comp_localHomologyRestriction`: the
  isomorphism along the fibre restricts to the isomorphism at the point.
* `Bundle.Trivialization.localChartFiberLocalHomologyIso_hom_comp_localHomologyMap_proj`: the
  square with the projection of the bundle and the second projection.

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

variable {B : Type w} [TopologicalSpace B] {P : Type w} [NormedAddCommGroup P]
  {E : B → Type w} [TopologicalSpace (TotalSpace P E)]
  (e : Trivialization P (π P E)) {Q : Type w} [NormedAddCommGroup Q]
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
  exact Φ.isOpenEmbedding_domRestrict (isOpen_univ.prod hS) hW

variable {b : B}

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

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) [T1Space B]
  [∀ b, TopologicalSpace (E b)] [FiberBundle P E]

/-- **The chart identifies the local homology along `P × {0}` with that along the fibre `E_b`.**
Excision to the open set `P × S` followed by the chart `Bundle.Trivialization.localChart`
identifies `Hₖ(P × Q, P × Q ∖ (P × {0}))` with `Hₖ(E, E ∖ E_b)`, the model fibre first. -/
def localChartFiberLocalHomologyIso (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (k : ℕ) :
    localHomology R (Prod.snd ⁻¹' {0} : Set (P × Q)) k ≅ localHomology R (π P E ⁻¹' {b}) k :=
  have hW := (isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)
  have hj := isOpenEmbedding_localChart hS hSc hSe
  have := isIso_localHomologyMap R (.mk Subtype.val continuous_subtypeVal) hW
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) rfl (isClosed_singleton.preimage continuous_snd)
    (fun x (hx : x.2 = 0) ↦ ⟨⟨x, mem_univ _, hx ▸ h0⟩, rfl⟩) k
  have := isIso_localHomologyMap R (.mk (e.localChart c S) hj.continuous) hj
    (localChart_preimage_proj_preimage hSc hSe hb hcb)
    (isClosed_singleton.preimage (FiberBundle.continuous_proj P E))
    (proj_preimage_subset_range_localChart hSe hb hcb h0) k
  (asIso (localHomologyMap R (.mk Subtype.val continuous_subtypeVal)
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k)).symm ≪≫
      asIso (localHomologyMap R (.mk (e.localChart c S) hj.continuous)
        (localChart_preimage_proj_preimage hSc hSe hb hcb).subset k)

/-- The isomorphism `Bundle.Trivialization.localChartFiberLocalHomologyIso`, preceded by excision
to `P × S`, is the map induced by the chart. -/
@[reassoc]
theorem localHomologyMap_comp_localChartFiberLocalHomologyIso_hom (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S)
    (h : e.localChart c S ⁻¹' (π P E ⁻¹' {b}) ⊆ Subtype.val ⁻¹' (Prod.snd ⁻¹' {0})) (k : ℕ) :
    localHomologyMap R (.mk Subtype.val continuous_subtypeVal)
        (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k ≫
        (localChartFiberLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom =
      localHomologyMap R (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous)
        h k := by
  rw [localChartFiberLocalHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id_assoc, asIso_hom]

/-- **The chart carries the projection of the bundle to the second projection.** The isomorphism
`Bundle.Trivialization.localChartFiberLocalHomologyIso`, followed by the map
`Hₖ(E, E ∖ E_b) ⟶ Hₖ(B, B ∖ {b})` induced by the projection and by the reading of local homology
at `b` in the chart `c` (excision to the source of `c`, then `c`), is the map
`Hₖ(P × Q, P × Q ∖ (P × {0})) ⟶ Hₖ(Q, Q ∖ {0})` induced by the second projection. -/
theorem localChartFiberLocalHomologyIso_hom_comp_localHomologyMap_proj (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) (h : c.sourceRestrict ⁻¹' {0} ⊆ {(⟨b, hb⟩ : c.source)}) (k : ℕ) :
    (localChartFiberLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom ≫
        localHomologyMap R (.mk (π P E) (FiberBundle.continuous_proj P E))
          (T := {((⟨b, hb⟩ : c.source) : B)}) subset_rfl k ≫
        (localHomologyIsoOfIsOpenEmbedding R c.open_source.isOpenEmbedding_subtypeVal
          (⟨b, hb⟩ : c.source) k).inv ≫ localHomologyMap R c.sourceRestrict h k =
      localHomologyMap R (.mk Prod.snd continuous_snd) (T := {(0 : Q)})
        (S := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k := by
  have hW := (isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)
  have := isIso_localHomologyMap R (.mk Subtype.val continuous_subtypeVal) hW
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) rfl (isClosed_singleton.preimage continuous_snd)
    (fun x (hx : x.2 = 0) ↦ ⟨⟨x, mem_univ _, hx ▸ h0⟩, rfl⟩) k
  rw [← cancel_epi (localHomologyMap R (.mk Subtype.val continuous_subtypeVal)
    (S := (Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}) : Set (univ ×ˢ S : Set (P × Q))))
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k),
    localHomologyMap_comp_localChartFiberLocalHomologyIso_hom_assoc _ _ _ _ _ _ _
      (localChart_preimage_proj_preimage hSc hSe hb hcb).subset, localHomologyMap_comp_assoc]
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
  rw [key, Category.assoc, Iso.hom_inv_id_assoc, localHomologyMap_comp, localHomologyMap_comp]
  refine localHomologyMap_congr R (ContinuousMap.ext fun x ↦ ?_) _ k
  rw [ContinuousMap.comp_apply, c.sourceRestrict_apply]
  exact c.right_inv (hSc x.property.2)

end FiberLocalHomology

variable [∀ b, AddCommMonoid (E b)]

/-- Over the base set of `e`, the chart sends `(v, q)` to the vector `e.symm (c.symm q) v` over
`c.symm q`. -/
theorem localChart_apply (hSe : MapsTo c.symm S e.baseSet) (x : (univ ×ˢ S : Set (P × Q))) :
    e.localChart c S x = ⟨c.symm x.val.2, e.symm (c.symm x.val.2) x.val.1⟩ := by
  rw [localChart_def, e.mk_symm (hSe x.property.2)]

variable [NormedSpace ℝ P] [∀ b, Module ℝ (E b)] [e.IsLinear ℝ]

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

/-- The chart sends the origin to the point `0_b` of the zero section. -/
theorem localChart_zero (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S) :
    e.localChart c S ⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩ = zeroSection P E b := by
  obtain rfl : c.symm 0 = b := by rw [← hcb, c.left_inv hb]
  rw [localChart_apply hSe]
  exact TotalSpace.ext rfl (heq_of_eq ((not_iff_not.1 (e.symm_apply_ne_zero_iff ℝ (hSe h0))).2 rfl))

section LocalHomology

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- **The chart identifies the local homology at the origin with that at `0_b`.** Excision to the
open set `P × S` followed by the chart `Bundle.Trivialization.localChart` identifies
`Hₖ(P × Q, P × Q ∖ {(0, 0)})` with `Hₖ(E, E ∖ {0_b})`, the model fibre first. -/
def localChartLocalHomologyIso [T1Space (TotalSpace P E)] (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (k : ℕ) : localHomology R {((0, 0) : P × Q)} k ≅ localHomology R {zeroSection P E b} k :=
  have hW := (isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)
  have hj := isOpenEmbedding_localChart hS hSc hSe
  have h : e.localChart c S ⁻¹' {zeroSection P E b} =
      (Subtype.val ⁻¹' {((0, 0) : P × Q)} : Set (univ ×ˢ S : Set (P × Q))) := by
    rw [← localChart_zero hSe hb hcb h0, ← image_singleton, hj.injective.preimage_image]
    exact ext fun x ↦ Subtype.ext_iff
  have := isIso_localHomologyMap R (.mk Subtype.val continuous_subtypeVal) hW
    (T := {((0, 0) : P × Q)}) rfl isClosed_singleton
    (singleton_subset_iff.2 ⟨⟨(0, 0), mk_mem_prod (mem_univ _) h0⟩, rfl⟩) k
  have := isIso_localHomologyMap R (.mk (e.localChart c S) hj.continuous) hj h isClosed_singleton
    (singleton_subset_iff.2 ⟨_, localChart_zero hSe hb hcb h0⟩) k
  (asIso (localHomologyMap R (.mk Subtype.val continuous_subtypeVal) (T := {((0, 0) : P × Q)})
    subset_rfl k)).symm ≪≫ asIso (localHomologyMap R (.mk (e.localChart c S) hj.continuous)
      h.subset k)

/-- The isomorphism `Bundle.Trivialization.localChartLocalHomologyIso`, preceded by excision to
`P × S`, is the map induced by the chart. -/
@[reassoc]
theorem localHomologyMap_comp_localChartLocalHomologyIso_hom
    [T1Space (TotalSpace P E)] (hS : IsOpen S) (hSc : S ⊆ c.target)
    (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0) (h0 : (0 : Q) ∈ S)
    (h : e.localChart c S ⁻¹' {zeroSection P E b} ⊆ Subtype.val ⁻¹' {((0, 0) : P × Q)})
    (k : ℕ) :
    localHomologyMap R (.mk Subtype.val continuous_subtypeVal) (T := {((0, 0) : P × Q)})
        subset_rfl k ≫ (localChartLocalHomologyIso R hS hSc hSe hb hcb h0 k).hom =
      localHomologyMap R (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous)
        h k := by
  rw [localChartLocalHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc,
    asIso_hom]

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
  have hW := (isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)
  have := isIso_localHomologyMap R (.mk Subtype.val continuous_subtypeVal) hW
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) rfl (isClosed_singleton.preimage continuous_snd)
    (fun x (hx : x.2 = 0) ↦ ⟨⟨x, mem_univ _, hx ▸ h0⟩, rfl⟩) k
  have hpt : (Subtype.val ⁻¹' {((0, 0) : P × Q)} : Set (univ ×ˢ S : Set (P × Q))) ⊆
      Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}) := fun x (hx : x.val = (0, 0)) ↦ by
    simp [hx]
  rw [← cancel_epi (localHomologyMap R (.mk Subtype.val continuous_subtypeVal)
    (S := (Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}) : Set (univ ×ˢ S : Set (P × Q))))
    (T := (Prod.snd ⁻¹' {0} : Set (P × Q))) subset_rfl k),
    localHomologyMap_comp_localChartFiberLocalHomologyIso_hom_assoc _ _ _ _ _ _ _
      (localChart_preimage_proj_preimage hSc hSe hb hcb).subset,
    localHomologyMap_comp_localHomologyRestriction,
    localHomologyMap_comp_localHomologyRestriction_assoc,
    ← localHomologyRestriction_comp_localHomologyMap R (.mk Subtype.val continuous_subtypeVal)
      (T := {((0, 0) : P × Q)}) hpt subset_rfl k, Category.assoc,
    localHomologyMap_comp_localChartLocalHomologyIso_hom,
    localHomologyRestriction_comp_localHomologyMap]
  exact fun x hx ↦ congrArg Subtype.val ((isOpenEmbedding_localChart hS hSc hSe).injective
    (hx.trans (localChart_zero hSe hb hcb h0).symm))

end LocalHomology

end Bundle.Trivialization

end
