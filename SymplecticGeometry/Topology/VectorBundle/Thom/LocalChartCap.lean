/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
public import SymplecticGeometry.Topology.Category.TopCat.Monoidal
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalChart
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalHomologyRestriction
public import SymplecticGeometry.Topology.VectorBundle.ZeroSection

/-!
# The cap product of an excisive couple, read in a local chart of the total space

Let `E → B` be a real vector bundle with model fibre `P`, `e` a linear trivialization, `c` a chart
of the base at `b` with `c b = 0`, and `ι : P × S → E` the chart
`Bundle.Trivialization.localChart` of the total space, so that local homology at `0_b` is local
homology of `P × Q` at the origin (`Bundle.Trivialization.localChartLocalHomologyIso`).

For a class `a ∈ Hʳ(E, E ∖ 0)` and a class `a' ∈ Hʳ(P × Q, (P ∖ 0) × Q)` that agree on `P × S`
(their pull-backs along `ι` and along the inclusion `j : P × S → P × Q` are equal), the following
two maps `Hₙ(P × Q, P × Q ∖ 0) ⟶ H_q(Q, Q ∖ 0)`, `r + q = n`, are equal
(`Bundle.Trivialization.localChartLocalHomologyIso_hom_comp_singularRelativeCap`):

* carry a class to `Hₙ(E, E ∖ 0_b)` by the chart, read it relative to `E ∖ 0 ∪ E ∖ E_b`, cap it
  with `a` by the cap product of the excisive couple `(E ∖ 0, E ∖ E_b)`
  (`TopCat.singularRelativeCap`), push the result forward along the projection to
  `H_q(B, B ∖ b)` and read it in `c`;
* read the class relative to `(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, cap it with `a'` by the cap product of
  the couple `((P ∖ 0) × Q, P × (Q ∖ 0))`, and push the result forward along the second
  projection.

The second map is the one that `AlgebraicTopology/Cohomology/Cap/ProdLocal.lean` computes. The
first is built on the cap product of the excisive couple, at the point `b`, with which the
hypothesis of `TauCeti.HomologicalOrientation.map_singularCap_eq_fundamentalClass` is stated.

The proof is the naturality of the cap product of an excisive couple
(`TopCat.singularRelativeCap_naturality`), once along `ι` and once along `j`, applied to the class
of `P × S` from which excision recovers the given class; read in the chart, the projection of the
bundle is the second projection.

## Main results

* `Bundle.Trivialization.localChartLocalHomologyIso_hom_comp_singularRelativeCap`: the cap product
  of the excisive couple carried through the chart.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, Section 6 (the cap product and its
  naturality).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §11 (the Thom class, computed in a local trivialization).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Set Topology TauCeti

namespace Bundle.Trivialization

universe u v w

variable {B : Type w} [TopologicalSpace B] {P : Type w} [TopologicalSpace P] {E : B → Type w}
  [TopologicalSpace (TotalSpace P E)] {e : Trivialization P (π P E)} {Q : Type w}
  [TopologicalSpace Q] {c : OpenPartialHomeomorph B Q} {S : Set Q}
  [∀ b, AddCommMonoid (E b)] [AddCommMonoid P] [Module ℝ P] [∀ b, Module ℝ (E b)]
  [e.IsLinear ℝ]

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable [∀ b, TopologicalSpace (E b)] [FiberBundle P E] [Zero Q] [T1Space B] [T1Space P]
  [T1Space Q] [T1Space (TotalSpace P E)] {b : B}
  {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S' T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
  (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S') (μ : M ⊗ S' ⟶ N)

/-- **The cap product of an excisive couple, carried through the chart of the total space.** Let
`a ∈ Hʳ(E, E ∖ 0)` and `a' ∈ Hʳ(P × Q, (P ∖ 0) × Q)` have the same pull-back to
`(P × S, (P ∖ 0) × S)`, along the chart and along the inclusion. Then, for `r + q = n`, carrying a
class of `Hₙ(P × Q, P × Q ∖ 0)` to `Hₙ(E, E ∖ 0_b)` by the chart, reading it relative to
`E ∖ 0 ∪ E ∖ E_b`, capping with `a` by the cap product of the excisive couple `(E ∖ 0, E ∖ E_b)`,
pushing forward along the projection to `H_q(B, B ∖ b)` and reading the result in `c` (excision to
the source of `c`, then `c`) is reading the class relative to `(P ∖ 0) × Q ∪ P × (Q ∖ 0)`, capping
with `a'` by the cap product of the couple `((P ∖ 0) × Q, P × (Q ∖ 0))` and pushing forward along
the second projection to `H_q(Q, Q ∖ 0)`. -/
theorem localChartLocalHomologyIso_hom_comp_singularRelativeCap (hS : IsOpen S)
    (hSc : S ⊆ c.target) (hSe : MapsTo c.symm S e.baseSet) (hb : b ∈ c.source) (hcb : c b = 0)
    (h0 : (0 : Q) ∈ S)
    (hU : IsOpen ((↑) ⁻¹' (zeroSectionCompl P E : Set (TopCat.of (TotalSpace P E))) :
      Set ↥((zeroSectionCompl P E : Set (TopCat.of (TotalSpace P E))) ∪
        TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹' ({b}ᶜ : Set (TopCat.of B)))))
    {r q n : ℕ} (hn : r + q = n)
    (a : (TopPair.ofSubset (X := TopCat.of (TotalSpace P E))
      (zeroSectionCompl P E)).singularCohomology R k M r)
    (a' : (TopPair.ofSubset
      (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))).singularCohomology R k M r)
    (ha : TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (B := {x | x.val.1 ≠ 0})
          (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
            TopCat.of (univ ×ˢ S : Set (P × Q)) ⟶ TopCat.of P ⊗ TopCat.of Q)
          fun _ hw ↦ hw) r a' =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (B := {x | x.val.1 ≠ 0})
          (TopCat.ofHom ⟨e.localChart c S, (isOpenEmbedding_localChart hS hSc hSe).continuous⟩ :
            TopCat.of (univ ×ˢ S : Set (P × Q)) ⟶ TopCat.of (TotalSpace P E))
          (localChart_preimage_zeroSectionCompl hSe).superset) r a) :
    (localChartLocalHomologyIso T hS hSc hSe hb hcb h0 n).hom ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
          (zeroSectionCompl_union_compl_preimage_singleton b).superset hv) T n ≫
        TopCat.singularRelativeCap k u μ _
          (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹' ({b}ᶜ : Set (TopCat.of B)))
          hU ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P E)).preimage
            continuous_subtypeVal) r q n hn a ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩)
            (mapsTo_preimage _ ({b}ᶜ : Set (TopCat.of B)))) N q ≫
        ((localHomologyIsoOfIsOpenEmbedding N c.open_source.isOpenEmbedding_subtypeVal
          ⟨b, hb⟩ q).inv : localHomology N {b} q ⟶ _) ≫
        localHomologyMap N c.sourceRestrict
          (hcb ▸ (c.sourceRestrict_preimage_singleton hb).subset) q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _
          (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
            (0 : P) (0 : Q))) T n ≫
        TopCat.singularRelativeCap k u μ
          (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P)))
          (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q)))
          (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
          (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton)
          r q n hn a' ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap (snd (TopCat.of P) (TopCat.of Q)) (mapsTo_preimage _ _)) N q := by
  have hW := (isOpen_univ.prod hS).isOpenEmbedding_subtypeVal (X := P × Q)
  have h0' : ((0, 0) : P × Q) ∈ univ ×ˢ S := mk_mem_prod (mem_univ _) h0
  have hpt := (localChart_preimage_singleton_zeroSection hS hSc hSe hb hcb h0).subset
  -- Both sides are computed on the class of `P × S` from which excision recovers the given one.
  rw [← cancel_epi (localHomologyIsoOfIsOpenEmbedding T hW ⟨(0, 0), h0'⟩ n).hom,
    localChartLocalHomologyIso_hom _ hS hSc hSe hb hcb h0 hpt, Category.assoc,
    Iso.hom_inv_id_assoc]
  -- The subsets of `P × S` on which the couple is read, and the maps out of `P × S`.
  let UW : Set (TopCat.of (univ ×ˢ S : Set (P × Q))) := {x | x.val.1 ≠ 0}
  let VW : Set (TopCat.of (univ ×ˢ S : Set (P × Q))) := (Subtype.val ⁻¹' (Prod.snd ⁻¹' {0}))ᶜ
  let ι : TopCat.of (univ ×ˢ S : Set (P × Q)) ⟶ TopCat.of (TotalSpace P E) :=
    TopCat.ofHom ⟨e.localChart c S, (isOpenEmbedding_localChart hS hSc hSe).continuous⟩
  let j : TopCat.of (univ ×ˢ S : Set (P × Q)) ⟶ TopCat.of P ⊗ TopCat.of Q :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩
  have hιU : MapsTo ι UW (zeroSectionCompl P E) :=
    (localChart_preimage_zeroSectionCompl hSe).superset
  have hιV : MapsTo ι VW
      (TopCat.ofHom ⟨π P E, FiberBundle.continuous_proj P E⟩ ⁻¹' ({b}ᶜ : Set (TopCat.of B))) :=
    fun w hw ↦ (proj_localChart_eq_iff hSc hSe hb hcb w).not.2 hw
  have hjU : MapsTo j UW (fst (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of P))) :=
    fun _ hw ↦ hw
  have hjV : MapsTo j VW (snd (TopCat.of P) (TopCat.of Q) ⁻¹' ({0}ᶜ : Set (TopCat.of Q))) :=
    fun _ hw ↦ hw
  have hy : MapsTo (𝟙 (TopCat.of (univ ×ˢ S : Set (P × Q)))) {⟨(0, 0), h0'⟩}ᶜ (UW ∪ VW) := by
    rintro ⟨⟨v, w⟩, hvw⟩ h
    by_contra h'
    simp only [mem_union, mem_preimage, mem_compl_iff, mem_singleton_iff, mem_ofPred_eq, ne_eq,
      not_or, not_not, UW, VW] at h'
    exact h (Subtype.ext (Prod.ext h'.1 h'.2))
  have hUW : IsOpen ((↑) ⁻¹' UW : Set ↥(UW ∪ VW)) :=
    ((isOpen_compl_singleton.preimage continuous_fst).preimage continuous_subtypeVal).preimage
      continuous_subtypeVal
  have hVW : IsOpen ((↑) ⁻¹' VW : Set ↥(UW ∪ VW)) :=
    ((isClosed_singleton.preimage continuous_snd).preimage
      continuous_subtypeVal).isOpen_compl.preimage continuous_subtypeVal
  -- Read relative to the couples, the chart and the inclusion of `P × S` are maps of couples.
  have h1 : localHomologyMap T
        (.mk (e.localChart c S) (isOpenEmbedding_localChart hS hSc hSe).continuous) hpt n ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
        (zeroSectionCompl_union_compl_preimage_singleton b).superset hv) T n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hy) T n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap ι (hιU.union_union hιV)) T n := by
    rw [localHomologyMap_def, ← TopPair.singularHomologyMap_comp,
      ← TopPair.singularHomologyMap_comp]
    exact congrArg (TopPair.singularHomologyMap · T n)
      (TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ hy (hιU.union_union hιV)
        (by rw [Category.comp_id, Category.id_comp]))
  have h2 : (localHomologyIsoOfIsOpenEmbedding T hW ⟨(0, 0), h0'⟩ n).hom ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _
        (TopCat.mapsTo_compl_singleton_preimage_fst_compl_union_preimage_snd_compl
          (0 : P) (0 : Q))) T n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hy) T n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap j (hjU.union_union hjV)) T n := by
    rw [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyMap_def,
      ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp]
    -- `TopCat.of P ⊗ TopCat.of Q` unfolds to `TopCat.of (P × Q)`, so `j` followed by the
    -- identity of `P × Q`, which is `(TopCat.tensorObjIsoProd P Q).hom`, is the inclusion.
    exact congrArg (TopPair.singularHomologyMap · T n)
      (TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ hy (hjU.union_union hjV)
        (by rw [Category.id_comp, Iso.comp_inv_eq, TopCat.tensorObjIsoProd_hom_eq_id]; rfl))
  -- `ha` writes the chart, the inclusion and `UW` out, while the goal has the local definitions
  -- `ι`, `j` and `UW`, which `rw` does not unfold; so `ha` is restated through them first.
  rw [reassoc_of% h1, reassoc_of% h2,
    ← reassoc_of% (TopCat.singularRelativeCap_naturality k u μ hUW hVW hU
      ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P E)).preimage
        continuous_subtypeVal) ι hιU hιV r q n hn a),
    ← reassoc_of% (TopCat.singularRelativeCap_naturality k u μ hUW hVW
      (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union isOpen_compl_singleton)
      (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union isOpen_compl_singleton) j hjU hjV
      r q n hn a'),
    show TopPair.singularCohomologyMap (TopPair.ofSubsetMap j hjU) r a' =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap ι hιU) r a from ha]
  congr 2
  -- Read in the charts, the projection of the bundle is the second projection.
  have h3 := localHomologyMap_localChart_comp_localHomologyMap_proj N hS hSc hSe hb hcb q
  simp only [localHomologyMap_def] at h3 ⊢
  -- The two sides differ only by the local definitions `ι`, `VW` and `j`, and by the second
  -- projection of the product `TopCat.of P ⊗ TopCat.of Q`, which is `Prod.snd` by definition.
  exact h3

end Bundle.Trivialization

end
