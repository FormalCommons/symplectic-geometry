/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import SymplecticGeometry.Geometry.Manifold.CenteredExtChartAt
public import SymplecticGeometry.Topology.VectorBundle.Thom.LocalHomologyRestriction
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.CategoryTheory.Monoidal.Preadditive
import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.FundamentalClass

/-!
# Push-forwards from the Thom pair that are fundamental classes, read in charts

Let `V → B` be a real vector bundle over a compact manifold `B` with a homological orientation
`o` of dimension `q`, and let `u ∈ Hʳ(V, V ∖ 0)` and `γ ∈ Hₙ(V, V ∖ 0)` with `r + q = n`. This
file gives a pointwise test for `π_*(u ⌢ γ) ∈ H_q(B)` to be the fundamental class of `o`: at
each `b : B`, compute the cap product with `u` of the local class of `γ` at the point `0_b` of
the zero section, push it forward to `H_q(B, B ∖ b)`, and compare it with `o b` after reading
both in the centred chart of `B` at `b`.

It is the general criterion
`TauCeti.HomologicalOrientation.map_singularCap_eq_fundamentalClass`
(`Cohomology/Cap/FundamentalClass.lean`), with the excisive couple `(V ∖ 0, V ∖ V_b)`, whose
union is the complement of `0_b` (`Bundle.zeroSectionCompl_union_compl_preimage_singleton`), so
that the local class of `γ` at `0_b` factors through the restriction of the Thom pair
(`SymplecticGeometry.thomPairLocalHomologyRestriction_comp_singularHomologyMap_ofSubsetMap`),
and with the
comparison made after the centred chart, which detects classes of local homology at `b`
(`OpenPartialHomeomorph.injective_localHomologyMap_sourceRestrict`).

## Main results

* `TauCeti.HomologicalOrientation.map_proj_singularCap_eq_fundamentalClass_of_centeredExtChartAt`:
  the pointwise criterion for `π_*(u ⌢ γ)` to be the fundamental class of the base of a vector
  bundle, read in centred charts.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products, local orientations and the fundamental class, Lemma 3.27).
-/

public section

noncomputable section

open Bundle CategoryTheory MonoidalCategory Module Set AlgebraicTopology

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace TauCeti.HomologicalOrientation

open SymplecticGeometry

variable {E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {B : Type}
  [TopologicalSpace B] [T2Space B] [CompactSpace B] [ChartedSpace H B] [ChartedSpace E B]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {V : B → Type}
  [TopologicalSpace (TotalSpace P V)] [∀ b, AddCommMonoid (V b)]
  [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle P V] [VectorBundle ℝ P V]

/-- **The pointwise criterion for a fundamental class, read in centred charts.** Let `V → B` be a
real vector bundle over a compact manifold `B` with a homological orientation `o` of dimension
`q`, and let `u ∈ Hʳ(V, V ∖ 0)` and `γ ∈ Hₙ(V, V ∖ 0)`, `r + q = n`. Suppose that for every
`b : B`, the cap product with `u` of the local class of `γ` at `0_b`, by the excisive couple
`(V ∖ 0, V ∖ V_b)`, pushed forward along the projection to `H_q(B, B ∖ b)` and read in the centred
chart at `b`, is the local orientation `o b` read in that chart. Then `π_*(u ⌢ γ)` is the
fundamental class of `o`. -/
theorem map_proj_singularCap_eq_fundamentalClass_of_centeredExtChartAt {q : ℕ}
    (o : HomologicalOrientation B E q) (hq : finrank ℝ E = q) {r n : ℕ} (h : r + q = n)
    (u : (thomPair P V).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) r)
    (γ : ((thomPair P V).singularHomology (ModuleCat.of ℤ (ULift.{0} ℤ)) n : ModuleCat.{0} ℤ))
    (hγ : ∀ b, localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (centeredExtChartAt I b).sourceRestrict
        (sourceRestrict_centeredExtChartAt_preimage_zero I b).subset q
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          (centeredExtChartAt I b).open_source.isOpenEmbedding_subtypeVal
          ⟨b, mem_centeredExtChartAt_source I b⟩ q).inv
          (TopPair.singularHomologyMap
            (TopPair.ofSubsetMap (TopCat.ofHom ⟨π P V, FiberBundle.continuous_proj P V⟩)
              (mapsTo_preimage _ ({b}ᶜ : Set (TopCat.of B)))) (ModuleCat.of ℤ (ULift.{0} ℤ)) q
            (TopCat.singularRelativeCap ℤ (ρ_ _).inv (ρ_ _).hom _
              (TopCat.ofHom ⟨π P V, FiberBundle.continuous_proj P V⟩ ⁻¹'
                ({b}ᶜ : Set (TopCat.of B)))
              ((isOpen_zeroSectionCompl P V).preimage continuous_subtypeVal)
              ((isOpen_compl_singleton.preimage (FiberBundle.continuous_proj P V)).preimage
                continuous_subtypeVal) r q n h u
              (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) fun _ hv ↦
                (zeroSectionCompl_union_compl_preimage_singleton b).superset hv)
                (ModuleCat.of ℤ (ULift.{0} ℤ)) n
                ((thomPairLocalHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) P V b n).hom
                  γ))))) =
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (centeredExtChartAt I b).sourceRestrict
        (sourceRestrict_centeredExtChartAt_preimage_zero I b).subset q
        ((localHomologyIsoOfIsOpenEmbedding (ModuleCat.of ℤ (ULift.{0} ℤ))
          (centeredExtChartAt I b).open_source.isOpenEmbedding_subtypeVal
          ⟨b, mem_centeredExtChartAt_source I b⟩ q).inv (o b).val)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom ⟨π P V, FiberBundle.continuous_proj P V⟩)
      (((thomPair P V).singularCap ℤ (ρ_ _).inv (ρ_ _).hom r q n h u).hom γ) =
      o.fundamentalClass hq :=
  o.map_singularCap_eq_fundamentalClass ℤ hq _ _ _ (isOpen_zeroSectionCompl P V) r n h u γ
    fun b ↦ (centeredExtChartAt I b).injective_localHomologyMap_sourceRestrict _
      (mem_centeredExtChartAt_source I b) (centeredExtChartAt_self I b) q (by
      rw [← thomPairLocalHomologyRestriction_comp_singularHomologyMap_ofSubsetMap _ _ _ b n
        fun _ hv ↦ (zeroSectionCompl_union_compl_preimage_singleton b).superset hv,
        ConcreteCategory.comp_apply]
      exact hγ b)

end TauCeti.HomologicalOrientation

end
