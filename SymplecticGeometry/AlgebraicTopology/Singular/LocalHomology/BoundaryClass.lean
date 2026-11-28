/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RelativeFundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Relative
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
import TauCeti.Data.Set.Image

/-!
# The boundary class of a compact manifold with collared boundary

We work in the setting of Tau Ceti's relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`): `X` is compact Hausdorff, `ι : M → X` is
an open embedding of an `(n + 1)`-manifold oriented by `o`, and the complement `∂X = X ∖ ι(M)` is
the image of a collared map. The connecting morphism of the pair `(X, ∂X)` carries the relative
fundamental class `[X, ∂X]` to the *boundary class* `∂[X, ∂X] ∈ Hₙ(∂X; ℤ)`.

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryClass`: the boundary class `∂[X, ∂X]`.

## Main results

* `TauCeti.HomologicalOrientation.boundaryClass_neg`: reversing the orientation negates the
  boundary class.
* `TauCeti.HomologicalOrientation.map_subtypeVal_boundaryClass`: the boundary class vanishes in
  `Hₙ(X; ℤ)`, by exactness of the sequence of the pair.
* `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassRel_comap`,
  `TauCeti.HomologicalOrientation.map_boundaryClass_comap`: a homeomorphism `h : X ≃ₜ X'` that
  restricts to a homeomorphism `φ : M ≃ₜ M'` carries the relative fundamental class and the
  boundary class for `o'.comap φ` to those for `o'`. The first follows from the uniqueness of the
  relative fundamental class (`TauCeti.HomologicalOrientation.eq_fundamentalClassRel`), the second
  from it by naturality of the connecting morphism. The proof of the first adapts that of Tau
  Ceti's `TauCeti.HomologicalOrientation.localHomologyMap_fundamentalClassOn_comap` from the
  fundamental class along a compact set to the relative fundamental class.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: the fundamental
  class of a compact manifold with boundary and its image in the homology of the boundary.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set Topology Module

namespace TauCeti.HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}

variable {n : ℕ} (o : HomologicalOrientation M E (n + 1)) (hn : finrank ℝ E = n + 1)
  (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary class** `∂[X, ∂X] ∈ Hₙ(∂X; ℤ)` of a compact `(n + 1)`-manifold `X` with
collared boundary `∂X`, the complement of `ι(M)`: the image of the relative fundamental class
`[X, ∂X]` under the connecting morphism of the pair `(X, ∂X)`. -/
def boundaryClass :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of ↥((range ι)ᶜ : Set X)) :=
  ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl).hom (o.fundamentalClassRel hn hι hιf hf)

theorem boundaryClass_def :
    o.boundaryClass hn hι hιf hf =
      ((TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl).hom (o.fundamentalClassRel hn hι hιf hf) :=
  (rfl)

/-- Reversing the orientation negates the boundary class. -/
@[simp]
theorem boundaryClass_neg : (-o).boundaryClass hn hι hιf hf = -o.boundaryClass hn hι hιf hf := by
  rw [boundaryClass_def, boundaryClass_def, fundamentalClassRel_neg]
  exact map_neg _ _

/-- The boundary class vanishes in `Hₙ(X; ℤ)`, by exactness of the sequence of the pair
`(X, ∂X)`. -/
@[simp]
theorem map_subtypeVal_boundaryClass :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
        TopCat.of ↥((range ι)ᶜ : Set X) ⟶ TopCat.of X)).hom
        (o.boundaryClass hn hι hιf hf) = 0 := by
  have h := (TopPair.ofSubset (X := TopCat.of X) (range ι)ᶜ).singularHomologyδ_comp
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (n + 1) n rfl
  -- `h` is the vanishing of the composite morphism; evaluate it at `[X, ∂X]`.
  exact ConcreteCategory.congr_hom h (o.fundamentalClassRel hn hι hιf hf)

section Homeomorph

variable {X' M' : Type} {N' : Type*} [TopologicalSpace X'] [TopologicalSpace N']
  [TopologicalSpace M'] [T2Space X'] [CompactSpace X'] [T2Space M'] [ChartedSpace E M']
  {ι' : M' → X'} {f' : N' → X'}

/-- **The relative fundamental class under a homeomorphism.** Let `h : X ≃ₜ X'` and
`φ : M ≃ₜ M'` be homeomorphisms with `h ∘ ι = ι' ∘ φ`, for two instances of the setting of the
relative fundamental class. Then `h` carries the relative fundamental class for the pull-back
`o'.comap φ` of an orientation `o'` of `M'` to the relative fundamental class for `o'`. -/
theorem localHomologyMap_fundamentalClassRel_comap {d : ℕ} (o' : HomologicalOrientation M' E d)
    (hd : finrank ℝ E = d) (hι : IsOpenEmbedding ι) (hιf : range ι = (range f)ᶜ)
    (hf : IsCollared f) (hι' : IsOpenEmbedding ι') (hιf' : range ι' = (range f')ᶜ)
    (hf' : IsCollared f') (h : X ≃ₜ X') (φ : M ≃ₜ M') (hφ : h ∘ ι = ι' ∘ φ) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (h : C(X, X'))
        (by rw [ContinuousMap.coe_ofClass, ← φ.surjective.range_comp, ← hφ,
          h.injective.preimage_range_comp]) d
        ((o'.comap φ.isOpenEmbedding).fundamentalClassRel hd hι hιf hf) =
      o'.fundamentalClassRel hd hι' hιf' hf' := by
  refine o'.eq_fundamentalClassRel hd hι' hιf' hf' fun x' ↦ ?_
  obtain ⟨x, rfl⟩ := φ.surjective x'
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have hx : (h : C(X, X')) ⁻¹' {ι' (φ x)} ⊆ {ι x} := fun y hy ↦
    h.injective (hy.trans (congrFun hφ x).symm)
  rw [← ConcreteCategory.comp_apply, localHomologyMap_comp_localHomologyRestriction,
    ← localHomologyRestriction_comp_localHomologyMap R _ (singleton_subset_iff.2 (mem_range_self x))
      hx, ConcreteCategory.comp_apply, localHomologyRestriction_fundamentalClassRel, comap_apply,
    IsOpenEmbedding.coe_localOrientationEquiv_symm, ← ConcreteCategory.comp_apply,
    localHomologyIsoOfIsOpenEmbedding_hom_comp_localHomologyMap R hι hι' φ.isOpenEmbedding _ hφ,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- **The boundary class under a homeomorphism.** Let `h : X ≃ₜ X'` and `φ : M ≃ₜ M'` be
homeomorphisms with `h ∘ ι = ι' ∘ φ`, for two instances of the setting of the boundary class, and
let `g : ∂X → ∂X'` be the restriction of `h`. Then `g` carries the boundary class for the pull-back
`o'.comap φ` of an orientation `o'` of `M'` to the boundary class for `o'`. -/
theorem map_boundaryClass_comap (o' : HomologicalOrientation M' E (n + 1))
    (hι' : IsOpenEmbedding ι') (hιf' : range ι' = (range f')ᶜ) (hf' : IsCollared f')
    (h : X ≃ₜ X') (φ : M ≃ₜ M') (hφ : h ∘ ι = ι' ∘ φ)
    (g : C(↥((range ι)ᶜ : Set X), ↥((range ι')ᶜ : Set X'))) (hg : ∀ z, (g z : X') = h z) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom g)).hom ((o'.comap φ.isOpenEmbedding).boundaryClass hn hι hιf hf) =
        o'.boundaryClass hn hι' hιf' hf' := by
  have hpre : (h : C(X, X')) ⁻¹' range ι' ⊆ range ι := by
    rw [ContinuousMap.coe_ofClass, ← φ.surjective.range_comp, ← hφ, h.injective.preimage_range_comp]
  set F := TopPair.ofSubsetMap (X := TopCat.of X) (Y := TopCat.of X') (B := (range ι)ᶜ)
    (B' := (range ι')ᶜ) (TopCat.ofHom (h : C(X, X')))
    ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 hpre))
  -- The restriction of `h` to the subspaces of the pairs is `g`.
  have hsnd : TopPair.Hom.snd F = TopCat.ofHom g := by
    ext z
    refine Subtype.ext ?_
    exact (TopPair.ofSubsetMap_snd_apply _ _ z).trans (hg z).symm
  have hnat := ConcreteCategory.congr_hom
    (TopPair.singularHomologyδ_naturality (ModuleCat.of ℤ (ULift.{0} ℤ)) F (n + 1) n rfl)
    ((o'.comap φ.isOpenEmbedding).fundamentalClassRel hn hι hιf hf)
  rw [hsnd] at hnat
  rw [boundaryClass_def, boundaryClass_def, ← localHomologyMap_fundamentalClassRel_comap o' hn hι
    hιf hf hι' hιf' hf' h φ hφ, localHomologyMap_def]
  -- `hnat` is the goal for composites, stated with `SSet.homologyMap` for the singular homology
  -- functor (`TauCeti.singularHomologyFunctor_obj_map`) and with the subspace of the pair
  -- `(X, ∂X)` for `∂X`: the two agree only after unfolding, hence `exact`.
  exact hnat

end Homeomorph

end TauCeti.HomologicalOrientation

end
