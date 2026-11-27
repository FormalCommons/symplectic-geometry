/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import SymplecticGeometry.Topology.OpenPartialHomeomorph.SourceRestrict

/-!
# Local homology along open embeddings

`TauCeti.localHomologyIsoOfIsOpenEmbeddingOfPreimage` is excision along an open embedding
`j : M → N` as an isomorphism `Hₖ(M, M ∖ S) ≅ Hₖ(N, N ∖ T)`, for a closed set `T` in the image
of `j` with `S = j ⁻¹' T`; Tau Ceti's `TauCeti.localHomologyIsoOfIsOpenEmbedding` is the case
of a point.

Tau Ceti's `TauCeti.localHomologyIsoOfIsOpenEmbedding` identifies the local homology of `M` at
`x` with that of `N` at `j x`, for an open embedding `j : M → N` into a `T₁` space. This file
shows that these isomorphisms are natural along a commuting square `h ∘ ι = ι' ∘ φ` in which
`ι`, `ι'` and `φ` are open embeddings and `h` is any continuous map.

For an open partial homeomorphism `c : M → Q` and a point `x` of its source, the local homology
of `M` at `x` can be read in `c`: in the source of `c` first, through the inverse of
`TauCeti.localHomologyIsoOfIsOpenEmbedding` for the inclusion of the source, and then along
`c.sourceRestrict`. With coefficients in a module, this reading is injective.

## Main definitions

* `TauCeti.localHomologyIsoOfIsOpenEmbeddingOfPreimage`: excision along an open embedding, as an
  isomorphism.

## Main results

* `TauCeti.localHomologyIsoOfIsOpenEmbedding_hom_comp_localHomologyMap`: along such a square,
  the isomorphism for `ι` followed by the map induced by `h` is the isomorphism for `φ` followed
  by the isomorphism for `ι'`.
* `TauCeti.localHomologyPointClass_comp_localHomologyIsoOfIsOpenEmbedding_hom`: the isomorphism
  at a point carries the class of the point to the class of its image.
* `Topology.IsOpenEmbedding.injective_localHomologyMap`: with coefficients in a module, the
  map of excision along an open embedding is injective.
* `OpenPartialHomeomorph.injective_localHomologyMap_sourceRestrict`: reading the local homology
  of `M` at `x` in an open partial homeomorphism, through its source, is injective.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  homology, computed by excision in a neighbourhood.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe w v u

namespace TauCeti

section Excision

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]

/-- **Excision along an open embedding, as an isomorphism.** If `j : M → N` is an open embedding,
`T` is a closed set of `N` in the image of `j` and `S = j ⁻¹' T`, then the map induced by `j`
is an isomorphism `Hₖ(M, M ∖ S) ≅ Hₖ(N, N ∖ T)`. -/
def localHomologyIsoOfIsOpenEmbeddingOfPreimage {j : M → N} (hj : IsOpenEmbedding j) {S : Set M}
    {T : Set N} (h : j ⁻¹' T = S) (hT : IsClosed T) (hTj : T ⊆ range j) (k : ℕ) :
    localHomology R S k ≅ localHomology R T k :=
  have := isIso_localHomologyMap R ⟨j, hj.continuous⟩ hj h hT hTj k
  asIso (localHomologyMap R ⟨j, hj.continuous⟩ h.subset k)

@[simp]
lemma localHomologyIsoOfIsOpenEmbeddingOfPreimage_hom {j : M → N} (hj : IsOpenEmbedding j)
    {S : Set M} {T : Set N} (h : j ⁻¹' T = S) (hT : IsClosed T) (hTj : T ⊆ range j) (k : ℕ) :
    (localHomologyIsoOfIsOpenEmbeddingOfPreimage R hj h hT hTj k).hom =
      localHomologyMap R ⟨j, hj.continuous⟩ h.subset k :=
  (rfl)

end Excision

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {X M X' M' : Type w} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace X']
  [TopologicalSpace M'] [T1Space X] [T1Space X'] [T1Space M']

/-- **Naturality of the local isomorphisms of open embeddings.** Let `ι : M → X`,
`ι' : M' → X'` and `φ : M → M'` be open embeddings and `h : X → X'` a continuous map with
`h ∘ ι = ι' ∘ φ`. Then the identification of `Hₖ(M, M ∖ {x})` with `Hₖ(X, X ∖ {ι x})` followed
by the map induced by `h` is the identification with `Hₖ(M', M' ∖ {φ x})` followed by the
identification with `Hₖ(X', X' ∖ {ι' (φ x)})`. -/
@[reassoc]
lemma localHomologyIsoOfIsOpenEmbedding_hom_comp_localHomologyMap {ι : M → X} {ι' : M' → X'}
    {φ : M → M'} (hι : IsOpenEmbedding ι) (hι' : IsOpenEmbedding ι') (hφ : IsOpenEmbedding φ)
    (h : C(X, X')) (hsq : h ∘ ι = ι' ∘ φ) (x : M) (hx : h ⁻¹' {ι' (φ x)} ⊆ {ι x}) (k : ℕ) :
    (localHomologyIsoOfIsOpenEmbedding R hι x k).hom ≫ localHomologyMap R h hx k =
      (localHomologyIsoOfIsOpenEmbedding R hφ x k).hom ≫
        (localHomologyIsoOfIsOpenEmbedding R hι' (φ x) k).hom := by
  simp only [localHomologyIsoOfIsOpenEmbedding_hom, localHomologyMap_comp]
  congr 1
  exact ContinuousMap.ext fun y ↦ congrFun hsq y

/-- The identification `TauCeti.localHomologyIsoOfIsOpenEmbedding` of the local homology of `M`
at `x` with that of `X` at `ι x` carries the class of the point `x` to the class of `ι x`. -/
@[reassoc, elementwise]
lemma localHomologyPointClass_comp_localHomologyIsoOfIsOpenEmbedding_hom {ι : M → X}
    (hι : IsOpenEmbedding ι) (x : M) :
    localHomologyPointClass R {x} x ≫ (localHomologyIsoOfIsOpenEmbedding R hι x 0).hom =
      localHomologyPointClass R {ι x} (ι x) := by
  rw [localHomologyIsoOfIsOpenEmbedding_hom]
  exact localHomologyPointClass_map _ _ _ _

end TauCeti

namespace Topology.IsOpenEmbedding

open TauCeti

variable {S : Type*} [Ring S] (R : ModuleCat.{w} S) {M Q : Type w} [TopologicalSpace M]
  [TopologicalSpace Q]

/-- **Excision along an open embedding, injectivity.** If `j : M → Q` is an open embedding, `T`
is a closed set of `Q` in the image of `j` and `A = j ⁻¹' T`, then the map
`Hₖ(M, M ∖ A) → Hₖ(Q, Q ∖ T)` induced by `j`, with coefficients in a module `R`, is
injective. -/
theorem injective_localHomologyMap {j : C(M, Q)} (hj : IsOpenEmbedding j) {A : Set M}
    {T : Set Q} (h : j ⁻¹' T = A) (hT : IsClosed T) (hTj : T ⊆ range j) (k : ℕ) :
    Function.Injective (localHomologyMap R j h.subset k) :=
  have := isIso_localHomologyMap R j hj h hT hTj k
  (ModuleCat.mono_iff_injective _).1 inferInstance

end Topology.IsOpenEmbedding

namespace OpenPartialHomeomorph

open TauCeti

variable {S : Type*} [Ring S] (R : ModuleCat.{w} S) {M Q : Type w} [TopologicalSpace M]
  [TopologicalSpace Q] [T1Space M] [T1Space Q]

/-- Let `c : M → Q` be an open partial homeomorphism between `T₁` spaces and `x` a point of its
source, with `c x = y`. Reading the local homology of `M` at `x`, with coefficients in a module
`R`, first in the source of `c` and then in `Q` along `c.sourceRestrict`, is injective. -/
theorem injective_localHomologyMap_sourceRestrict (c : OpenPartialHomeomorph M Q) {x : M}
    (hx : x ∈ c.source) {y : Q} (hy : c x = y) (k : ℕ) :
    Function.Injective fun a ↦ localHomologyMap R c.sourceRestrict
      (hy ▸ (c.sourceRestrict_preimage_singleton hx).subset) k
      ((localHomologyIsoOfIsOpenEmbedding R c.open_source.isOpenEmbedding_subtypeVal
        ⟨x, hx⟩ k).inv a) := by
  subst hy
  exact (c.isOpenEmbedding_sourceRestrict.injective_localHomologyMap R
    (c.sourceRestrict_preimage_singleton hx) isClosed_singleton
    (Set.singleton_subset_iff.2 ⟨_, c.sourceRestrict_apply ⟨x, hx⟩⟩) k).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

end OpenPartialHomeomorph

end
