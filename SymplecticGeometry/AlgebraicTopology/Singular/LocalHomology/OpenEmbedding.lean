/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding

/-!
# Naturality of local homology along open embeddings

Tau Ceti's `TauCeti.localHomologyIsoOfIsOpenEmbedding` identifies the local homology of `M` at
`x` with that of `N` at `j x`, for an open embedding `j : M → N` into a `T₁` space. This file
shows that these isomorphisms are natural along a commuting square `h ∘ ι = ι' ∘ φ` in which
`ι`, `ι'` and `φ` are open embeddings and `h` is any continuous map.

## Main results

* `TauCeti.localHomologyIsoOfIsOpenEmbedding_hom_comp_localHomologyMap`: along such a square,
  the isomorphism for `ι` followed by the map induced by `h` is the isomorphism for `φ` followed
  by the isomorphism for `ι'`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  homology, computed by excision in a neighbourhood.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology

universe w v u

namespace TauCeti

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

end TauCeti

end
