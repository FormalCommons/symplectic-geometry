/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import TauCeti.AlgebraicTopology.Singular.Relative
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Relative singular chains: open subspaces and changes of the subset

This file adds to Tau Ceti's relative singular chains of a topological pair:

* `TopCat.mono_chainComplexMap_inclusion'_f`: the inclusion of an open set `U ⊆ X` induces a
  monomorphism of singular chains in each degree;
* `TopPair.ιChainComplex_comp_singularChainComplexπ_eq_zero`: a singular simplex of the ambient
  space with image in the subspace vanishes in relative chains;
* `TopPair.openSubspacePair U A`: for an open set `U` and a set `A` of `X`, the pair of `U` and the
  preimage of `A` in `U`, with `TopPair.openSubspacePair_compl` for a complement, and its map
  `TopPair.openSubspaceInclusion` into the pair `(X, A)`;
* `TopPair.restrictSubsetMap`: for `A ⊆ B` and a subcomplex `S` of the singular simplicial set of
  `X`, the map from the singular pair of `(X, A)` restricted to `S` to that of `(X, B)`, with its
  compatibility with the quotient maps (`TopPair.chainComplexπ_restrictSubsetMap`), with the
  inclusions of the restricted chains
  (`TopPair.chainComplexMap_restrictSubsetMap_comp_restrictι`), and with composition
  (`TopPair.chainComplexMap_restrictSubsetMap_comp`);
* `TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id`: a map of pairs
  `(X, A) ⟶ (X, B)` that is the identity of `X` carries the quotient map of `(X, A)` to that of
  `(X, B)`.

These declarations are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Singular/Relative.lean`, same names), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, and, for
`TopPair.singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id`, as of the commit
`c9d170eed5`, not yet in the pinned release; they are stated here
under their Tau Ceti names, so that moving Tau Ceti past them deletes this file without renames.

Tau Ceti's file closes its module docstring with the following note on the source of its
relative-chain construction, which the declarations above extend; it is kept here unchanged:

The construction follows the quotient-chain presentation in Eilenberg--Steenrod, *Foundations of
Algebraic Topology*, Chapters I--III, and is implemented using Mathlib's `SSetPair` relative-chain
functor.

Tau Ceti's file has no References section; this module docstring adds the one below.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, relative
  homology groups.
-/

public section

noncomputable section

open Simplicial CategoryTheory Limits TopologicalSpace

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (P : TopPair.{w}) (R : C)

/-- Open inclusions induce monomorphisms of singular chains in each degree. -/
instance _root_.TopCat.mono_chainComplexMap_inclusion'_f {X : TopCat.{w}} (U : Opens X)
    (R : C) (q : ℕ) :
    Mono ((SSet.chainComplexMap (TopCat.toSSet.map (Opens.inclusion' U)) R).f q) :=
  inferInstanceAs (Mono ((SSet.chainComplexMap
    (TopPair.toSSetPair.obj (TopPair.ofSubset (U : Set X))).hom R).f q))

/-- A simplex lying in the subspace of a pair vanishes in relative singular chains. -/
lemma ιChainComplex_comp_singularChainComplexπ_eq_zero {n : ℕ}
    (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌)
    (hσ : Set.range (P.fst.toSSetObjEquiv _ σ) ⊆ Set.range P.map) :
    (TopCat.toSSet.obj P.fst).ιChainComplex σ ≫ (P.singularChainComplexπ R).f n = 0 := by
  obtain ⟨τ, hτ⟩ := (P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ σ).2 hσ
  -- The relative quotient source is the ambient singular chains after toSSetPair unfolds.
  erw [← hτ, ← SSet.ι_chainComplexMap_f, Category.assoc, ← HomologicalComplex.comp_f,
    chainComplexMap_comp_singularChainComplexπ, HomologicalComplex.zero_f, comp_zero]

/-- A map of pairs `(X, A) ⟶ (X, B)` given by the identity of `X` carries the quotient map to the
relative singular chains of `(X, A)` to the quotient map to those of `(X, B)`. -/
@[reassoc]
lemma singularChainComplexπ_comp_singularChainComplexMap_of_fst_eq_id {X A B : TopCat.{w}}
    {i : A ⟶ X} {j : B ⟶ X} {hi : Topology.IsEmbedding i} {hj : Topology.IsEmbedding j}
    (f : TopPair.of i hi ⟶ TopPair.of j hj) (hf : Hom.fst f = 𝟙 X) :
    (TopPair.of i hi).singularChainComplexπ R ≫ singularChainComplexMap f R =
      (TopPair.of j hj).singularChainComplexπ R := by
  rw [← singularChainComplexπ_pair_naturality, hf]
  exact (congrArg (· ≫ _) ((TopCat.toSSet ⋙ (SSet.chainComplexFunctor C).obj R).map_id X)).trans
    (Category.id_comp _)

section OpenSubspace

open TopologicalSpace

variable {R}

variable {X : TopCat.{w}} (U : Opens X) (A : Set X)

/-- The original subspace paired with the inverse image of the relative subset. -/
abbrev openSubspacePair : TopPair.{w} :=
  TopPair.ofSubset (Opens.inclusion' U ⁻¹' (A : Set X))

/-- The open-subspace pair of a complement is the complement pair of the inverse image. -/
lemma openSubspacePair_compl :
    openSubspacePair U Aᶜ = ofSubset (Opens.inclusion' U ⁻¹' A)ᶜ := rfl

/-- The map of original relative pairs induced by the open inclusion. -/
def openSubspaceInclusion :
    openSubspacePair U A ⟶ TopPair.ofSubset (A : Set X) :=
  TopPair.ofSubsetMap (Opens.inclusion' U) (fun _ hx ↦ hx)

/-- The ambient component of the native pair map is the open inclusion. -/
@[simp]
lemma openSubspaceInclusion_fst :
    TopPair.Hom.fst (openSubspaceInclusion U A) = Opens.inclusion' U := by
  erw [openSubspaceInclusion, TopPair.ofSubsetMap_fst]

variable (S : (TopCat.toSSet.obj X).Subcomplex)

/-- Enlarging the relative subset induces a map of the native restricted pairs. -/
def restrictSubsetMap
    {A B : Set X} (hAB : A ⊆ B) :
    (TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrict S ⟶
      (TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrict S :=
  SSetPair.restrictMap (TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB)) (by
    erw [TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id,
      SSet.Subcomplex.preimage_id]
    exact le_refl S)

/-- The ambient map of a support restriction is the identity. -/
@[simp]
lemma restrictSubsetMap_right
    {A B : Set X} (hAB : A ⊆ B) : (restrictSubsetMap S hAB).right = 𝟙 S.toSSet := by
  ext i σ
  apply Subtype.ext
  erw [restrictSubsetMap, SSetPair.restrictMap_right_app_coe]
  erw [TopPair.toSSetPair_map_right, TopPair.ofSubsetMap_fst, CategoryTheory.Functor.map_id]
  -- The identity natural transformation evaluates to the original simplex.
  rfl

/-- Relative quotient maps commute with support restriction. -/
@[reassoc]
lemma chainComplexπ_restrictSubsetMap
    {A B : Set X} (hAB : A ⊆ B) :
    ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrict S).chainComplexπ R ≫
      SSetPair.chainComplexMap (restrictSubsetMap S hAB) R =
      ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrict S).chainComplexπ R := by
  erw [← SSetPair.chainComplexπ_naturality, restrictSubsetMap_right]
  erw [SSet.chainComplexMap_id, Category.id_comp]

/-- Support change commutes with the original relative-chain inclusion. -/
lemma chainComplexMap_restrictSubsetMap_comp_restrictι
    {A B : Set X} (hAB : A ⊆ B) :
    SSetPair.chainComplexMap (restrictSubsetMap S hAB) R ≫
      SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrictι S) R =
    SSetPair.chainComplexMap ((TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrictι S) R ≫
      TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) hAB) R := by
  have hc : restrictSubsetMap S hAB ≫ (TopPair.toSSetPair.obj (TopPair.ofSubset B)).restrictι S =
      (TopPair.toSSetPair.obj (TopPair.ofSubset A)).restrictι S ≫
        TopPair.toSSetPair.map (TopPair.ofSubsetMap (𝟙 X) hAB) :=
    SSetPair.restrictMap_comp_restrictι _ _
  have h := congrArg (fun f ↦ SSetPair.chainComplexMap f R) hc
  simpa only [CategoryTheory.Functor.map_comp] using h

/-- Successive support restrictions compose. -/
@[reassoc (attr := simp)]
lemma chainComplexMap_restrictSubsetMap_comp
    {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C) :
    SSetPair.chainComplexMap (restrictSubsetMap S hAB) R ≫
      SSetPair.chainComplexMap (restrictSubsetMap S hBC) R =
      SSetPair.chainComplexMap (restrictSubsetMap S (hAB.trans hBC)) R := by
  apply (cancel_epi (((toSSetPair.obj (ofSubset A)).restrict S).chainComplexπ R)).1
  erw [chainComplexπ_restrictSubsetMap_assoc, chainComplexπ_restrictSubsetMap,
    chainComplexπ_restrictSubsetMap]

end OpenSubspace

end TopPair

end
