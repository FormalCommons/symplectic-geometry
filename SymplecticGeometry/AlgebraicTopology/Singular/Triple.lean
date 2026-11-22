/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The singular chain sequence of a triple of nested subsets

Nested subsets `B ⊆ A ⊆ X` give Tau Ceti's triple `TauCeti.TopTriple.ofSubset`, whose outer pair
is the pair `(X, A)` of `TopPair.ofSubset A`, but only up to unfolding the outer pair functor.
This file restates the singular chain sequence `C(A, B) ⟶ C(X, B) ⟶ C(X, A)` of the triple and its
connecting morphism `Hₙ(X, A) ⟶ Hₘ(A, B)` with the outer pair written as `TopPair.ofSubset A`, as
`TopPair.singularChainComplexπOfSubset` does for the quotient map of a pair. Composites with maps
into the relative chains or the relative homology of `(X, A)` then reassociate by `rw`.

## Main definitions and results

* `TauCeti.TopTriple.singularChainComplexShortComplexOfSubset`: the chain sequence of the triple,
  with last term the relative chains of `TopPair.ofSubset A`, and its exactness
  `TauCeti.TopTriple.shortExact_singularChainComplexShortComplexOfSubset`.
* `TauCeti.TopTriple.singularHomologyδOfSubset`: the connecting morphism of the triple, with source
  the relative homology of `TopPair.ofSubset A`; it is the connecting morphism of the chain
  sequence (`TauCeti.TopTriple.singularHomologyδOfSubset_def`), and the connecting morphism of the
  pair `(X, A)` followed by the map to relative homology
  (`TauCeti.TopTriple.singularHomologyδOfSubset_eq_comp_singularHomologyπ`).

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I–III, the exact
  sequence of a triple.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {A B : Set X} (h : B ⊆ A)

/-- The singular chain sequence `C(A, B) ⟶ C(X, B) ⟶ C(X, A)` of the triple of nested subsets
`B ⊆ A ⊆ X`: `TauCeti.TopTriple.singularChainComplexShortComplex` of `TopTriple.ofSubset h`, with
its last term written as the relative chains of `TopPair.ofSubset A` rather than as those of the
outer pair of the triple. -/
noncomputable abbrev singularChainComplexShortComplexOfSubset : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (X₃ := (TopPair.ofSubset A).singularChainComplex R) _ _
    ((ofSubset h).singularChainComplexMap_innerToTotal_comp_totalToOuter R)

/-- The singular chain sequence of a triple of nested subsets is short exact. -/
lemma shortExact_singularChainComplexShortComplexOfSubset :
    (singularChainComplexShortComplexOfSubset R h).ShortExact :=
  (ofSubset h).shortExact_singularChainComplexShortComplex R

/-- The connecting morphism `Hₙ(X, A) ⟶ Hₘ(A, B)` of the triple of nested subsets `B ⊆ A ⊆ X`, for
`m + 1 = n`: `TauCeti.TopTriple.singularHomologyδ` of `TopTriple.ofSubset h`, with its source
written as the relative homology of `TopPair.ofSubset A`. -/
noncomputable abbrev singularHomologyδOfSubset (n m : ℕ) (hm : m + 1 = n := by lia) :
    (TopPair.ofSubset A).singularHomology R n ⟶
      (innerPair.obj (ofSubset h)).singularHomology R m :=
  (ofSubset h).singularHomologyδ R n m hm

lemma singularHomologyδOfSubset_eq (n m : ℕ) (hm : m + 1 = n) :
    singularHomologyδOfSubset R h n m hm = (ofSubset h).singularHomologyδ R n m hm :=
  (rfl)

/-- The connecting morphism of a triple of nested subsets is the connecting morphism of its
singular chain sequence. -/
lemma singularHomologyδOfSubset_def (n m : ℕ) (hm : m + 1 = n) :
    singularHomologyδOfSubset R h n m hm =
      (shortExact_singularChainComplexShortComplexOfSubset R h).δ n m (by simpa) :=
  -- `TauCeti.TopTriple.singularHomologyδ_def`, whose short complex is this one up to unfolding the
  -- outer pair of the triple
  (ofSubset h).singularHomologyδ_def R n m hm

/-- The connecting morphism of the triple of nested subsets `B ⊆ A ⊆ X` is the connecting morphism
`Hₙ(X, A) ⟶ Hₘ(A)` of the pair `(X, A)` followed by the map to `Hₘ(A, B)`. -/
lemma singularHomologyδOfSubset_eq_comp_singularHomologyπ (n m : ℕ) (hm : m + 1 = n) :
    singularHomologyδOfSubset R h n m hm =
      (TopPair.ofSubset A).singularHomologyδ R n m hm ≫
        (innerPair.obj (ofSubset h)).singularHomologyπ R m :=
  -- `TauCeti.TopTriple.singularHomologyδ_eq_comp_singularHomologyπ`, whose outer pair is
  -- `TopPair.ofSubset A` up to unfolding
  (ofSubset h).singularHomologyδ_eq_comp_singularHomologyπ R n m hm

end TopTriple

end TauCeti

end
