/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Category.TopPair

/-!
# Maps of topological pairs

Supplements to Tau Ceti's `TauCeti/Topology/Category/TopPair.lean`: homotopies of maps of
pairs, and where isomorphisms of pairs of the form `(X, A)` send points.

## Main results

* `TopPair.homotopic_of_homotopy_fst`: two maps of pairs `P ⟶ (X, A)` are homotopic once their
  maps of ambient spaces are homotopic through maps sending the subspace of `P` into `A`. It
  combines `TopPair.isoOfSubsetRange_hom_comp_ofSubsetMap` with `TopPair.ofSubsetHomotopy`, so
  that the source may be any pair and not only one of the form `(X, A)`.
* `TopPair.iso_ofSubset_hom_fst_mapsTo_compl`: an isomorphism of pairs `(X, A) ≅ (Y, B)` maps
  `X ∖ A` into `Y ∖ B`.
* `TopPair.iso_ofSubset_compl_singleton_hom_fst_apply`: in particular, an isomorphism of pairs
  `(M, M ∖ {x}) ≅ (N, N ∖ {y})` sends `x` to `y`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §2.1 (homotopies of maps
  of pairs).
-/

public section

open CategoryTheory

universe w

namespace TopPair

variable {P : TopPair.{w}} {X : TopCat.{w}} {A : Set X}

/-- Two maps of pairs `φ ψ : P ⟶ (X, A)` are homotopic as maps of pairs as soon as their maps of
ambient spaces are homotopic through maps which send the subspace of `P` into `A`. -/
theorem homotopic_of_homotopy_fst {φ ψ : P ⟶ ofSubset A}
    (F : (Hom.fst φ).hom.Homotopy (Hom.fst ψ).hom)
    (hF : ∀ (t : unitInterval) (x : P.fst), x ∈ Set.range P.map → F (t, x) ∈ A) :
    Homotopic φ ψ := by
  rw [← isoOfSubsetRange_hom_comp_ofSubsetMap φ, ← isoOfSubsetRange_hom_comp_ofSubsetMap ψ]
  exact ⟨(ofSubsetHomotopy F hF).comp (Homotopy.refl _)⟩

/-- An isomorphism of pairs `e : (X, A) ≅ (Y, B)` maps the complement of `A` into the
complement of `B`, since its inverse maps `B` into `A`. -/
theorem iso_ofSubset_hom_fst_mapsTo_compl {X Y : TopCat.{w}} {A : Set X} {B : Set Y}
    (e : ofSubset A ≅ ofSubset B) : Set.MapsTo (Hom.fst e.hom) Aᶜ Bᶜ := by
  intro x hx hy
  have hmaps := mapsTo_range_map_of_hom (P := ofSubset B) e.inv
  rw [range_ofSubset_map] at hmaps
  have hinv : Hom.fst e.inv (Hom.fst e.hom x) = x :=
    ConcreteCategory.congr_hom (congrArg (fun f => Hom.fst f) e.hom_inv_id) x
  exact hx (hinv ▸ hmaps hy)

/-- An isomorphism of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` sends `x` to `y`. -/
theorem iso_ofSubset_compl_singleton_hom_fst_apply {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] {x : M} {y : N}
    (e : ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅ ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    Hom.fst e.hom x = y := by
  by_contra h
  exact iso_ofSubset_hom_fst_mapsTo_compl e (fun h => h rfl) h

end TopPair

end
