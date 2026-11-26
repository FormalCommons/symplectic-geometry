/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Category.TopPair

/-!
# Homotopies of maps of topological pairs

Supplements to Tau Ceti's `TauCeti/Topology/Category/TopPair.lean`.

## Main results

* `TopPair.homotopic_of_homotopy_fst`: two maps of pairs `P ⟶ (X, A)` are homotopic once their
  maps of ambient spaces are homotopic through maps sending the subspace of `P` into `A`. It
  combines `TopPair.isoOfSubsetRange_hom_comp_ofSubsetMap` with `TopPair.ofSubsetHomotopy`, so
  that the source may be any pair and not only one of the form `(X, A)`.

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

end TopPair

end
