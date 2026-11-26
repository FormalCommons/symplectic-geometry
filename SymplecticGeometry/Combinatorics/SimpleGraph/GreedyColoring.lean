/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
import TauCeti.Combinatorics.SimpleGraph.Coloring.Degeneracy

/-!
# Greedy colourings of graphs of bounded degree

A locally finite graph in which every vertex has degree at most `Δ` can be coloured with
`Δ + 1` colours, whether or not it has finitely many vertices.

Tau Ceti proves the bound for finite graphs, with the maximal degree, as
`SimpleGraph.colorable_maxDegree_add_one`, and more generally for graphs of degeneracy at
most `k`, as `SimpleGraph.colorable_succ_of_forall_exists_card_le`. The result here drops the
finiteness of the vertex type. Its proof follows that of Tau Ceti's
`SimpleGraph.colorable_maxDegree_add_one`.

## Main results

* `SimpleGraph.colorable_of_forall_degree_le`: if every vertex of a locally finite graph
  has degree at most `Δ`, then the graph is `(Δ + 1)`-colourable.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {Δ : ℕ}

/-- A locally finite graph in which every vertex has degree at most `Δ` is
`(Δ + 1)`-colourable. The vertex type may be infinite. -/
theorem colorable_of_forall_degree_le [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ Δ) :
    G.Colorable (Δ + 1) := by
  classical
  refine colorable_succ_of_forall_exists_card_le fun s ⟨v, hv⟩ ↦ ⟨v, hv, ?_⟩
  calc
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card fun w hw ↦
      (G.mem_neighborFinset v w).mpr (Finset.mem_filter.mp hw).2
    _ = G.degree v := G.card_neighborFinset_eq_degree v
    _ ≤ Δ := hdeg v

end SimpleGraph

end
