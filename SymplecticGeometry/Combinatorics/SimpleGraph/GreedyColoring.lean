/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Greedy colourings of graphs of bounded degree

A finite graph in which every vertex has degree at most `Δ` can be coloured with `Δ + 1`
colours. The vertices are coloured one at a time, and each vertex gets a colour that none
of its already coloured neighbours has. There is always such a colour, since a vertex has
at most `Δ` neighbours.

## Main results

* `SimpleGraph.colorable_of_forall_degree_le`: if every vertex of a graph on a finite type
  has degree at most `Δ`, then the graph is `(Δ + 1)`-colourable.
* `SimpleGraph.colorable_of_maxDegree_le`: the same, with the bound on the maximal degree.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {Δ : ℕ}

/-- The greedy step: a colouring of the vertices that is proper on a finite set `s` extends
to one that is proper on `insert a s`. -/
private theorem exists_proper_insert [DecidableEq V] [G.LocallyFinite]
    (hdeg : ∀ v, G.degree v ≤ Δ)
    {s : Finset V} {a : V} (f : V → Fin (Δ + 1))
    (hf : ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → f u ≠ f v) :
    ∃ g : V → Fin (Δ + 1), ∀ u ∈ insert a s, ∀ v ∈ insert a s, G.Adj u v → g u ≠ g v := by
  -- The colours of the neighbours of `a` in `s` do not exhaust `Fin (Δ + 1)`.
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
      (s := ((G.neighborFinset a).filter (· ∈ s)).image f) <|
    Finset.card_image_le.trans_lt <| (Finset.card_filter_le _ _).trans_lt <| by
      simpa [card_neighborFinset_eq_degree] using Nat.lt_succ_of_le (hdeg a)
  refine ⟨Function.update f a c, ?_⟩
  have key : ∀ u ∈ s, G.Adj a u → c ≠ f u := fun u hu hau h ↦
    hc (Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨(G.mem_neighborFinset a u).2 hau, hu⟩,
      h.symm⟩)
  intro u hu v hv huv
  have hne : u ≠ v := G.ne_of_adj huv
  by_cases hua : u = a
  · subst hua
    rw [Function.update_self, Function.update_of_ne (Ne.symm hne)]
    exact key v (Finset.mem_of_mem_insert_of_ne hv (Ne.symm hne)) huv
  have hu' := Finset.mem_of_mem_insert_of_ne hu hua
  by_cases hva : v = a
  · subst hva
    rw [Function.update_self, Function.update_of_ne hne]
    exact (key u hu' huv.symm).symm
  rw [Function.update_of_ne hua, Function.update_of_ne hva]
  exact hf u hu' v (Finset.mem_of_mem_insert_of_ne hv hva) huv

/-- A graph on a finite type in which every vertex has degree at most `Δ` is
`(Δ + 1)`-colourable. -/
theorem colorable_of_forall_degree_le [Finite V] [G.LocallyFinite] (hdeg : ∀ v, G.degree v ≤ Δ) :
    G.Colorable (Δ + 1) := by
  classical
  have := Fintype.ofFinite V
  have h : ∀ s : Finset V, ∃ f : V → Fin (Δ + 1), ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → f u ≠ f v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ 0, by simp⟩
    | insert a s _ ih =>
      obtain ⟨f, hf⟩ := ih
      exact G.exists_proper_insert hdeg f hf
  obtain ⟨f, hf⟩ := h Finset.univ
  exact ⟨Coloring.mk f fun {u v} huv ↦ hf u (Finset.mem_univ u) v (Finset.mem_univ v) huv⟩

/-- A graph on a finite type of maximal degree at most `Δ` is `(Δ + 1)`-colourable. -/
theorem colorable_of_maxDegree_le [Fintype V] [DecidableRel G.Adj] (h : G.maxDegree ≤ Δ) :
    G.Colorable (Δ + 1) :=
  G.colorable_of_forall_degree_le fun v ↦ (G.degree_le_maxDegree v).trans h

end SimpleGraph

end
