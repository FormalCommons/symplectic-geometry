/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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

As an application, a finite set `S` with a symmetric real function `d` can be coloured so
that distinct points of `S` with one colour are at `d`-distance at least `R`: colour the graph
on `S` joining distinct points at distance less than `R`. If at most `C * (1 + r) ^ m` points
of `S` lie within distance `r` of each point of `S`, then for `R ≥ 1` this takes at most
`(2 ^ m * C + 1) * R ^ m` colours. Donaldson [Donaldson1996] colours the centres of a cover
by balls in this way.

## Main results

* `SimpleGraph.colorable_of_forall_degree_le`: if every vertex of a locally finite graph
  has degree at most `Δ`, then the graph is `(Δ + 1)`-colourable.
* `Finset.exists_coloring_le_of_card_lt_le`: if each point of `S` has at most `K` other points
  of `S` at distance less than `R`, then `K + 1` colours suffice.
* `Finset.exists_coloring_le_of_card_le_mul_pow`: under the counting bound
  `#{x ∈ S | d x y ≤ r} ≤ C * (1 + r) ^ m`, at most `(2 ^ m * C + 1) * R ^ m` colours suffice.

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

namespace Finset

variable {α : Type*} {d : α → α → ℝ}

/-- Let `d` be a symmetric real function on `α`, and `S` a finite set in which each point has
at most `K` other points at `d`-distance less than `R`. Then there is a colouring of `α` with
`K + 1` colours in which any two distinct points of `S` with the same colour are at distance
at least `R`. -/
theorem exists_coloring_le_of_card_lt_le [DecidableEq α] (hd : ∀ x y, d x y = d y x)
    (S : Finset α) {R : ℝ} {K : ℕ} (hK : ∀ y ∈ S, #{x ∈ S | x ≠ y ∧ d x y < R} ≤ K) :
    ∃ c : α → Fin (K + 1), ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → c x = c x' → R ≤ d x x' := by
  classical
  let G : SimpleGraph S :=
    { Adj := fun x y ↦ x ≠ y ∧ d x y < R
      symm := ⟨fun x y h ↦ ⟨h.1.symm, hd x y ▸ h.2⟩⟩
      loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
  obtain ⟨col⟩ := G.colorable_of_forall_degree_le fun y ↦ by
    rw [← G.card_neighborFinset_eq_degree]
    refine le_trans ?_ (hK y y.property)
    rw [← card_map (Function.Embedding.subtype (· ∈ S))]
    refine card_le_card fun x hx ↦ ?_
    obtain ⟨x, hxy, rfl⟩ := mem_map.mp hx
    have hadj : x ≠ y ∧ d x y < R := ((G.mem_neighborFinset y x).mp hxy).symm
    exact mem_filter.mpr ⟨x.property, fun h ↦ hadj.1 (Subtype.ext h), hadj.2⟩
  refine ⟨fun a ↦ if h : a ∈ S then col ⟨a, h⟩ else 0, fun x hx x' hx' hne hc ↦ ?_⟩
  simp only [hx, hx', dite_true] at hc
  by_contra hlt
  exact col.valid (v := ⟨x, hx⟩) (w := ⟨x', hx'⟩)
    ⟨fun h ↦ hne (congrArg Subtype.val h), not_le.mp hlt⟩ hc

/-- Let `d` be a symmetric real function on `α`, and `S` a finite set with the counting bound
`#{x ∈ S | d x y ≤ r} ≤ C * (1 + r) ^ m` for all `y ∈ S` and `r ≥ 0`. Then for every `R ≥ 1`
there is a colouring of `α` with `N ≤ (2 ^ m * C + 1) * R ^ m` colours in which any two
distinct points of `S` with the same colour are at distance at least `R`. -/
theorem exists_coloring_le_of_card_le_mul_pow (hd : ∀ x y, d x y = d y x) (S : Finset α)
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hS : ∀ y ∈ S, ∀ r, 0 ≤ r → (#{x ∈ S | d x y ≤ r} : ℝ) ≤ C * (1 + r) ^ m)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ N : ℕ, (N : ℝ) ≤ (2 ^ m * C + 1) * R ^ m ∧
      ∃ c : α → Fin N, ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → c x = c x' → R ≤ d x x' := by
  classical
  have hpow : C * (1 + R) ^ m ≤ 2 ^ m * C * R ^ m := by
    rw [mul_comm (2 ^ m) C, mul_assoc, ← mul_pow]
    gcongr
    linarith
  refine ⟨⌊2 ^ m * C * R ^ m⌋₊ + 1, ?_,
    exists_coloring_le_of_card_lt_le hd S fun y hy ↦ Nat.le_floor ?_⟩
  · have h1 : (1 : ℝ) ≤ R ^ m := one_le_pow₀ hR
    have h2 := Nat.floor_le (by positivity : 0 ≤ 2 ^ m * C * R ^ m)
    push_cast
    nlinarith
  · refine le_trans ?_ ((hS y hy R (zero_le_one.trans hR)).trans hpow)
    exact_mod_cast card_le_card fun x hx ↦ by
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.2.le⟩

end Finset

end
