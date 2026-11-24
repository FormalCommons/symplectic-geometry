/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Connected
public import SymplecticGeometry.Topology.Order.OrdConnected

/-!
# Semialgebraic sets and functions of one variable

Facts about semialgebraic data on the line. The first two concern the points to the right of a
point `a : ℝ`; curve selection and the growth of one-variable semialgebraic functions both use
them. The third is the finiteness of frontiers. Points of the line are written
`![t] : Fin 1 → ℝ`, the coordinate space of Tau Ceti's semialgebraic geometry.

* `TauCeti.IsSemialgebraic.eventually_nhdsGT_mem_or_notMem`: a semialgebraic subset of the line
  contains, or misses, every point `![t]` with `t > a` close enough to `a`;
  `TauCeti.IsSemialgebraic.exists_pos_forall_Ioo_mem_or_notMem` is its form with an interval
  `(0, ε)`.
* `TauCeti.IsSemialgebraicOn.eventually_continuousAt_nhdsGT`: a function of one variable that is
  semialgebraic on a set containing the points `![t]`, `t > a` close to `a`, is continuous at
  these points; `TauCeti.IsSemialgebraicOn.exists_pos_forall_Ioo_continuousAt` is its form with
  an interval `(0, δ)`.
* `TauCeti.IsSemialgebraic.finite_frontier_of_unique`: a semialgebraic subset of the line
  `σ → ℝ`, `σ` having one element, has finite frontier;
  `TauCeti.finite_frontier_of_isSemialgebraic_preimage_funUnique` is its form for a subset of
  `ℝ`.

All three come from a cylindrical algebraic decomposition. A cell of a decomposition of
`ℝ ^ 1` is open or a single point (`TauCeti.IsCAD.isOpen_or_subsingleton`), so the points just
right of `a` lie in one open cell (`TauCeti.IsCAD.exists_isOpen_eventually_mem_nhdsGT`). For a
function, take a decomposition of the plane adapted to the graph of a coordinate: the cell
containing a point of the graph just right of `a` lies in the graph and lies over that open
cell, and it contains the graph of a continuous function on its projection, which is then the
coordinate.

For the frontier, a semialgebraic subset of the line is the union of finitely many connected
semialgebraic sets (`TauCeti.IsSemialgebraic.exists_finite_isConnected_partition`), its frontier
lies in the union of their frontiers, and each of these is order-connected, so its frontier has
at most two points (`Set.OrdConnected.encard_frontier_le_two`).

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Sections 2.3–2.5.
* L. van den Dries, *Tame Topology and o-minimal Structures*, Cambridge University Press, 1998,
  Chapter 3.
-/

public section

open Filter Set Topology MvPolynomial

namespace TauCeti

/-- Every cell of a cylindrical algebraic decomposition of `ℝ ^ 1` is open or a single point: a
coordinate projection maps it homeomorphically onto an open subset of `ℝ ^ 0` or `ℝ ^ 1`. -/
theorem IsCAD.isOpen_or_subsingleton {𝒞 : Set (Set (Fin 1 → ℝ))} (h : IsCAD 1 𝒞)
    {E : Set (Fin 1 → ℝ)} (hE : E ∈ 𝒞) : IsOpen E ∨ E.Subsingleton := by
  obtain ⟨d, ι, hι, he⟩ := h.exists_injective_isOpenEmbedding_comp hE
  have hd : d ≤ 1 := by simpa using Fintype.card_le_of_injective ι hι
  interval_cases d
  · exact .inr fun x hx y hy ↦
      congrArg Subtype.val (he.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subsingleton.elim _ _))
  · obtain rfl : ι = id := Subsingleton.elim _ _
    refine .inl ?_
    simpa using he.isOpen_range

/-- In a cylindrical algebraic decomposition of `ℝ ^ 1`, one open cell contains every point `![t]`
with `t > a` close enough to `a`. -/
theorem IsCAD.exists_isOpen_eventually_mem_nhdsGT {𝒞 : Set (Set (Fin 1 → ℝ))} (h : IsCAD 1 𝒞)
    (a : ℝ) : ∃ E ∈ 𝒞, IsOpen E ∧ ∀ᶠ t in 𝓝[>] a, ![t] ∈ E := by
  -- The points `t` with `![t]` in a one-point cell form a finite set.
  set T := (fun t : ℝ ↦ ![t]) ⁻¹' ⋃₀ {E ∈ 𝒞 | E.Subsingleton}
  have hT : T.Finite := by
    refine Finite.preimage (fun s _ t _ hst ↦ by simpa using hst) ?_
    exact (h.finite.subset fun _ (hE : _ ∈ {E ∈ 𝒞 | E.Subsingleton}) ↦ hE.1).sUnion
      fun _ (hE : _ ∈ {E ∈ 𝒞 | E.Subsingleton}) ↦ hE.2.finite
  have hTa : (T \ {a})ᶜ ∈ 𝓝 a :=
    (hT.sdiff.isClosed.isOpen_compl).mem_nhds fun ha ↦ ha.2 rfl
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (nhdsWithin_le_nhds hTa)
  have hcell (t : ℝ) (ht : t ∈ Ioo a b) : ∀ E ∈ 𝒞, ![t] ∈ E → IsOpen E := fun E hE htE ↦
    (h.isOpen_or_subsingleton hE).resolve_right fun hs ↦ hb ht ⟨⟨E, ⟨hE, hs⟩, htE⟩, ht.1.ne'⟩
  -- The cell of the midpoint contains the whole connected set `![t]`, `a < t < b`.
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := by
    have := mem_Ioi.1 hab
    constructor <;> simp only [m] <;> linarith
  obtain ⟨E, ⟨hE, hmE⟩, -⟩ := h.isPartition.2 ![m]
  have hEo := hcell m hm E hE hmE
  set U := ⋃₀ {F ∈ 𝒞 | F ≠ E ∧ IsOpen F}
  have hU : IsOpen U := isOpen_sUnion fun _ hF ↦ hF.2.2
  have hEU : Disjoint E U := disjoint_sUnion_right.2 fun F hF ↦
    h.isPartition.pairwiseDisjoint hE hF.1 hF.2.1.symm
  have hconn : IsPreconnected ((fun t : ℝ ↦ ![t]) '' Ioo a b) :=
    isPreconnected_Ioo.image _ (by fun_prop)
  have hsub : (fun t : ℝ ↦ ![t]) '' Ioo a b ⊆ E := by
    refine hconn.subset_left_of_subset_union hEo hU hEU ?_ ⟨![m], ⟨m, hm, rfl⟩, hmE⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨F, ⟨hF, htF⟩, -⟩ := h.isPartition.2 ![t]
    rcases eq_or_ne F E with rfl | hFE
    exacts [.inl htF, .inr ⟨F, ⟨hF, hFE, hcell t ht F hF htF⟩, htF⟩]
  exact ⟨E, hE, hEo, eventually_of_mem (Ioo_mem_nhdsGT hab) fun t ht ↦ hsub ⟨t, ht, rfl⟩⟩

/-- A semialgebraic subset of the line contains every point `![t]` with `t > a` close enough to
`a`, or contains none of them. -/
theorem IsSemialgebraic.eventually_nhdsGT_mem_or_notMem {s : Set (Fin 1 → ℝ)}
    (hs : IsSemialgebraic s) (a : ℝ) :
    (∀ᶠ t in 𝓝[>] a, ![t] ∈ s) ∨ ∀ᶠ t in 𝓝[>] a, ![t] ∉ s := by
  obtain ⟨𝒞, h𝒞, hsub⟩ := hs.exists_isCAD_subset_or_disjoint
  obtain ⟨E, hE, -, hev⟩ := h𝒞.exists_isOpen_eventually_mem_nhdsGT a
  rcases hsub E hE with hEs | hEs
  · exact .inl (hev.mono fun t ht ↦ hEs ht)
  · exact .inr (hev.mono fun t ht ↦ hEs.notMem_of_mem_left ht)

/-- A semialgebraic subset of the line contains the points `![t]` for all `t` in some interval
`(0, ε)`, or misses them all. -/
theorem IsSemialgebraic.exists_pos_forall_Ioo_mem_or_notMem {s : Set (Fin 1 → ℝ)}
    (hs : IsSemialgebraic s) :
    ∃ ε > 0, (∀ t ∈ Ioo 0 ε, ![t] ∈ s) ∨ ∀ t ∈ Ioo 0 ε, ![t] ∉ s := by
  rcases hs.eventually_nhdsGT_mem_or_notMem 0 with h | h
  · obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
    exact ⟨ε, hε, .inl hsub⟩
  · obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
    exact ⟨ε, hε, .inr hsub⟩

/-- A real function of one variable that is semialgebraic on a set containing the points `![t]`,
`t > a` close to `a`, is continuous at these points. -/
private theorem eventually_continuousAt_nhdsGT_scalar {g : (Fin 1 → ℝ) → ℝ}
    {s : Set (Fin 1 → ℝ)} (hg : IsSemialgebraicOn (fun x (_ : Unit) ↦ g x) s) {a : ℝ}
    (hs : ∀ᶠ t in 𝓝[>] a, ![t] ∈ s) : ∀ᶠ t in 𝓝[>] a, ContinuousAt g ![t] := by
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hs
  -- Restrict `g` to the semialgebraic set `A` of the points `![t]`, `a < t < b`.
  set A : Set (Fin 1 → ℝ) := {x | a < x 0} ∩ {x | x 0 < b}
  have hA : IsSemialgebraic A := by
    simpa using (isSemialgebraic_eval_lt (C a) (X 0)).inter (isSemialgebraic_eval_lt (X 0) (C b))
  have hAs : A ⊆ s := fun x hx ↦ by
    have : x = ![x 0] := by ext i; fin_cases i; simp
    exact this ▸ hb hx
  have hgA := hg.mono hA hAs
  -- The graph of `g` over `A`, in the plane, with the value as coordinate `0`.
  let e : Fin 1 ⊕ Unit → Fin 2 := Sum.elim (fun _ ↦ 1) fun _ ↦ 0
  set G := (fun y : Fin 2 → ℝ ↦ y ∘ e) ⁻¹'
    (Equiv.sumArrowEquivProdArrow (Fin 1) Unit ℝ ⁻¹' A.graphOn fun x _ ↦ g x)
  have hG : IsSemialgebraic G := hgA.graph.preimage_comp e
  have hmemG (c : ℝ) (x : Fin 1 → ℝ) : Fin.cons c x ∈ G ↔ x ∈ A ∧ g x = c := by
    have hx : (Fin.cons c x : Fin 2 → ℝ) ∘ e ∘ Sum.inl = x := by
      ext i; fin_cases i; simp [e]
    rw [mem_preimage (f := fun y : Fin 2 → ℝ ↦ y ∘ e),
      mem_preimage_sumArrowEquivProdArrow_scalar_graphOn, Function.comp_assoc, hx]
    simp [e]
  obtain ⟨𝒞, h𝒞, hsub⟩ := hG.exists_isCAD_subset_or_disjoint
  obtain ⟨_, ⟨E, hE, rfl⟩, hDo, hev⟩ := h𝒞.image_tail.exists_isOpen_eventually_mem_nhdsGT a
  have hev' := hev.and (Ioo_mem_nhdsGT hab)
  -- The cell `E₁` through a point of the graph just right of `a` lies in the graph, over the
  -- open cell `Fin.tail '' E`.
  obtain ⟨t₁, ht₁E, ht₁⟩ := hev'.exists
  have hp₁ : Fin.cons (g ![t₁]) ![t₁] ∈ G := (hmemG _ _).2 ⟨by simpa [A] using ht₁, rfl⟩
  obtain ⟨E₁, ⟨hE₁, hp₁E₁⟩, -⟩ := h𝒞.isPartition.2 (Fin.cons (g ![t₁]) ![t₁])
  have hE₁G : E₁ ⊆ G := (hsub E₁ hE₁).resolve_right fun hd ↦ hd.notMem_of_mem_left hp₁E₁ hp₁
  have htail : Fin.tail '' E₁ = Fin.tail '' E :=
    h𝒞.image_tail.isPartition.pairwiseDisjoint.elim_set (mem_image_of_mem _ hE₁)
      (mem_image_of_mem _ hE) ![t₁] ⟨_, hp₁E₁, Fin.tail_cons _ _⟩ ht₁E
  obtain ⟨h, hh, hhE₁⟩ := h𝒞.exists_continuous_cons_mem hE₁
  have hgh : ContinuousOn g (Fin.tail '' E₁) := by
    refine continuousOn_iff_continuous_domRestrict.2 (hh.congr fun x ↦ ?_)
    exact ((hmemG _ _).1 (hE₁G (hhE₁ x))).2.symm
  rw [htail] at hgh
  exact hev.mono fun t ht ↦ hgh.continuousAt (hDo.mem_nhds ht)

/-- A function of one variable that is semialgebraic on a set containing the points `![t]`,
`t > a` close to `a`, is continuous at these points. -/
theorem IsSemialgebraicOn.eventually_continuousAt_nhdsGT {τ : Type*} [Finite τ]
    {f : (Fin 1 → ℝ) → (τ → ℝ)} {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn f s) {a : ℝ}
    (hs : ∀ᶠ t in 𝓝[>] a, ![t] ∈ s) : ∀ᶠ t in 𝓝[>] a, ContinuousAt f ![t] := by
  simp only [continuousAt_pi]
  exact eventually_all.2 fun i ↦
    eventually_continuousAt_nhdsGT_scalar ((isSemialgebraicOn_pi_iff.1 hf).2 i) hs

/-- A function of one variable that is semialgebraic on a set containing the points `![t]`,
`0 < t < ε₀`, is continuous at `![t]` for all `t` in some interval `(0, δ)`. -/
theorem IsSemialgebraicOn.exists_pos_forall_Ioo_continuousAt {τ : Type*} [Finite τ]
    {f : (Fin 1 → ℝ) → (τ → ℝ)} {s : Set (Fin 1 → ℝ)} (hf : IsSemialgebraicOn f s) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hs : ∀ t ∈ Ioo 0 ε₀, ![t] ∈ s) :
    ∃ δ > 0, ∀ t ∈ Ioo 0 δ, ContinuousAt f ![t] :=
  mem_nhdsGT_iff_exists_Ioo_subset.1 <| hf.eventually_continuousAt_nhdsGT <|
    eventually_of_mem (Ioo_mem_nhdsGT hε₀) hs

/-- A subset of `ℝ` that is semialgebraic as a subset of the line `σ → ℝ`, `σ` having one element,
has finite frontier. -/
theorem finite_frontier_of_isSemialgebraic_preimage_funUnique {σ : Type*} [Unique σ] {t : Set ℝ}
    (ht : IsSemialgebraic (Homeomorph.funUnique σ ℝ ⁻¹' t)) : (frontier t).Finite := by
  -- `t` is the union of the images of finitely many connected sets, which are order-connected.
  set e := Homeomorph.funUnique σ ℝ
  obtain ⟨𝒞, h𝒞, -, hc, hU⟩ := ht.exists_finite_isConnected_partition
  rw [← e.image_preimage t, ← hU, sUnion_eq_biUnion, image_iUnion₂]
  exact (h𝒞.biUnion fun E hE ↦ ((hc E hE).1.isPreconnected.image _
    e.continuous.continuousOn).ordConnected.finite_frontier).subset
    (h𝒞.frontier_biUnion_subset _)

/-- A semialgebraic subset of the line `σ → ℝ`, `σ` having one element, has finite frontier: it
is a finite union of connected sets, each of which has at most two frontier points. -/
theorem IsSemialgebraic.finite_frontier_of_unique {σ : Type*} [Unique σ] {s : Set (σ → ℝ)}
    (hs : IsSemialgebraic s) : (frontier s).Finite := by
  set e := Homeomorph.funUnique σ ℝ
  rw [← e.preimage_image s] at hs ⊢
  rw [← e.preimage_frontier]
  exact (finite_frontier_of_isSemialgebraic_preimage_funUnique hs).preimage e.injective.injOn

end TauCeti

end
