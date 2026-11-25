/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Convex open sets minus a piece of a hyperplane

Let `T` be a convex open set in a real topological vector space and `g` a nonzero continuous
linear functional. Removing from `T` any subset `L` of the hyperplane `g = 0` leaves at most two
preconnected pieces: the points of `T \ L` where `0 ≤ g`, and those where `g ≤ 0`. Each piece
lies between the convex set `T ∩ {±g > 0}` and its closure (an open half-space of `g` has the
closed one as closure, `ContinuousLinearMap.closure_setOfPred_lt_apply`), and the closure of each
contains `T ∩ L` (`Convex.exists_isPreconnected_diff_of_subset_ker`). If `T` meets the
hyperplane outside `L`, the two pieces share a point and `T \ L` is preconnected
(`Convex.isPreconnected_diff_of_subset_ker`).

In a product `E × F` with `F` nontrivial and separated by its dual, this applies to
`L = K ×ˢ {0}` (`Convex.exists_isPreconnected_diff_prod_zero`,
`Convex.isPreconnected_diff_prod_zero`), and in `ℝ × F` to a piece `K` of the line that stops at
a point `b` with `(b, 0) ∈ T` (`Convex.isPreconnected_diff_prod_zero_of_subset_Iic`,
`Convex.isPreconnected_diff_prod_zero_of_subset_Ici`). These are the model for the complement of
an embedded arc in a slice chart.
-/

public section

open Set Topology

namespace Convex

section Hyperplane

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] {T L : Set V} {g : StrongDual ℝ V}

omit [IsTopologicalAddGroup V] in
/-- The closure of the open half-space `{z | a < g z}` of a nonzero continuous linear
functional `g` is the closed half-space `{z | a ≤ g z}`. -/
theorem _root_.ContinuousLinearMap.closure_setOfPred_lt_apply [ContinuousAdd V] (hg : g ≠ 0)
    (a : ℝ) :
    closure {z | a < g z} = {z | a ≤ g z} := by
  have h := (g.isOpenMap_of_ne_zero hg).preimage_closure_eq_closure_preimage g.continuous (Ioi a)
  rw [closure_Ioi] at h
  simpa only [preimage, mem_Ici, mem_Ioi] using h.symm

omit [IsTopologicalAddGroup V] in
/-- In an open set `T`, the points where a nonzero continuous linear functional `g` is
nonnegative lie in the closure of those where it is positive. -/
theorem _root_.IsOpen.inter_setOfPred_nonneg_subset_closure [ContinuousAdd V] (hT : IsOpen T)
    (hg : g ≠ 0) :
    T ∩ {z | 0 ≤ g z} ⊆ closure (T ∩ {z | 0 < g z}) := by
  rw [← g.closure_setOfPred_lt_apply hg 0]
  exact hT.inter_closure

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
private theorem inter_setOfPred_pos_subset (hL : L ⊆ {z | g z = 0}) :
    T ∩ {z | 0 < g z} ⊆ (T \ L) ∩ {z | 0 ≤ g z} := by
  rintro z ⟨hzT, hz : 0 < g z⟩
  exact ⟨⟨hzT, fun hzL => hz.ne' (hL hzL)⟩, hz.le⟩

/-- In a convex open set `T`, the points of `T \ L` where a nonzero continuous linear functional
`g` is nonnegative form a preconnected set, for `L` in the kernel of `g`. -/
theorem isPreconnected_diff_inter_setOfPred_nonneg (hTc : Convex ℝ T) (hT : IsOpen T)
    (hg : g ≠ 0) (hL : L ⊆ {z | g z = 0}) :
    IsPreconnected ((T \ L) ∩ {z | 0 ≤ g z}) :=
  ((hTc.inter (convex_halfSpace_gt g.isLinear 0)).isPreconnected).subset_closure
    (inter_setOfPred_pos_subset hL)
    fun _ hz => hT.inter_setOfPred_nonneg_subset_closure hg ⟨hz.1.1, hz.2⟩

/-- In an open set `T`, the points of a subset `L` of the kernel of a nonzero continuous linear
functional `g` lie in the closure of the points of `T \ L` where `g` is nonnegative. -/
theorem _root_.IsOpen.inter_subset_closure_diff_inter_setOfPred_nonneg (hT : IsOpen T)
    (hg : g ≠ 0) (hL : L ⊆ {z | g z = 0}) :
    T ∩ L ⊆ closure ((T \ L) ∩ {z | 0 ≤ g z}) := fun _ hz =>
  closure_mono (inter_setOfPred_pos_subset hL)
    (hT.inter_setOfPred_nonneg_subset_closure hg ⟨hz.1, (hL hz.2).ge⟩)

/-- The half of `isPreconnected_diff_inter_setOfPred_nonneg` where `g` is nonpositive. -/
theorem isPreconnected_diff_inter_setOfPred_nonpos (hTc : Convex ℝ T) (hT : IsOpen T)
    (hg : g ≠ 0) (hL : L ⊆ {z | g z = 0}) :
    IsPreconnected ((T \ L) ∩ {z | g z ≤ 0}) := by
  simpa using isPreconnected_diff_inter_setOfPred_nonneg hTc hT (neg_ne_zero.2 hg)
    (L := L) fun z hz => by simp [show g z = 0 from hL hz]

/-- The half of `IsOpen.inter_subset_closure_diff_inter_setOfPred_nonneg` where `g` is
nonpositive. -/
theorem _root_.IsOpen.inter_subset_closure_diff_inter_setOfPred_nonpos (hT : IsOpen T)
    (hg : g ≠ 0) (hL : L ⊆ {z | g z = 0}) :
    T ∩ L ⊆ closure ((T \ L) ∩ {z | g z ≤ 0}) := by
  simpa using hT.inter_subset_closure_diff_inter_setOfPred_nonneg (neg_ne_zero.2 hg)
    (L := L) fun z hz => by simp [show g z = 0 from hL hz]

/-- Removing from a convex open set `T` a subset `L` of the kernel of a nonzero continuous linear
functional leaves the union of two preconnected sets `P`, `Q` whose closures both contain
`T ∩ L`. -/
theorem exists_isPreconnected_diff_of_subset_ker (hTc : Convex ℝ T) (hT : IsOpen T) (hg : g ≠ 0)
    (hL : L ⊆ {z | g z = 0}) :
    ∃ P Q : Set V, IsPreconnected P ∧ IsPreconnected Q ∧ T \ L = P ∪ Q ∧
      T ∩ L ⊆ closure P ∩ closure Q :=
  ⟨_, _, isPreconnected_diff_inter_setOfPred_nonneg hTc hT hg hL,
    isPreconnected_diff_inter_setOfPred_nonpos hTc hT hg hL,
    by rw [← inter_union_distrib_left, ← ofPred_or]; simp [le_total],
    subset_inter (hT.inter_subset_closure_diff_inter_setOfPred_nonneg hg hL)
      (hT.inter_subset_closure_diff_inter_setOfPred_nonpos hg hL)⟩

/-- If a convex open set `T` meets the kernel of a nonzero continuous linear functional at a point
outside `L`, then removing from `T` a subset `L` of that kernel leaves a preconnected set. -/
theorem isPreconnected_diff_of_subset_ker (hTc : Convex ℝ T) (hT : IsOpen T) (hg : g ≠ 0)
    (hL : L ⊆ {z | g z = 0}) {x : V} (hxT : x ∈ T) (hxL : x ∉ L) (hx : g x = 0) :
    IsPreconnected (T \ L) := by
  have h := IsPreconnected.union x (s := (T \ L) ∩ {z | 0 ≤ g z})
    (t := (T \ L) ∩ {z | g z ≤ 0}) ⟨⟨hxT, hxL⟩, hx.ge⟩ ⟨⟨hxT, hxL⟩, hx.le⟩
    (isPreconnected_diff_inter_setOfPred_nonneg hTc hT hg hL)
    (isPreconnected_diff_inter_setOfPred_nonpos hTc hT hg hL)
  rw [← inter_union_distrib_left, ← ofPred_or] at h
  simpa [le_total] using h

end Hyperplane

section Prod

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [SeparatingDual ℝ F]
  [Nontrivial F] {T : Set (E × F)}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] in
/-- A nonzero continuous linear functional on `E × F` that vanishes on `E × {0}`. -/
private theorem exists_ne_zero_forall_prod_zero :
    ∃ g : StrongDual ℝ (E × F), g ≠ 0 ∧ ∀ c : E, g (c, 0) = 0 := by
  obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : StrongDual ℝ F)
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 hℓ
  exact ⟨ℓ.comp (ContinuousLinearMap.snd ℝ E F),
    fun h => hy (by simpa using DFunLike.congr_fun h (0, y)), fun c => by simp⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [SeparatingDual ℝ F] [Nontrivial F] in
private theorem prod_zero_subset_ker {g : StrongDual ℝ (E × F)} (hg : ∀ c : E, g (c, 0) = 0)
    (K : Set E) : K ×ˢ ({0} : Set F) ⊆ {z | g z = 0} := by
  rintro ⟨c, y⟩ ⟨-, rfl : y = 0⟩
  exact hg c

/-- In a product `E × F` with `F` nontrivial and separated by its dual (for instance a nontrivial
real normed space), removing from a convex open set `T` a piece `K ×ˢ {0}` of `E × {0}` leaves
the union of two preconnected sets `P`, `Q` whose closures both contain `T ∩ K ×ˢ {0}`. -/
theorem exists_isPreconnected_diff_prod_zero (hTc : Convex ℝ T) (hT : IsOpen T) (K : Set E) :
    ∃ P Q : Set (E × F), IsPreconnected P ∧ IsPreconnected Q ∧ T \ K ×ˢ {0} = P ∪ Q ∧
      T ∩ K ×ˢ {0} ⊆ closure P ∩ closure Q :=
  let ⟨_, hg, hg0⟩ := exists_ne_zero_forall_prod_zero (E := E) (F := F)
  exists_isPreconnected_diff_of_subset_ker hTc hT hg (prod_zero_subset_ker hg0 K)

/-- In a product `E × F` with `F` nontrivial and separated by its dual (for instance a nontrivial
real normed space), removing from a convex open set `T` a piece `K ×ˢ {0}` of `E × {0}` leaves
a preconnected set, provided `(c, 0) ∈ T` for some `c ∉ K`. -/
theorem isPreconnected_diff_prod_zero (hTc : Convex ℝ T) (hT : IsOpen T) {K : Set E} {c : E}
    (hcT : (c, 0) ∈ T) (hcK : c ∉ K) : IsPreconnected (T \ K ×ˢ {0}) :=
  let ⟨_, hg, hg0⟩ := exists_ne_zero_forall_prod_zero (E := E) (F := F)
  isPreconnected_diff_of_subset_ker hTc hT hg (prod_zero_subset_ker hg0 K) hcT
    (fun h => hcK h.1) (hg0 c)

end Prod

section Real

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [SeparatingDual ℝ F] [Nontrivial F]
  {T : Set (ℝ × F)} {K : Set ℝ} {b : ℝ}

/-- In `ℝ × F` with `F` nontrivial and separated by its dual (for instance a nontrivial real
normed space), removing from a convex open set `T` a piece `K ×ˢ {0}` of the line `ℝ × {0}`
with `K ⊆ Iic b` leaves a preconnected set, provided `(b, 0) ∈ T`. -/
theorem isPreconnected_diff_prod_zero_of_subset_Iic (hTc : Convex ℝ T) (hT : IsOpen T)
    (hK : K ⊆ Iic b) (hbT : (b, 0) ∈ T) : IsPreconnected (T \ K ×ˢ {0}) := by
  have hs : (fun t : ℝ => ((t, 0) : ℝ × F)) ⁻¹' T ∈ 𝓝 b :=
    (hT.preimage (by fun_prop)).mem_nhds hbT
  obtain ⟨c, hcT, hbc : b < c⟩ :=
    Filter.nonempty_of_mem <|
      Filter.inter_mem (nhdsWithin_le_nhds (s := Ioi b) hs) self_mem_nhdsWithin
  exact isPreconnected_diff_prod_zero hTc hT hcT fun hcK => (hK hcK).not_gt hbc

/-- In `ℝ × F` with `F` nontrivial and separated by its dual (for instance a nontrivial real
normed space), removing from a convex open set `T` a piece `K ×ˢ {0}` of the line `ℝ × {0}`
with `K ⊆ Ici b` leaves a preconnected set, provided `(b, 0) ∈ T`. -/
theorem isPreconnected_diff_prod_zero_of_subset_Ici (hTc : Convex ℝ T) (hT : IsOpen T)
    (hK : K ⊆ Ici b) (hbT : (b, 0) ∈ T) : IsPreconnected (T \ K ×ˢ {0}) := by
  have hs : (fun t : ℝ => ((t, 0) : ℝ × F)) ⁻¹' T ∈ 𝓝 b :=
    (hT.preimage (by fun_prop)).mem_nhds hbT
  obtain ⟨c, hcT, hcb : c < b⟩ :=
    Filter.nonempty_of_mem <|
      Filter.inter_mem (nhdsWithin_le_nhds (s := Iio b) hs) self_mem_nhdsWithin
  exact isPreconnected_diff_prod_zero hTc hT hcT fun hcK => (hK hcK).not_gt hcb

end Real

end Convex
