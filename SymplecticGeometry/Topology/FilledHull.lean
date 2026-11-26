/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import TauCeti.Topology.FilledIn
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Frontier

/-!
# Filled sublevel sets and the first exit of a curve

For a set `K` of a topological space, the points whose connected component in `Kᶜ` has compact
closure form `K` together with the relatively compact components of `Kᶜ`. This set is Tau Ceti's
`TauCeti.fillIn K univ`
(`setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn`) and, in an R₀ space, Tau Ceti's
filled hull `TauCeti.filledHull K` for the bornology of relatively compact sets
(`setOfPred_isCompact_closure_connectedComponentIn_compl_eq_filledHull`). Tau Ceti proves it compact
for compact `K` (`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`). Through
these two identifications this file adds what an exhaustion by such sets needs: every component of
its complement has noncompact closure
(`not_isCompact_closure_connectedComponentIn_compl_setOfPred_isCompact_closure`, from
`TauCeti.isFilledIn_fillIn`), and for closed `K` it is closed, its part outside `K` is open, it
lies in the interior of the set built from any `L` with `K ⊆ interior L`, and its frontier lies in
that of `K`.

For a function `h : X → ℝ` and a level `c`, `SymplecticGeometry.filledSublevel h c` is this set
for the sublevel set `{x | h x ≤ c}`. For continuous `h` with compact sublevel sets these sets
form a compact exhaustion of `X`: each is compact, `filledSublevel h c ⊆ interior
(filledSublevel h c')` for `c < c'`, and they cover `X`. Their frontier lies on the level set
`{x | h x = c}`, so a preconnected set on which `h` avoids `c` lies inside or outside
`filledSublevel h c` (`subset_filledSublevel_or_disjoint_of_isPreconnected`, from Tau Ceti's
`IsPreconnected.subset_interior_or_subset_compl_closure`).

`IsClosed.exists_mem_Ico_image_Icc_subset_mem_frontier` locates where a curve from a closed set
to its complement first leaves it: at the infimum `s` of the parameters at which it is outside,
the curve is on the frontier, and it is outside the set at parameters arbitrarily close after
`s`. The **first exit** `SymplecticGeometry.exists_image_Icc_subset_filledSublevel_and_disjoint`
applies it to a filled sublevel set and a curve whose crossings of the level `c` are isolated from
the right: then `α s` is on the level `c`, and just after `s` the curve lies in a single component
of `{x | c < h x}`, which has noncompact closure, so it stays out of the set for a while.

These sets are the compact exhaustion along which proper rays are built in
`SymplecticGeometry/Geometry/Manifold/ProperRay.lean`.

Closedness, openness of the filled-in part and the frontier bound come from Tau Ceti's
`IsClosed.isClosed_filledHull` and `IsClosed.isOpen_filledHull_sdiff`, through the bornology of
relatively compact sets, as in the proof of
`IsCompact.isCompact_setOf_isCompact_closure_connectedComponentIn_compl`.

## Main results

* `setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn`,
  `setOfPred_isCompact_closure_connectedComponentIn_compl_eq_filledHull`,
  `not_isCompact_closure_connectedComponentIn_compl_setOfPred_isCompact_closure`,
  `IsClosed.isClosed_setOfPred_isCompact_closure_connectedComponentIn_compl`,
  `IsClosed.isOpen_setOfPred_isCompact_closure_connectedComponentIn_compl_sdiff`,
  `IsClosed.setOfPred_isCompact_closure_connectedComponentIn_compl_subset_interior`,
  `IsClosed.frontier_setOfPred_isCompact_closure_connectedComponentIn_compl_subset`.
* `IsClosed.exists_mem_Ico_image_Icc_subset_mem_frontier`: where a curve first leaves a closed
  set.
* `SymplecticGeometry.isCompact_filledSublevel`, `SymplecticGeometry.filledSublevel_mono`,
  `SymplecticGeometry.filledSublevel_subset_interior`,
  `SymplecticGeometry.iUnion_filledSublevel`,
  `SymplecticGeometry.frontier_filledSublevel_subset`.
* `SymplecticGeometry.exists_image_Icc_subset_filledSublevel_and_disjoint`: the first exit of
  a curve.
-/

public section

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] {K L : Set X} {x : X}

/-- The set of points whose component in `Kᶜ` has compact closure is Tau Ceti's filling
`TauCeti.fillIn K univ` of `K` in the whole space. -/
theorem setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn :
    {x | IsCompact (closure (connectedComponentIn Kᶜ x))} = TauCeti.fillIn K univ := by
  ext x
  by_cases hx : x ∈ K
  · exact ⟨fun _ ↦ TauCeti.subset_fillIn hx,
      fun _ ↦ TauCeti.isCompact_closure_connectedComponentIn_compl_of_mem hx⟩
  · simp [TauCeti.mem_fillIn_iff, hx, ← compl_eq_univ_sdiff]

/-- **The complement of a filled set has only noncompact components.** If `H` is the set of
points whose component in `Kᶜ` has compact closure, then every component of `Hᶜ` has noncompact
closure. -/
theorem not_isCompact_closure_connectedComponentIn_compl_setOfPred_isCompact_closure
    (hx : x ∉ {x | IsCompact (closure (connectedComponentIn Kᶜ x))}) :
    ¬IsCompact (closure (connectedComponentIn
      {x | IsCompact (closure (connectedComponentIn Kᶜ x))}ᶜ x)) := by
  rw [setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn] at hx ⊢
  simpa [← compl_eq_univ_sdiff] using
    TauCeti.isFilledIn_iff.1 (TauCeti.isFilledIn_fillIn K univ) x ⟨mem_univ x, hx⟩

section Closed

variable [R0Space X]

/-- In an R₀ space, the set of points whose component in `Kᶜ` has compact closure is Tau Ceti's
filled hull of `K` for the bornology of relatively compact sets. -/
theorem setOfPred_isCompact_closure_connectedComponentIn_compl_eq_filledHull :
    {x | IsCompact (closure (connectedComponentIn Kᶜ x))} =
      @TauCeti.filledHull X _ (Bornology.relativelyCompact X) K := by
  ext x
  exact ((@TauCeti.mem_filledHull_iff X _ (.relativelyCompact X) K x).trans
    Bornology.relativelyCompact.isBounded_iff).symm

variable [LocallyConnectedSpace X]

/-- For a closed set `K`, the points whose component in `Kᶜ` has compact closure form a closed
set. -/
theorem IsClosed.isClosed_setOfPred_isCompact_closure_connectedComponentIn_compl (hK : IsClosed K) :
    IsClosed {x | IsCompact (closure (connectedComponentIn Kᶜ x))} := by
  let : Bornology X := .relativelyCompact X
  rw [setOfPred_isCompact_closure_connectedComponentIn_compl_eq_filledHull]
  exact hK.isClosed_filledHull

/-- For a closed set `K`, the points outside `K` whose component in `Kᶜ` has compact closure form
an open set. -/
theorem IsClosed.isOpen_setOfPred_isCompact_closure_connectedComponentIn_compl_sdiff
    (hK : IsClosed K) :
    IsOpen ({x | IsCompact (closure (connectedComponentIn Kᶜ x))} \ K) := by
  let : Bornology X := .relativelyCompact X
  rw [setOfPred_isCompact_closure_connectedComponentIn_compl_eq_filledHull]
  exact hK.isOpen_filledHull_sdiff

/-- For a closed set `K` and a set `L` with `K ⊆ interior L`, the set of points whose component in
`Kᶜ` has compact closure lies in the interior of the corresponding set for `L`. -/
theorem IsClosed.setOfPred_isCompact_closure_connectedComponentIn_compl_subset_interior
    (hK : IsClosed K) (hKL : K ⊆ interior L) :
    {x | IsCompact (closure (connectedComponentIn Kᶜ x))} ⊆
      interior {x | IsCompact (closure (connectedComponentIn Lᶜ x))} := by
  have hmono : {x | IsCompact (closure (connectedComponentIn Kᶜ x))} ⊆
      {x | IsCompact (closure (connectedComponentIn Lᶜ x))} := by
    simp only [setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn]
    exact TauCeti.fillIn_mono (hKL.trans interior_subset)
  intro x hx
  by_cases hxK : x ∈ K
  · refine interior_mono ?_ (hKL hxK)
    exact fun _ hy ↦ TauCeti.isCompact_closure_connectedComponentIn_compl_of_mem hy
  · exact interior_mono hmono <|
      hK.isOpen_setOfPred_isCompact_closure_connectedComponentIn_compl_sdiff.subset_interior_iff.2
        sdiff_subset ⟨hx, hxK⟩

/-- For a closed set `K`, the frontier of the set of points whose component in `Kᶜ` has compact
closure lies in the frontier of `K`. -/
theorem IsClosed.frontier_setOfPred_isCompact_closure_connectedComponentIn_compl_subset
    (hK : IsClosed K) :
    frontier {x | IsCompact (closure (connectedComponentIn Kᶜ x))} ⊆ frontier K := by
  intro x hx
  have hKH : K ⊆ {x | IsCompact (closure (connectedComponentIn Kᶜ x))} :=
    fun _ ↦ TauCeti.isCompact_closure_connectedComponentIn_compl_of_mem
  have hxH := hK.isClosed_setOfPred_isCompact_closure_connectedComponentIn_compl.frontier_subset hx
  have hxK : x ∈ K := by
    by_contra hxK
    have hint : x ∈ interior ({x | IsCompact (closure (connectedComponentIn Kᶜ x))} \ K) := by
      rw [hK.isOpen_setOfPred_isCompact_closure_connectedComponentIn_compl_sdiff.interior_eq]
      exact ⟨hxH, hxK⟩
    exact hx.2 (interior_mono sdiff_subset hint)
  rw [hK.frontier_eq]
  exact ⟨hxK, fun hint ↦ hx.2 (interior_mono hKH hint)⟩

end Closed

/-- **Where a curve first leaves a closed set.** Let `ι` be a densely ordered, conditionally
complete linear order, `F` a closed set and `α : ι → X` continuous on `[a, b]`, with `α a ∈ F`,
`α b ∉ F` and `a < b`. Then there is `s ∈ [a, b)` such that `α` maps `[a, s]` into `F`, `α s`
lies on the frontier of `F`, and every interval `(s, u)` contains a parameter at which `α` is
outside `F`. -/
theorem IsClosed.exists_mem_Ico_image_Icc_subset_mem_frontier {ι : Type*}
    [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    {F : Set X} (hF : IsClosed F) {α : ι → X} {a b : ι} (hα : ContinuousOn α (Icc a b))
    (hab : a < b) (ha : α a ∈ F) (hb : α b ∉ F) :
    ∃ s ∈ Ico a b, α '' Icc a s ⊆ F ∧ α s ∈ frontier F ∧
      ∀ u : ι, s < u → ∃ t ∈ Ioo s u, α t ∉ F := by
  set T := {t | t ∈ Icc a b ∧ α t ∉ F}
  have hbT : b ∈ T := ⟨⟨hab.le, le_rfl⟩, hb⟩
  have hTbdd : BddBelow T := ⟨a, fun t ht ↦ ht.1.1⟩
  set s := sInf T
  have has : a ≤ s := le_csInf ⟨b, hbT⟩ fun t ht ↦ ht.1.1
  have hsb : s ≤ b := csInf_le hTbdd hbT
  -- Before `s` the curve stays in `F`, and so it does at `s`, since `F` is closed.
  have hbefore : α '' Ico a s ⊆ F := by
    rintro _ ⟨t, ht, rfl⟩
    by_contra htF
    exact (csInf_le hTbdd ⟨⟨ht.1, ht.2.le.trans hsb⟩, htF⟩).not_gt ht.2
  have hIcc : α '' Icc a s ⊆ F := by
    rcases has.eq_or_lt with hs | hs
    · rw [← hs, Icc_self, image_singleton]
      exact singleton_subset_iff.2 ha
    · have hc : ContinuousOn α (closure (Ico a s)) := by
        rw [closure_Ico hs.ne]
        exact hα.mono (Icc_subset_Icc_right hsb)
      rw [← closure_Ico hs.ne]
      exact hc.image_closure.trans (closure_minimal hbefore hF)
  have hsF : α s ∈ F := hIcc ⟨s, ⟨has, le_rfl⟩, rfl⟩
  have hsb' : s < b := hsb.lt_of_ne fun hs ↦ hb (hs ▸ hsF)
  -- Right after `s` there are parameters at which the curve is outside `F`.
  have hafter (u : ι) (hu : s < u) : ∃ t ∈ Ioo s u, α t ∉ F := by
    obtain ⟨t, htT, htu⟩ := exists_lt_of_csInf_lt ⟨b, hbT⟩ hu
    exact ⟨t, ⟨(csInf_le hTbdd htT).lt_of_ne fun hst ↦ htT.2 (hst ▸ hsF), htu⟩, htT.2⟩
  refine ⟨s, ⟨has, hsb'⟩, hIcc, ⟨subset_closure hsF, fun hint ↦ ?_⟩, hafter⟩
  have hIcc_nhds : Icc a b ∈ 𝓝[>] s := mem_of_superset (Ioo_mem_nhdsGT hsb')
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc_left has))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hsb').1 <|
    nhdsWithin_le_of_mem hIcc_nhds <|
      (hα s ⟨has, hsb'.le⟩).preimage_mem_nhdsWithin (isOpen_interior.mem_nhds hint)
  obtain ⟨t, ht, htF⟩ := hafter u hu
  exact htF (interior_subset (hsub ht))

namespace SymplecticGeometry

variable {h : X → ℝ} {c c' : ℝ}

/-- The **filled sublevel set** of `h : X → ℝ` at level `c`: the points whose connected component
in the complement of `{x | h x ≤ c}` has compact closure. It is the sublevel set together with
the components of its complement that have compact closure. -/
def filledSublevel (h : X → ℝ) (c : ℝ) : Set X :=
  {x | IsCompact (closure (connectedComponentIn {y | h y ≤ c}ᶜ x))}

theorem filledSublevel_def (h : X → ℝ) (c : ℝ) :
    filledSublevel h c = {x | IsCompact (closure (connectedComponentIn {y | h y ≤ c}ᶜ x))} :=
  (rfl)

@[simp]
theorem mem_filledSublevel_iff :
    x ∈ filledSublevel h c ↔ IsCompact (closure (connectedComponentIn {y | h y ≤ c}ᶜ x)) := by
  rw [filledSublevel_def, mem_ofPred]

/-- A filled sublevel set contains the sublevel set. -/
theorem setOfPred_le_subset_filledSublevel : {x | h x ≤ c} ⊆ filledSublevel h c := fun _ hx ↦
  mem_filledSublevel_iff.2 (TauCeti.isCompact_closure_connectedComponentIn_compl_of_mem hx)

/-- The filled sublevel sets increase with the level. -/
theorem filledSublevel_mono : Monotone (filledSublevel h) := fun _ _ hcc ↦ by
  simp only [filledSublevel_def, setOfPred_isCompact_closure_connectedComponentIn_compl_eq_fillIn]
  exact TauCeti.fillIn_mono fun _ (hx : _ ≤ _) ↦ hx.trans hcc

/-- The filled sublevel sets cover the space. -/
theorem iUnion_filledSublevel : ⋃ c, filledSublevel h c = univ :=
  eq_univ_of_forall fun x ↦
    mem_iUnion.2 ⟨h x, setOfPred_le_subset_filledSublevel (show h x ≤ h x from le_rfl)⟩

/-- Every component of the complement of a filled sublevel set has noncompact closure. -/
theorem not_isCompact_closure_connectedComponentIn_compl_filledSublevel
    (hx : x ∉ filledSublevel h c) :
    ¬IsCompact (closure (connectedComponentIn (filledSublevel h c)ᶜ x)) := by
  rw [filledSublevel_def] at hx ⊢
  exact not_isCompact_closure_connectedComponentIn_compl_setOfPred_isCompact_closure hx

/-- A filled sublevel set of a compact sublevel set is compact, in a locally compact Hausdorff,
locally connected space with no compact connected component. -/
theorem isCompact_filledSublevel [T2Space X] [WeaklyLocallyCompactSpace X]
    [LocallyConnectedSpace X] (hX : ∀ x : X, ¬IsCompact (connectedComponent x))
    (hc : IsCompact {x | h x ≤ c}) : IsCompact (filledSublevel h c) := by
  rw [filledSublevel_def]
  exact hc.isCompact_setOf_isCompact_closure_connectedComponentIn_compl hX

variable [R0Space X] [LocallyConnectedSpace X]

/-- The filled sublevel sets of a continuous function are closed. -/
theorem isClosed_filledSublevel (hh : Continuous h) : IsClosed (filledSublevel h c) := by
  rw [filledSublevel_def]
  exact IsClosed.isClosed_setOfPred_isCompact_closure_connectedComponentIn_compl
    (isClosed_le hh continuous_const)

/-- A filled sublevel set lies in the interior of every filled sublevel set of a higher level. -/
theorem filledSublevel_subset_interior (hh : Continuous h) (hcc : c < c') :
    filledSublevel h c ⊆ interior (filledSublevel h c') := by
  rw [filledSublevel_def, filledSublevel_def]
  exact IsClosed.setOfPred_isCompact_closure_connectedComponentIn_compl_subset_interior
    (isClosed_le hh continuous_const) fun x (hx : h x ≤ c) ↦ mem_interior_iff_mem_nhds.2 <|
      mem_of_superset ((isOpen_lt hh continuous_const).mem_nhds (show h x < c' from
        hx.trans_lt hcc)) fun _ (hy : h _ < c') ↦ hy.le

/-- The frontier of a filled sublevel set lies on the level set. -/
theorem frontier_filledSublevel_subset (hh : Continuous h) :
    frontier (filledSublevel h c) ⊆ {x | h x = c} := by
  rw [filledSublevel_def]
  exact (IsClosed.frontier_setOfPred_isCompact_closure_connectedComponentIn_compl_subset
    (isClosed_le hh continuous_const)).trans (frontier_le_subset_eq hh continuous_const)

/-- A preconnected set on which `h` never takes the value `c` lies in `filledSublevel h c` or
misses it, since the frontier of that set lies on the level `c`. -/
theorem subset_filledSublevel_or_disjoint_of_isPreconnected (hh : Continuous h) {S : Set X}
    (hS : IsPreconnected S) (hc : ∀ x ∈ S, h x ≠ c) :
    S ⊆ filledSublevel h c ∨ Disjoint S (filledSublevel h c) := by
  rcases hS.subset_interior_or_subset_compl_closure (disjoint_left.2 fun x hx hfr ↦
      hc x hx (frontier_filledSublevel_subset hh hfr)) with h₁ | h₁
  · exact .inl (h₁.trans interior_subset)
  · exact .inr (subset_compl_iff_disjoint_right.1 (h₁.trans (compl_subset_compl.2 subset_closure)))

/-- **First exit of a curve from a filled sublevel set.** Let `α : ℝ → X` be a continuous curve
with `α a` in the filled sublevel set `filledSublevel h c` and `α b` outside it, where `a < b`,
and suppose that each parameter `t ∈ [a, b)` with `h (α t) = c` is followed by an interval on
which `h ∘ α` differs from `c`; this holds when the zeros of `h ∘ α - c` in `[a, b]` are isolated.
Then there is `s ∈ [a, b)` such that `α` maps `[a, s]` into the set and some `(s, s + ε₀]`,
`ε₀ > 0`, outside it. -/
theorem exists_image_Icc_subset_filledSublevel_and_disjoint (hh : Continuous h)
    {α : ℝ → X} (hα : Continuous α) {a b : ℝ} (hab : a < b) (ha : α a ∈ filledSublevel h c)
    (hb : α b ∉ filledSublevel h c)
    (hzero : ∀ t ∈ Ico a b, h (α t) = c → ∀ᶠ u in 𝓝[>] t, h (α u) ≠ c) :
    ∃ s ∈ Ico a b, α '' Icc a s ⊆ filledSublevel h c ∧
      ∃ ε₀ > 0, Disjoint (α '' Ioc s (s + ε₀)) (filledSublevel h c) := by
  obtain ⟨s, ⟨has, hsb⟩, hIcc, hfr, hafter⟩ :=
    (isClosed_filledSublevel (c := c) hh).exists_mem_Ico_image_Icc_subset_mem_frontier
      hα.continuousOn hab ha hb
  have hsc : h (α s) = c := frontier_filledSublevel_subset hh hfr
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 <|
    (hzero s ⟨has, hsb⟩ hsc).and (Ioo_mem_nhdsGT hsb)
  set ε₀ := (u - s) / 2
  have hε₀ : 0 < ε₀ := by simp only [ε₀]; linarith [mem_Ioi.1 hu]
  have hJ : Ioc s (s + ε₀) ⊆ Ioo s u := fun t ht ↦ ⟨ht.1, by
    simp only [ε₀] at ht; linarith [ht.2, mem_Ioi.1 hu]⟩
  obtain ⟨t₀, ht₀, ht₀F⟩ := hafter (s + ε₀) (by linarith)
  have ht₀J : t₀ ∈ Ioc s (s + ε₀) := Ioo_subset_Ioc_self ht₀
  have hct₀ : c < h (α t₀) := not_le.1 fun hle ↦ ht₀F (setOfPred_le_subset_filledSublevel hle)
  -- On `(s, s + ε₀]` the curve stays above the level `c`, by the intermediate value theorem.
  have habove : ∀ t ∈ Ioc s (s + ε₀), c < h (α t) := by
    intro t ht
    refine lt_of_le_of_ne (not_lt.1 fun hlt ↦ ?_) fun hct ↦ (hsub (hJ ht)).1 hct.symm
    obtain ⟨t', ht', hct'⟩ := isPreconnected_Ioc.intermediate_value ht ht₀J
      (hh.comp hα).continuousOn ⟨hlt.le, hct₀.le⟩
    exact (hsub (hJ ht')).1 hct'
  -- Its image there is preconnected and misses `{x | h x ≤ c}`, so it lies in the component of
  -- `α t₀`, which has noncompact closure.
  refine ⟨s, ⟨has, hsb⟩, hIcc, ε₀, hε₀, disjoint_left.2 ?_⟩
  have hcomp : α '' Ioc s (s + ε₀) ⊆ connectedComponentIn {y | h y ≤ c}ᶜ (α t₀) :=
    (isPreconnected_Ioc.image _ hα.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem α ht₀J) (by rintro _ ⟨t, ht, rfl⟩; exact not_le.2 (habove t ht))
  intro y hy hyF
  refine ht₀F ?_
  rw [mem_filledSublevel_iff, connectedComponentIn_eq (hcomp hy)]
  exact hyF

end SymplecticGeometry

end
