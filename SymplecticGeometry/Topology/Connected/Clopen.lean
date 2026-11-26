/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Preconnected sets and clopen sets

A dense subset `s` of a preconnected space is preconnected as soon as every point of the space
has a neighbourhood `t` such that `t ∩ s` is preconnected. Applied to the interior of a manifold
with boundary, this shows that the interior of a connected manifold is connected.

## Main results

* `Dense.isPreconnected_of_forall_exists_mem_nhds`: the criterion above.
* `IsPreconnected.subset_of_isClopen_preimage_val`: a preconnected `s` that meets a set `t` whose
  trace on some `u ⊇ s` is open and closed in `u` lies in `t`.
* `IsPreconnected.inter_of_isClopen_preimage_val`: cutting a preconnected set `s` by a set whose
  trace on some `u ⊇ s` is open and closed in `u` leaves a preconnected set.
* `PreconnectedSpace.eq_zero_of_eventually_eq_zero`: on a preconnected space, let `f` be a
  function such that at every point, zero or not, either `f` vanishes on a neighbourhood or `f`
  has no zero on a punctured neighbourhood. If `f` vanishes near one point, then `f = 0`.
* `isPreconnected_compl_of_forall_exists_mem_nhds`: in a preconnected space, the complement of a
  preconnected set `A` is preconnected if near each point of `A` the complement of `A` has at most
  two preconnected pieces, each with all of `A` nearby in its closure, and near one point of `A`
  it has only one.
* `IsPreconnected.sdiff_of_forall_exists_mem_nhds`: the same inside a preconnected set `U`, with
  the neighbourhoods taken inside `U`.

`PreconnectedSpace.eq_zero_of_eventually_eq_zero` abstracts the open-and-closed argument of
Tau Ceti's `TauCeti.not_eventually_eq_zero_of_conjWirtingerDeriv_apply_one_eq_mul`.

The proof of `isPreconnected_compl_of_forall_exists_mem_nhds` adapts that of Tau Ceti's
`TauCeti.isPreconnected_compl_of_isDiscrete`: given a separation of the complement, each point of
`A` joins the side that contains its neighbourhood outside `A`, and the points of `A` that join
neither side form a set that is open in `A`. Its relative form
`IsPreconnected.sdiff_of_forall_exists_mem_nhds` passes to the subspace `U`, as the proof of
Tau Ceti's `TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank` does.
-/

public section

open Set Topology Relation Filter

variable {X : Type*} [TopologicalSpace X]

/-- A dense subset `s` of a preconnected space is preconnected if every point `x` has a
neighbourhood `t` with `t ∩ s` preconnected. The point `x` need not lie in `s`. -/
theorem Dense.isPreconnected_of_forall_exists_mem_nhds [PreconnectedSpace X] {s : Set X}
    (hs : Dense s) (h : ∀ x, ∃ t ∈ 𝓝 x, IsPreconnected (t ∩ s)) : IsPreconnected s := by
  choose t ht hpre using h
  have hU : (⋃ x, t x ∩ s) = s :=
    Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_right)
      fun a ha ↦ mem_iUnion.2 ⟨a, mem_of_mem_nhds (ht a), ha⟩
  -- Two points whose neighbourhoods `t` meet near each other give sets that meet in `s`.
  have hmeet : ∀ x, ∀ᶠ y in 𝓝 x, (t x ∩ s ∩ (t y ∩ s)).Nonempty := fun x ↦ by
    filter_upwards [interior_mem_nhds.2 (ht x)] with y hy
    obtain ⟨z, ⟨hzx, hzy⟩, hz⟩ := hs.inter_open_nonempty (interior (t x) ∩ interior (t y))
      (isOpen_interior.inter isOpen_interior) ⟨y, hy, mem_interior_iff_mem_nhds.2 (ht y)⟩
    exact ⟨z, ⟨interior_subset hzx, hz⟩, interior_subset hzy, hz⟩
  rw [← hU]
  refine IsPreconnected.iUnion_of_reflTransGen hpre fun x y ↦ ?_
  refine PreconnectedSpace.induction₂' _ (fun x ↦ ?_) ⟨fun _ _ _ ↦ ReflTransGen.trans⟩ x y
  filter_upwards [hmeet x] with y hy
  exact ⟨ReflTransGen.single hy, ReflTransGen.single (by rwa [inter_comm])⟩

/-- If `s ⊆ u` is preconnected, the trace of `t` on `u` is open and closed in `u`, and `s` meets
`t`, then `s ⊆ t`. This is `IsPreconnected.subset_isClopen` relative to `u`. -/
theorem IsPreconnected.subset_of_isClopen_preimage_val {s t u : Set X} (hs : IsPreconnected s)
    (hsu : s ⊆ u) (ht : IsClopen ((↑) ⁻¹' t : Set u)) (hne : (s ∩ t).Nonempty) : s ⊆ t := by
  obtain ⟨x, hxs, hxt⟩ := hne
  have hs' : IsPreconnected ((↑) ⁻¹' s : Set u) := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hsu]
  have hst := hs'.subset_isClopen ht ⟨⟨x, hsu hxs⟩, hxs, hxt⟩
  exact fun y hy ↦ hst (a := ⟨y, hsu hy⟩) hy

/-- If `s ⊆ u` is preconnected and the trace of `t` on `u` is open and closed in `u`, then
`s ∩ t` is preconnected: it is either empty or all of `s`. -/
theorem IsPreconnected.inter_of_isClopen_preimage_val {s t u : Set X} (hs : IsPreconnected s)
    (hsu : s ⊆ u) (ht : IsClopen ((↑) ⁻¹' t : Set u)) : IsPreconnected (s ∩ t) := by
  rcases (s ∩ t).eq_empty_or_nonempty with h | h
  · rw [h]
    exact isPreconnected_empty
  rwa [inter_eq_left.2 (hs.subset_of_isClopen_preimage_val hsu ht h)]

/-- **Unique continuation from a dichotomy.** On a preconnected space, let `f` be a function
such that at each point `x`, either `f` vanishes on a neighbourhood of `x`, or `f` has no zero on
a punctured neighbourhood of `x`. If `f` vanishes on a neighbourhood of one point, then `f = 0`. -/
theorem PreconnectedSpace.eq_zero_of_eventually_eq_zero [PreconnectedSpace X] {M : Type*}
    [Zero M] {f : X → M}
    (hf : ∀ x, (∀ᶠ y in 𝓝 x, f y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) {z : X}
    (hz : ∀ᶠ y in 𝓝 z, f y = 0) : f = 0 := by
  set S := {x | ∀ᶠ y in 𝓝 x, f y = 0}
  have hS : IsClopen S := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_),
      isOpen_setOfPred_eventually_nhds⟩
    filter_upwards [eventually_nhdsWithin_iff.1 ((hf x).resolve_left hx)] with y hy hyS
    obtain rfl | hyx := eq_or_ne y x
    · exact hx hyS
    · exact hy hyx hyS.self_of_nhds
  exact funext fun x ↦ (hS.eq_univ ⟨z, hz⟩ ▸ mem_univ x : x ∈ S).self_of_nhds

/-- A step of `isPreconnected_compl_of_forall_exists_mem_nhds`: let `s` and `t` be sets that do
not meet outside `A`, and let `Q ⊆ t` be a set outside `A`, inside a neighbourhood `V` of `x`,
whose closure contains `V ∩ A`. Then near `x`, no point of `A` has a neighbourhood whose part
outside `A` lies in `s`. -/
private theorem eventually_not_eventually_mem_of_subset_closure {A s t : Set X}
    (hst : ∀ y, y ∉ A → y ∈ s → y ∈ t → False) {x : X} {V Q : Set X} (hV : V ∈ 𝓝 x)
    (hQV : Q ⊆ V \ A) (hQ : V ∩ A ⊆ closure Q) (hQt : Q ⊆ t) :
    ∀ᶠ y in 𝓝 x, y ∈ A → ¬ ∀ᶠ z in 𝓝 y, z ∉ A → z ∈ s := by
  filter_upwards [eventually_mem_nhds_iff.2 hV] with y hyV hyA hys
  obtain ⟨z, ⟨hzs, -⟩, hzQ⟩ :=
    mem_closure_iff_nhds.1 (hQ ⟨mem_of_mem_nhds hyV, hyA⟩) _ (hys.and hyV)
  exact hst z (hQV hzQ).2 (hzs (hQV hzQ).2) (hQt hzQ)

/-- A step of `isPreconnected_compl_of_forall_exists_mem_nhds`: let `u` and `v` be open sets
that cover the complement of `A` and do not meet outside `A`. Near a point `x` with a
neighbourhood `V` as in that theorem, either all points near `x` outside `A` lie in `u`,
or all lie in `v`, or no point of `A` near `x` has a neighbourhood whose part outside `A` lies
in `u` or in `v`. -/
private theorem eventually_mem_or_eventually_not {A u v : Set X} (hu : IsOpen u) (hv : IsOpen v)
    (hcov : Aᶜ ⊆ u ∪ v) (huv : ∀ y, y ∉ A → y ∈ u → y ∈ v → False) {x : X} {V P Q : Set X}
    (hV : V ∈ 𝓝 x) (hPQ : V \ A = P ∪ Q) (hP : IsPreconnected P) (hQ : IsPreconnected Q)
    (hcl : V ∩ A ⊆ closure P ∩ closure Q) :
    (∀ᶠ y in 𝓝 x, y ∉ A → y ∈ u) ∨ (∀ᶠ y in 𝓝 x, y ∉ A → y ∈ v) ∨
      ∀ᶠ y in 𝓝 x, y ∈ A →
        (¬ ∀ᶠ z in 𝓝 y, z ∉ A → z ∈ u) ∧ ¬ ∀ᶠ z in 𝓝 y, z ∉ A → z ∈ v := by
  have hside (S : Set X) (hS : S ⊆ V \ A) (hSp : IsPreconnected S) : S ⊆ u ∨ S ⊆ v :=
    isPreconnected_iff_subset_of_disjoint.1 hSp u v hu hv (fun y hy ↦ hcov (hS hy).2)
      (eq_empty_iff_forall_notMem.2 fun y ⟨hy, hyu, hyv⟩ ↦ huv y (hS hy).2 hyu hyv)
  have hPV : P ⊆ V \ A := hPQ ▸ subset_union_left
  have hQV : Q ⊆ V \ A := hPQ ▸ subset_union_right
  have hall {s : Set X} (hPs : P ⊆ s) (hQs : Q ⊆ s) : ∀ᶠ y in 𝓝 x, y ∉ A → y ∈ s := by
    filter_upwards [hV] with y hyV hyA
    exact (union_subset hPs hQs) (hPQ ▸ ⟨hyV, hyA⟩ : y ∈ P ∪ Q)
  have hvu (y : X) (hy : y ∉ A) (hyv : y ∈ v) (hyu : y ∈ u) : False := huv y hy hyu hyv
  have hPc : V ∩ A ⊆ closure P := fun y hy ↦ (hcl hy).1
  have hQc : V ∩ A ⊆ closure Q := fun y hy ↦ (hcl hy).2
  rcases hside P hPV hP with hPu | hPv <;> rcases hside Q hQV hQ with hQu | hQv
  · exact Or.inl (hall hPu hQu)
  · refine Or.inr (Or.inr ?_)
    filter_upwards [eventually_not_eventually_mem_of_subset_closure huv hV hQV hQc hQv,
      eventually_not_eventually_mem_of_subset_closure hvu hV hPV hPc hPu] with y h₁ h₂ hyA
    exact ⟨h₁ hyA, h₂ hyA⟩
  · refine Or.inr (Or.inr ?_)
    filter_upwards [eventually_not_eventually_mem_of_subset_closure huv hV hPV hPc hPv,
      eventually_not_eventually_mem_of_subset_closure hvu hV hQV hQc hQu] with y h₁ h₂ hyA
    exact ⟨h₁ hyA, h₂ hyA⟩
  · exact Or.inr (Or.inl (hall hPv hQv))

/-- **Removing a set that separates at most two ways locally.** In a preconnected space, let `A`
be a preconnected set such that each point `a ∈ A` has a neighbourhood `V` whose part outside
`A` is the union of two preconnected sets `P` and `Q` (which may meet or coincide) whose
closures both contain `V ∩ A`. If one point `b ∈ A` has a neighbourhood whose part outside `A`
is preconnected, then the complement of `A` is preconnected.

Without the condition at `b`, the statement fails: an equator separates a sphere. -/
theorem isPreconnected_compl_of_forall_exists_mem_nhds [PreconnectedSpace X] {A : Set X}
    (hA : IsPreconnected A) {b : X} (hb : b ∈ A)
    (hbV : ∃ V ∈ 𝓝 b, IsPreconnected (V \ A))
    (h : ∀ a ∈ A, ∃ V ∈ 𝓝 a, ∃ P Q : Set X, V \ A = P ∪ Q ∧ IsPreconnected P ∧
      IsPreconnected Q ∧ V ∩ A ⊆ closure P ∩ closure Q) :
    IsPreconnected Aᶜ := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  have huv (y : X) (hy : y ∉ A) (hyu : y ∈ u) (hyv : y ∈ v) : False :=
    (eq_empty_iff_forall_notMem.1 hdisj) y ⟨hy, hyu, hyv⟩
  -- The points with a neighbourhood whose part outside `A` lies in `u`, respectively `v`, are
  -- disjoint open sets, since each point of `A` is in the closure of `Aᶜ`.
  set U' := {x | ∀ᶠ y in 𝓝 x, y ∉ A → y ∈ u}
  set V' := {x | ∀ᶠ y in 𝓝 x, y ∉ A → y ∈ v}
  have hUV (x : X) (hxu : x ∈ U') (hxv : x ∈ V') : False := by
    by_cases hx : x ∈ A
    · obtain ⟨V, hV, P, Q, hPQ, -, -, hcl⟩ := h x hx
      obtain ⟨y, ⟨hyu, hyv⟩, hyP⟩ :=
        mem_closure_iff_nhds.1 (hcl ⟨mem_of_mem_nhds hV, hx⟩).1 _ (hxu.and hxv)
      have hyA : y ∉ A := (hPQ ▸ subset_union_left hyP : y ∈ V \ A).2
      exact huv y hyA (hyu hyA) (hyv hyA)
    · exact huv x hx (hxu.self_of_nhds hx) (hxv.self_of_nhds hx)
  -- The points of `A` of neither kind form a set that is open in `A` and misses `b`, so it is
  -- empty since `A` is preconnected.
  set N := {x | ∀ᶠ y in 𝓝 x, y ∈ A → y ∉ U' ∧ y ∉ V'}
  have hbUV : b ∈ U' ∪ V' := by
    obtain ⟨V, hV, hVp⟩ := hbV
    have := isPreconnected_iff_subset_of_disjoint.1 hVp u v hu hv (fun y hy ↦ hcov hy.2)
      (eq_empty_iff_forall_notMem.2 fun y ⟨hy, hyu, hyv⟩ ↦ huv y hy.2 hyu hyv)
    refine this.imp (fun hVu ↦ ?_) fun hVv ↦ ?_ <;> filter_upwards [hV] with y hyV hyA
    exacts [hVu ⟨hyV, hyA⟩, hVv ⟨hyV, hyA⟩]
  have hAUV : A ⊆ U' ∪ V' := by
    refine (isPreconnected_iff_subset_of_disjoint.1 hA _ N
      (isOpen_setOfPred_eventually_nhds.union isOpen_setOfPred_eventually_nhds)
      isOpen_setOfPred_eventually_nhds (fun x hx ↦ ?_) ?_).resolve_right fun hAN ↦ ?_
    · obtain ⟨V, hV, P, Q, hPQ, hP, hQ, hcl⟩ := h x hx
      rcases eventually_mem_or_eventually_not hu hv hcov huv hV hPQ hP hQ hcl with
        hxu | hxv | hxN
      exacts [Or.inl (Or.inl hxu), Or.inl (Or.inr hxv), Or.inr hxN]
    · refine eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxUV, hxN⟩ ↦ ?_
      obtain ⟨h₁, h₂⟩ := hxN.self_of_nhds hx
      exact hxUV.elim h₁ h₂
    · obtain ⟨h₁, h₂⟩ := (hAN hb).self_of_nhds hb
      exact hbUV.elim h₁ h₂
  -- So the two kinds of points separate the whole space, and one of them is empty.
  have hcovX : univ ⊆ U' ∪ V' := fun x _ ↦ by
    by_cases hx : x ∈ A
    · exact hAUV hx
    · refine (hcov hx).imp (fun hxu ↦ ?_) fun hxv ↦ ?_
      · filter_upwards [hu.mem_nhds hxu] with y hy _ using hy
      · filter_upwards [hv.mem_nhds hxv] with y hy _ using hy
  refine (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ U' V'
    isOpen_setOfPred_eventually_nhds isOpen_setOfPred_eventually_nhds hcovX
    (eq_empty_iff_forall_notMem.2 fun x ⟨_, hxu, hxv⟩ ↦ hUV x hxu hxv)).imp
    (fun hU x hx ↦ ?_) fun hV x hx ↦ ?_
  exacts [(hU (mem_univ x)).self_of_nhds hx, (hV (mem_univ x)).self_of_nhds hx]

/-- **Removing a set that separates at most two ways locally, inside a preconnected set.**
Let `U` be a preconnected set and `A ⊆ U` a preconnected set such that each `a ∈ A` has a
neighbourhood `V ⊆ U` within `U` whose part outside `A` is the union of two preconnected sets
`P` and `Q` whose closures both contain `V ∩ A`. If one point `b ∈ A` has a neighbourhood
`V ⊆ U` within `U` with `V \ A` preconnected, then `U \ A` is preconnected.

This is `isPreconnected_compl_of_forall_exists_mem_nhds` in the subspace `U`, so the
neighbourhoods are taken in `U` and `U` need not be open. -/
theorem IsPreconnected.sdiff_of_forall_exists_mem_nhds {U A : Set X} (hUc : IsPreconnected U)
    (hA : IsPreconnected A) (hAU : A ⊆ U) {b : X} (hb : b ∈ A)
    (hbV : ∃ V ∈ 𝓝[U] b, V ⊆ U ∧ IsPreconnected (V \ A))
    (h : ∀ a ∈ A, ∃ V ∈ 𝓝[U] a, V ⊆ U ∧ ∃ P Q : Set X, V \ A = P ∪ Q ∧ IsPreconnected P ∧
      IsPreconnected Q ∧ V ∩ A ⊆ closure P ∩ closure Q) :
    IsPreconnected (U \ A) := by
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  -- Preconnectedness and closures of subsets of `U` read the same in `U` as in `X`.
  have hpre {S : Set X} (hS : S ⊆ U) :
      IsPreconnected ((↑) ⁻¹' S : Set U) ↔ IsPreconnected S := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hS]
  have hcl {S : Set X} (hS : S ⊆ U) : closure ((↑) ⁻¹' S : Set U) = (↑) ⁻¹' closure S := by
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hS]
  have hnhds {x : U} {V : Set X} (hV : V ∈ 𝓝[U] (x : X)) : (↑) ⁻¹' V ∈ 𝓝 x :=
    preimage_coe_mem_nhds_subtype.2 hV
  have hc := isPreconnected_compl_of_forall_exists_mem_nhds (X := U)
    (A := ((↑) : U → X) ⁻¹' A) ((hpre hAU).2 hA) (b := ⟨b, hAU hb⟩) hb ?_ ?_
  · have himage : ((↑) : U → X) '' ((↑) ⁻¹' A)ᶜ = U \ A := by
      rw [image_compl_preimage, Subtype.range_coe]
    exact himage ▸ hc.image _ continuous_subtypeVal.continuousOn
  · obtain ⟨V, hV, hVU, hVc⟩ := hbV
    exact ⟨_, hnhds hV, by rw [← preimage_sdiff]; exact (hpre (sdiff_subset.trans hVU)).2 hVc⟩
  · intro a ha
    obtain ⟨V, hV, hVU, P, Q, hPQ, hP, hQ, hPQcl⟩ := h a ha
    have hPU : P ⊆ U := (hPQ ▸ subset_union_left : P ⊆ V \ A).trans (sdiff_subset.trans hVU)
    have hQU : Q ⊆ U := (hPQ ▸ subset_union_right : Q ⊆ V \ A).trans (sdiff_subset.trans hVU)
    refine ⟨_, hnhds hV, (↑) ⁻¹' P, (↑) ⁻¹' Q, by rw [← preimage_sdiff, hPQ, preimage_union],
      (hpre hPU).2 hP, (hpre hQU).2 hQ, ?_⟩
    rw [hcl hPU, hcl hQU]
    exact fun y hy ↦ hPQcl hy

end
