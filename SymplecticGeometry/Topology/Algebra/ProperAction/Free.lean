/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Free proper actions

For a proper action of a topological group `G` on `X` that is free (`IsCancelSMul G X`), the map
`(g, x) ↦ (g • x, x)` is proper and injective, hence a closed embedding. Consequently the element
of `G` carrying one point to another depends continuously on the two points: if `a` and `b` are
continuous on a set `s` and `f y • a y = b y` on `s`, then `f` is continuous on `s`.

The first statement adapts the proof of `isClosedEmbedding_smul_const` (Tau Ceti,
`Topology/Algebra/ProperAction/Orbit.lean`) from a single orbit map to the whole action.

## Main results

* `ProperSMul.isClosedEmbedding_smul_pair`: for a free proper action, `(g, x) ↦ (g • x, x)` is a
  closed embedding.
* `ProperSMul.continuousOn_of_smul_eq`: the acting element between two continuous families of
  points is continuous.

## References

* N. Bourbaki, *General Topology*, Chapters 1–4, Springer, 1989, Chapter III, §4 (proper
  actions).
-/

public section

open Function Topology

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  [ProperSMul G X] [IsCancelSMul G X]

/-- For a free proper action, the map `(g, x) ↦ (g • x, x)` is a closed embedding. -/
@[to_additive /-- For a free proper additive action, the map `(g, x) ↦ (g +ᵥ x, x)` is a closed
embedding. -/]
theorem ProperSMul.isClosedEmbedding_smul_pair :
    IsClosedEmbedding fun gx : G × X ↦ (gx.1 • gx.2, gx.2) :=
  .of_continuous_injective_isClosedMap ProperSMul.isProperMap_smul_pair.continuous
    (fun ⟨g, x⟩ ⟨g', x'⟩ h ↦ by
      obtain ⟨h₁, rfl : x = x'⟩ := Prod.mk.inj h
      rw [IsCancelSMul.right_cancel g g' x h₁])
    ProperSMul.isProperMap_smul_pair.isClosedMap

/-- For a free proper action, the element of `G` carrying `a y` to `b y` is continuous where `a`
and `b` are: if `f y • a y = b y` for `y ∈ s`, and `a` and `b` are continuous on `s`, then so
is `f`. -/
@[to_additive /-- For a free proper additive action, the element of `G` carrying `a y` to `b y` is
continuous where `a` and `b` are: if `f y +ᵥ a y = b y` for `y ∈ s`, and `a` and `b` are
continuous on `s`, then so is `f`. -/]
theorem ProperSMul.continuousOn_of_smul_eq {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    {f : Y → G} {a b : Y → X} (ha : ContinuousOn a s) (hb : ContinuousOn b s)
    (h : ∀ y ∈ s, f y • a y = b y) : ContinuousOn f s := by
  have hpair : ContinuousOn (fun y ↦ (f y, a y)) s :=
    ProperSMul.isClosedEmbedding_smul_pair.isInducing.continuousOn_iff.2 <|
      (hb.prodMk ha).congr fun y hy ↦ by simp [h y hy]
  exact continuous_fst.comp_continuousOn hpair
