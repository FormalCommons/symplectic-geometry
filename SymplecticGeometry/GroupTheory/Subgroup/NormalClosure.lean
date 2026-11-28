/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Normal closures of termwise conjugate families

Replacing each member of a family of elements of a group by a conjugate of it does not change the
normal closure of the family (`Subgroup.normalClosure_range_eq_of_isConj`). This is the version for
families of Tau Ceti's `IsConj.normalClosure_singleton_eq`, and its proof is the same: conjugate
elements have the same set of conjugates. Likewise, replacing each member of a family of sets by
one with the same normal closure does not change the normal closure of the union
(`Subgroup.normalClosure_iUnion_congr`).

## Main results

* `Subgroup.normalClosure_range_eq_of_isConj`: if `a i` is conjugate to `b i` for every `i`, then
  the ranges of `a` and `b` have the same normal closure.
* `Subgroup.normalClosure_iUnion_congr`: if `s i` and `t i` have the same normal closure for every
  `i`, then so do the unions of the `s i` and of the `t i`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- Two families of elements of a group that are termwise conjugate normally generate the same
subgroup. -/
theorem normalClosure_range_eq_of_isConj {ι : Sort*} {a b : ι → G}
    (h : ∀ i, IsConj (a i) (b i)) :
    normalClosure (Set.range a) = normalClosure (Set.range b) := by
  simp only [normalClosure, Group.conjugatesOfSet, Set.biUnion_range, (h _).conjugatesOf_eq]

/-- If the sets `s i` and `t i` of a group have the same normal closure for every `i`, then so do
their unions. -/
theorem normalClosure_iUnion_congr {ι : Sort*} {s t : ι → Set G}
    (h : ∀ i, normalClosure (s i) = normalClosure (t i)) :
    normalClosure (⋃ i, s i) = normalClosure (⋃ i, t i) := by
  have key {s t : ι → Set G} (h : ∀ i, normalClosure (s i) = normalClosure (t i)) :
      normalClosure (⋃ i, s i) ≤ normalClosure (⋃ i, t i) :=
    normalClosure_le_normal <| Set.iUnion_subset fun i ↦ subset_normalClosure.trans <|
      (h i).le.trans (normalClosure_mono (Set.subset_iUnion t i))
  exact le_antisymm (key h) (key fun i ↦ (h i).symm)

end Subgroup

end
