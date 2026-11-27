/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Normal closures of termwise conjugate families, and along surjections

Replacing each member of a family of elements of a group by a conjugate of it does not change the
normal closure of the family (`Subgroup.normalClosure_range_eq_of_isConj`). This is the version for
families of Tau Ceti's `IsConj.normalClosure_singleton_eq`, and its proof is the same: conjugate
elements have the same set of conjugates.

The preimage under a surjective homomorphism `f` of the normal closure of `f '' s` is the normal
closure of `s` together with the kernel of `f`, so it is the normal closure of `s` when the kernel
lies in it (`Subgroup.comap_normalClosure_image_of_ker_le`).

## Main results

* `Subgroup.normalClosure_range_eq_of_isConj`: if `a i` is conjugate to `b i` for every `i`, then
  the ranges of `a` and `b` have the same normal closure.
* `Subgroup.comap_normalClosure_image_of_ker_le`: for a surjective `f` whose kernel lies in the
  normal closure of `s`, the preimage of the normal closure of `f '' s` is that of `s`.
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

/-- Let `f : G →* N` be surjective, with kernel in the normal closure of `s`. Then the preimage
under `f` of the normal closure of `f '' s` is the normal closure of `s`. -/
theorem comap_normalClosure_image_of_ker_le {N : Type*} [Group N] {f : G →* N}
    (hf : Function.Surjective f) {s : Set G} (h : f.ker ≤ normalClosure s) :
    (normalClosure (f '' s)).comap f = normalClosure s := by
  rw [← map_normalClosure s f hf, comap_map_eq, sup_of_le_left h]

end Subgroup

end
