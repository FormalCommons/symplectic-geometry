/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Suprema over finsets of finite infima

Two identities for suprema indexed by a finset `s` of finsets, of the infima
`⨅ i ∈ a, f i` over its members:

* `Finset.sup_iSup_erase`: splitting off one member `a ∈ s` of an indexed supremum;
* `Finset.iSup_image_union_iInf`: in a frame, the infimum over `a` distributes over the
  supremum over `t`, and gives the supremum over the unions `a ∪ b`, `b ∈ t`.

These are the identities of open sets behind a Mayer–Vietoris induction over the finite
intersections of a cover.
-/

public section

namespace Finset

variable {α ι : Type*}

/-- An indexed supremum over a finset is the join of the term at a member `a` and the supremum
over the rest. -/
theorem sup_iSup_erase [CompleteLattice α] [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∈ s)
    (f : ι → α) : f a ⊔ ⨆ b ∈ s.erase a, f b = ⨆ b ∈ s, f b := by
  conv_rhs => rw [← insert_erase ha, iSup_insert]

/-- In a frame, the supremum of the infima `⨅ i ∈ c, f i` over the unions `c = a ∪ b`, `b ∈ t`,
is the meet of `⨅ i ∈ a, f i` with the supremum of the infima over `t`. -/
theorem iSup_image_union_iInf [Order.Frame α] [DecidableEq ι] (f : ι → α) (a : Finset ι)
    (t : Finset (Finset ι)) :
    ⨆ c ∈ t.image (a ∪ ·), ⨅ i ∈ c, f i = (⨅ i ∈ a, f i) ⊓ ⨆ b ∈ t, ⨅ i ∈ b, f i := by
  rw [inf_iSup₂_eq, iSup_finset_image]
  simp only [iInf_union]

end Finset

end
