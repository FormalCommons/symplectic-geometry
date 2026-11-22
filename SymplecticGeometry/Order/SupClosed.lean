/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.CompleteLattice.Finset
public import TauCeti.Order.SupClosed

/-!
# Mayer–Vietoris induction over finite sets of members of an inf-closed family

Tau Ceti's `TauCeti.finset_sup_of_inf_closed` carries a property that holds at `⊥` and on an
inf-closed family `B`, and passes from `U`, `V` and `U ⊓ V` to `U ⊔ V`, to every finite join of
members of `B`, given as a finite set of elements of the lattice. This file states it for a
finite set of elements of `B` itself (`InfClosed.finset_sup_induction`), the form a directed
family indexed by `Finset B` needs. Over a complete lattice, the joins of the finite subsets of
an indexed family form a directed family with the same supremum (`iSup_finset_sup_eq_iSup`).
-/

public section

variable {α : Type*} [DistribLattice α] [OrderBot α] {B : Set α}

/-- A property that holds at `⊥` and on an inf-closed family `B`, and passes from `U`, `V` and
`U ⊓ V` to `U ⊔ V`, holds on the join of every finite set of members of `B`. -/
theorem InfClosed.finset_sup_induction (hB : InfClosed B) (P : α → Prop) (hbot : P ⊥)
    (hbase : ∀ U ∈ B, P U) (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (s : Finset B) : P (s.sup Subtype.val) := by
  classical
  rw [← Function.id_comp Subtype.val, ← Finset.sup_image]
  refine TauCeti.finset_sup_of_inf_closed P hB hbot hbase hsup _ fun _ hV ↦ ?_
  obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hV
  exact W.property

/-- The joins of the finite subsets of an indexed family in a complete lattice have the same
supremum as the family. -/
theorem iSup_finset_sup_eq_iSup {ι β : Type*} [CompleteLattice β] (f : ι → β) :
    ⨆ t : Finset ι, t.sup f = ⨆ i, f i := by
  simp only [Finset.sup_eq_iSup, ← iSup_eq_iSup_finset]

end
