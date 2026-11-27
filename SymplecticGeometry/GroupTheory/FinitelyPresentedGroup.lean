/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Data.Set.Finite.Lemmas
import TauCeti.GroupTheory.Presentation.Tietze

/-!
# Presentations of finitely presented groups with a nonempty set of generators

Mathlib's `Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup` gives every finitely
presented group a presentation by finitely many generators and a finite set of relators, but
the number of generators may be zero. Some constructions need at least one generator: in Gompf's
realization of a finitely presented group as the fundamental group of a closed symplectic
four-manifold, the generators become the handles of a closed surface, whose genus should be
positive. Adjoining one generator together with the trivial word as its defining word (Tau
Ceti's Tietze move `PresentedGroup.adjoinGenerators`) does not change the presented group, so
such a presentation always exists.

## Main results

* `Group.IsFinitelyPresented.exists_one_le_mulEquiv_presentedGroup`: a finitely presented group
  is presented by `g ≥ 1` generators and finitely many relators `w : Fin r → FreeGroup (Fin g)`.

## References

* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995]
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.2.8
-/

public section

namespace Group.IsFinitelyPresented

/-- A finitely presented group has a presentation with at least one generator: there are
`g ≥ 1` and finitely many relators `w : Fin r → FreeGroup (Fin g)` such that `G` is isomorphic
to the group they present. -/
theorem exists_one_le_mulEquiv_presentedGroup (G : Type*) [Group G] [IsFinitelyPresented G] :
    ∃ g r : ℕ, 1 ≤ g ∧ ∃ w : Fin r → FreeGroup (Fin g),
      Nonempty (G ≃* PresentedGroup (Set.range w)) := by
  obtain ⟨n, s, hs, ⟨φ⟩⟩ := exists_mulEquiv_presentedGroup (G := G)
  -- adjoin one generator, with the trivial word as its defining word
  let ψ := PresentedGroup.adjoinGenerators (fun _ : Unit ↦ (1 : FreeGroup (Fin n))) s
  let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
  set t := FreeGroup.freeGroupCongr e ''
    (Set.range (fun b : Unit ↦ FreeGroup.of (Sum.inr b) *
      (FreeGroup.map Sum.inl (1 : FreeGroup (Fin n)))⁻¹) ∪ FreeGroup.map Sum.inl '' s)
  have ht : t.Finite := ((Set.finite_range _).union (hs.image _)).image _
  obtain ⟨r, w, -, hw⟩ := ht.fin_param
  exact ⟨n + 1, r, Nat.le_add_left 1 n, w,
    ⟨(φ.trans ψ).trans ((PresentedGroup.equivPresentedGroup _ e).trans
      (PresentedGroup.equivOfNormalClosureEq (congrArg _ hw.symm)))⟩⟩

end Group.IsFinitelyPresented

end
