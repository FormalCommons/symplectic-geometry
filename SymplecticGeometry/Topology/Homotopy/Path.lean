/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Path

/-!
# Homotopies of loops with fixed and with free base point

Two loops `γ γ' : Path x x` that are homotopic with fixed ends (`Path.Homotopic`) are also
homotopic through loops, the base point being allowed to move:
`(γ : C(I, X)).HomotopicWith γ' fun p ↦ p 0 = p 1`. This is the easy half of the comparison
between based and free homotopy classes of loops; Tau Ceti's
`Path.exists_trans_homotopic_trans_of_homotopicWith` and `Path.homotopicWith_trans_trans_symm`
give the rest.

## Main results

* `Path.Homotopic.homotopicWith`: a homotopy with fixed ends is a homotopy through loops.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 (homotopy of loops in the homotopy axiom of Theorem 2.2.12).
-/

public section

open scoped unitInterval

namespace Path.Homotopic

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Loops at `x` that are homotopic with fixed ends are homotopic through loops: a homotopy
relative to the ends keeps every intermediate map closed. -/
theorem homotopicWith {γ γ' : Path x x} (h : γ.Homotopic γ') :
    (γ : C(I, X)).HomotopicWith (γ' : C(I, X)) fun p ↦ p 0 = p 1 := by
  obtain ⟨F⟩ := h
  exact ⟨{ toHomotopy := F.toHomotopy, prop' := fun s ↦ by simp }⟩

end Path.Homotopic

end
