/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions

/-!
# Discreteness of stabilizers along an orbit

For a group `G` with continuous multiplication acting on a type `α`, the stabilizers of `a` and
of `g • a` are conjugate in `G`, so one of them is discrete, for the subspace topology, exactly
when the other is. The Kempf–Ness theory uses this to see that stability, which asks for a
discrete stabilizer, holds along whole orbits.

## Main results

* `MulAction.discreteTopology_stabilizer_smul_iff`: the stabilizer of `g • a` is discrete exactly
  when that of `a` is.
-/

public section

open MulAction in
/-- The stabilizers of `a` and `g • a` are conjugate, so one is discrete exactly when the other
is. -/
theorem MulAction.discreteTopology_stabilizer_smul_iff {G α : Type*} [Group G]
    [TopologicalSpace G] [ContinuousMul G] [MulAction G α] (g : G) (a : α) :
    DiscreteTopology (stabilizer G (g • a)) ↔ DiscreteTopology (stabilizer G a) := by
  -- Conjugation by `g⁻¹` sends the stabilizer of `g • b` continuously and injectively into that
  -- of `b`.
  have key : ∀ (g : G) (b : α), DiscreteTopology (stabilizer G b) →
      DiscreteTopology (stabilizer G (g • b)) := fun g b _ ↦
    DiscreteTopology.of_continuous_injective
      (f := fun x : stabilizer G (g • b) ↦ (⟨g⁻¹ * x * g, by
        rw [mem_stabilizer_iff, mul_smul, mul_smul, x.property, inv_smul_smul]⟩ : stabilizer G b))
      (by fun_prop)
      fun x y h ↦ Subtype.ext <| by simpa using congrArg Subtype.val h
  refine ⟨fun h ↦ ?_, key g a⟩
  have := key g⁻¹ (g • a) h
  rwa [inv_smul_smul] at this

end
