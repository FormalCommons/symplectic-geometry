/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
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
  -- `MulAction.stabilizerEquivStabilizer` maps the stabilizer of `b` into that of `c = h • b` by
  -- a conjugation, which is injective and continuous.
  have key {h : G} {b c : α} (hb : c = h • b) [DiscreteTopology (stabilizer G c)] :
      DiscreteTopology (stabilizer G b) :=
    .of_continuous_injective (continuous_induced_rng.2 <| by
      simp_rw [Function.comp_def, stabilizerEquivStabilizer_apply, MulAut.conj_apply]; fun_prop)
      (stabilizerEquivStabilizer hb).injective
  exact ⟨fun _ ↦ key (h := g) rfl, fun _ ↦ key (inv_smul_smul g a).symm⟩

end
