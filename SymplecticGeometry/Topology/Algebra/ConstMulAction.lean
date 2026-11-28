/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import SymplecticGeometry.Topology.DiscreteSubset

/-!
# Continuous actions by constants: fixed points and affine maps

A monoid acting continuously on a compact Hausdorff space has a closed, hence compact, set of
fixed points (`TauCeti.isClosed_fixedPoints_of_continuousConstSMul`). If each fixed point is
isolated among the fixed points, this set is finite (`finite_fixedPoints`), by
`IsClosed.finite_inter_of_forall_eventually_notMem` applied with the whole space as the compact
set.

For `c ≠ 0` in a group with zero acting continuously on a topological additive group, the map
`y ↦ q + c • (y - p)` is an open embedding (`isOpenEmbedding_add_smul_sub`), as the composite of
Mathlib's homeomorphisms `Homeomorph.subRight`, `Homeomorph.smulOfNeZero` and
`Homeomorph.addLeft`.
-/

public section

open Filter Topology

/-- If the fixed points of a continuous action on a compact Hausdorff space are isolated, there
are finitely many of them. -/
theorem finite_fixedPoints {G X : Type*} [Monoid G] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    (hiso : ∀ p ∈ MulAction.fixedPoints G X, ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints G X) :
    (MulAction.fixedPoints G X).Finite :=
  by simpa using TauCeti.isClosed_fixedPoints_of_continuousConstSMul
    |>.finite_inter_of_forall_eventually_notMem isCompact_univ (by simpa using hiso)

/-- For `c ≠ 0`, the map `y ↦ q + c • (y - p)` of a topological additive group, on which a group
with zero acts continuously, is an open embedding. -/
theorem isOpenEmbedding_add_smul_sub {G₀ α : Type*} [GroupWithZero G₀] [AddGroup α]
    [MulAction G₀ α] [TopologicalSpace α] [IsTopologicalAddGroup α] [ContinuousConstSMul G₀ α]
    {c : G₀} (hc : c ≠ 0) (q p : α) : IsOpenEmbedding fun y ↦ q + c • (y - p) :=
  ((Homeomorph.subRight p).trans
    ((Homeomorph.smulOfNeZero c hc).trans (Homeomorph.addLeft q))).isOpenEmbedding

end
