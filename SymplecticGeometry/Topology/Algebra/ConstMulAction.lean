/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Topology.Algebra.ConstMulAction
public import SymplecticGeometry.Topology.DiscreteSubset

/-!
# Fixed points of continuous actions on compact spaces

A monoid acting continuously on a compact Hausdorff space has a closed, hence compact, set of
fixed points (`TauCeti.isClosed_fixedPoints_of_continuousConstSMul`). If each fixed point is
isolated among the fixed points, this set is finite (`finite_fixedPoints`), by
`IsClosed.finite_inter_of_forall_eventually_notMem` applied with the whole space as the compact
set.
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

end
