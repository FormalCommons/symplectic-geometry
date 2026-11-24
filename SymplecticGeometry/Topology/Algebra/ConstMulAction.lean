/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Fixed points of continuous actions on compact spaces

A monoid acting continuously on a compact Hausdorff space has a closed, hence compact, set of
fixed points (`TauCeti.isClosed_fixedPoints_of_continuousConstSMul`). If each fixed point is
isolated among the fixed points, this set is also discrete, so it is finite
(`finite_fixedPoints`).
-/

public section

open Filter Topology

/-- If the fixed points of a continuous action on a compact Hausdorff space are isolated, there
are finitely many of them. -/
theorem finite_fixedPoints {G X : Type*} [Monoid G] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    (hiso : ∀ p ∈ MulAction.fixedPoints G X, ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints G X) :
    (MulAction.fixedPoints G X).Finite :=
  TauCeti.isClosed_fixedPoints_of_continuousConstSMul.isCompact.finite <|
    isDiscrete_iff_nhdsNE.2 fun p hp ↦ inf_principal_eq_bot.2 (hiso p hp)

end
