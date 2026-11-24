/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Proper actions on invariant subsets

Complements to Mathlib's `Mathlib/Topology/Algebra/ProperAction/Basic.lean` and Tau Ceti's
`TauCeti/Topology/Algebra/ProperAction/Basic.lean`.

* `SubMulAction.properSMul`, `SubAddAction.properVAdd`: a proper action of a group `G` on `X`
  restricts to a proper action on every `G`-invariant subset of `X`, with the subspace topology.

The instance is Tau Ceti's `Topology.IsEmbedding.properSMul` for the inclusion of the subset, as
in the proof of Tau Ceti's
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.properSMul_levelSubMulAction`, here for the whole
group rather than a stabilizer. It sits beside Mathlib's `SubMulAction.continuousConstSMul`.

## References

* N. Bourbaki, *General Topology*, Chapters 1–4, Springer, 1989, Chapter III, §4.
-/

public section

/-- **A proper action restricts to invariant subsets.** If a group `G` acts properly on `X`, then
it acts properly on every `G`-invariant subset `S` of `X`, with the subspace topology. -/
@[to_additive /-- If a group `G` acts properly additively on `X`, then it acts properly on every
`G`-invariant subset `S` of `X`, with the subspace topology. -/]
instance SubMulAction.properSMul {G X : Type*} [Group G] [TopologicalSpace G] [MulAction G X]
    [TopologicalSpace X] [ProperSMul G X] (S : SubMulAction G X) : ProperSMul G S :=
  Topology.IsEmbedding.subtypeVal.properSMul fun g x ↦ SubMulAction.val_smul g x

end
