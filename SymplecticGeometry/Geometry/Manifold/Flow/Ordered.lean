/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Ordered

/-!
# Ordered flows: the last field

Let `v 0, …, v (k - 1)` be vector fields on a manifold `M` with flows `ψ^(v i)`, and let
`TauCeti.orderedFlowOf v s = ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))` be Tau Ceti's ordered
flow. Tau Ceti's definition splits off the first field (`TauCeti.orderedFlowOf_succ`); this file
splits off the last one. Tau Ceti's `TauCeti.orderedFlowOf_rev_neg_orderedFlowOf` and
`TauCeti.orderedFlowOf_orderedFlowOf_rev_neg` invert an ordered flow of complete fields.

## Main results

* `TauCeti.orderedFlowOf_castSucc`: the ordered flow of `k + 1` fields runs the last field first,
  then the ordered flow of the first `k`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §10.2
  (the proof of Theorem 10.2.5).
-/

public section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The ordered flow of `k + 1` fields runs the last field first and then the ordered flow of the
first `k` fields: `orderedFlowOf v s = orderedFlowOf (v ∘ castSucc) (s ∘ castSucc) ∘
ψ^(v k)_(s k)`. -/
theorem orderedFlowOf_castSucc {k : ℕ} (v : Fin (k + 1) → (x : M) → TangentSpace I x)
    (s : Fin (k + 1) → ℝ) :
    orderedFlowOf v s =
      orderedFlowOf (fun i ↦ v i.castSucc) (fun i ↦ s i.castSucc) ∘
        flowOf (v (Fin.last k)) (s (Fin.last k)) := by
  induction k with
  | zero =>
    rw [orderedFlowOf_succ, orderedFlowOf_of_fin_zero, orderedFlowOf_of_fin_zero,
      Function.comp_id, Function.id_comp, Fin.last_zero]
  | succ k ih =>
    rw [orderedFlowOf_succ, ih, orderedFlowOf_succ (fun i ↦ v i.castSucc)]
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero, Function.comp_assoc]

end TauCeti

end
