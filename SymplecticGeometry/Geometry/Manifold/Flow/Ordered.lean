/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Flow.Ordered

/-!
# Ordered flows: the last field, and inverses

Let `v 0, …, v (k - 1)` be vector fields on a manifold `M` with flows `ψ^(v i)`, and let
`TauCeti.orderedFlowOf v s = ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1))` be Tau Ceti's ordered
flow. Tau Ceti's definition splits off the first field (`TauCeti.orderedFlowOf_succ`); this file
splits off the last one (`TauCeti.orderedFlowOf_castSucc`), and shows that for complete `C¹`
fields the ordered flow of the fields in the reverse order, for the negated times in the reverse
order,

`ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘ ψ^(v 0)_(-s 0)`,

inverts `TauCeti.orderedFlowOf v s` on both sides. This follows from Tau Ceti's inversion of a
single complete flow, `TauCeti.flowOf_flowOf_neg`.

## Main results

* `TauCeti.orderedFlowOf_castSucc`: the ordered flow of `k + 1` fields runs the last field first,
  then the ordered flow of the first `k`.
* `TauCeti.orderedFlowOf_rev_neg_orderedFlowOf`, `TauCeti.orderedFlowOf_orderedFlowOf_rev_neg`:
  the reversed ordered flow with negated times is a left and a right inverse.

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

variable [T2Space M] [BoundarylessManifold I M] [IsManifold I 1 M]

/-- **The reversed ordered flow is a left inverse.** For complete `C¹` vector fields, the ordered
flow of the fields in the reverse order, for the negated times in the reverse order, undoes the
ordered flow: `ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘ ψ^(v 0)_(-s 0) ∘ ψ^(v 0)_(s 0) ∘ ⋯ ∘
ψ^(v (k-1))_(s (k-1)) = id`. -/
theorem orderedFlowOf_rev_neg_orderedFlowOf {k : ℕ} {v : Fin k → (x : M) → TangentSpace I x}
    (hv : ∀ i, CMDiff 1 (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (s : Fin k → ℝ) (x : M) :
    orderedFlowOf (fun i ↦ v i.rev) (fun i ↦ -s i.rev) (orderedFlowOf v s x) = x := by
  induction k with
  | zero => simp only [orderedFlowOf_of_fin_zero, id_eq]
  | succ k ih =>
    rw [orderedFlowOf_castSucc, orderedFlowOf_succ]
    simp only [Function.comp_apply, Fin.rev_castSucc, Fin.rev_last]
    have h := flowOf_flowOf_neg (hv 0) (hc 0) (-s 0) (orderedFlowOf (fun i ↦ v i.succ)
      (fun i ↦ s i.succ) x)
    rw [neg_neg] at h
    rw [h]
    exact ih (fun i ↦ hv i.succ) (fun i ↦ hc i.succ) (fun i ↦ s i.succ)

/-- **The reversed ordered flow is a right inverse.** For complete `C¹` vector fields, the ordered
flow undoes the ordered flow of the fields in the reverse order, for the negated times in the
reverse order: `ψ^(v 0)_(s 0) ∘ ⋯ ∘ ψ^(v (k-1))_(s (k-1)) ∘ ψ^(v (k-1))_(-s (k-1)) ∘ ⋯ ∘
ψ^(v 0)_(-s 0) = id`. -/
theorem orderedFlowOf_orderedFlowOf_rev_neg {k : ℕ} {v : Fin k → (x : M) → TangentSpace I x}
    (hv : ∀ i, CMDiff 1 (fun y ↦ (⟨y, v i y⟩ : TangentBundle I M)))
    (hc : ∀ i, IsCompleteVectorField (v i)) (s : Fin k → ℝ) (x : M) :
    orderedFlowOf v s (orderedFlowOf (fun i ↦ v i.rev) (fun i ↦ -s i.rev) x) = x := by
  simpa only [Fin.rev_rev, neg_neg] using
    orderedFlowOf_rev_neg_orderedFlowOf (v := fun i ↦ v i.rev) (fun i ↦ hv i.rev)
      (fun i ↦ hc i.rev) (fun i ↦ -s i.rev) x

end TauCeti

end
