/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Time changes of a flow that vary from point to point

Let `φ` be a flow of `ℝ` on a topological space `M` and `τ : M → ℝ`. The time change
`x ↦ φ (τ x) x` moves each point along its own orbit for the time `τ x`. Along the orbit of `x`
it acts through the reparametrization `s ↦ s + τ (φ s x)` of the time. This file gives the
topological facts about it that need no smooth structure:

* if `τ` is continuous and bounded, each reparametrization is onto `ℝ`, by the intermediate value
  theorem;
* if each reparametrization is a bijection of `ℝ`, the time change is a bijection of `M`. If two
  points `a`, `b` have the same image, then `b = φ s a` for `s = τ a - τ b`, and the
  reparametrization along the orbit of `a` takes the value `τ a` at `s` and at `0`, so `s = 0`.
  No case split on periodic orbits or rest points is needed.

This time change varies the time from point to point; it differs from Tau Ceti's
`Flow.timeChange`, which multiplies the time by a constant. The smooth case, where `τ` is
differentiable along the flow of a complete vector field and `1 + dτ(v) > 0`, is in
`SymplecticGeometry/Geometry/Manifold/Flow/TimeChange.lean`.

## Main results

* `Flow.surjective_add_apply`: for continuous bounded `τ`, the reparametrization
  `s ↦ s + τ (φ s x)` of an orbit is onto `ℝ`.
* `Flow.bijective_apply_self`: the time change `x ↦ φ (τ x) x` is bijective if each
  reparametrization `s ↦ s + τ (φ s x)` is.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorem 3.1 (moving sublevels along the flow of a rescaled gradient field).
-/

public section

open Set Function

namespace Flow

variable {M : Type*} [TopologicalSpace M] (ϕ : Flow ℝ M) {τ : M → ℝ}

/-- If `τ` is continuous and bounded, the reparametrization `s ↦ s + τ (ϕ s x)` of the orbit of
`x` is onto `ℝ`. -/
theorem surjective_add_apply (hτ : Continuous τ) (hτb : Bornology.IsBounded (range τ)) (x : M) :
    Surjective (fun s ↦ s + τ (ϕ s x)) := by
  obtain ⟨C, hC⟩ := hτb.subset_closedBall 0
  have hle (y : M) : |τ y| ≤ C := by
    simpa [Real.dist_0_eq_abs] using hC (mem_range_self y)
  intro r
  have hcont : Continuous (fun s ↦ s + τ (ϕ s x)) :=
    continuous_id.add (hτ.comp (ϕ.continuous continuous_id continuous_const))
  refine intermediate_value_univ (r - C) (r + C) hcont ⟨?_, ?_⟩
  · linarith [(abs_le.1 (hle (ϕ (r - C) x))).2]
  · linarith [(abs_le.1 (hle (ϕ (r + C) x))).1]

/-- If the reparametrization `s ↦ s + τ (ϕ s x)` of every orbit is a bijection of `ℝ`, then the
time change `x ↦ ϕ (τ x) x` is a bijection of `M`. -/
theorem bijective_apply_self (hinj : ∀ x, Injective (fun s ↦ s + τ (ϕ s x)))
    (hsurj : ∀ x, Surjective (fun s ↦ s + τ (ϕ s x))) : Bijective (fun x ↦ ϕ (τ x) x) := by
  refine ⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩
  · -- `b` lies on the orbit of `a`, at time `s = τ a - τ b`.
    have hb : b = ϕ (τ a - τ b) a := by
      rw [sub_eq_neg_add, Flow.map_add, ← show ϕ (τ b) b = ϕ (τ a) a from hab.symm,
        ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    have hs : τ a - τ b = 0 := by
      refine hinj a ?_
      simp only [← hb, Flow.map_zero_apply]
      ring
    rw [hb, hs, Flow.map_zero_apply]
  · obtain ⟨t, ht⟩ := hsurj y 0
    refine ⟨ϕ t y, ?_⟩
    simp only at ht ⊢
    rw [← Flow.map_add, add_comm, ht, Flow.map_zero_apply]

end Flow

end
