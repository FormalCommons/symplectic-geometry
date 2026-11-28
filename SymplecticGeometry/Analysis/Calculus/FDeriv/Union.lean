/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Gluing derivatives on two relatively closed sets

Mathlib's `HasFDerivWithinAt.union` glues derivatives within `s` and within `t` at a point that
lies in both sets. Here the point need lie only in `s ∪ t`, provided each of `s` and `t` is
closed relative to `s ∪ t`: at a point of the union outside `s`, it then lies outside the closure
of `s`, where `HasFDerivWithinAt.of_notMem_closure` gives the derivative within `s` for free.
The proof is that of `ContinuousOn.union_of_closure_inter_subset`, itself adapted from Mathlib's
`ContinuousOn.union_of_isClosed`. Tau Ceti's `TauCeti.hasFDerivAt_of_isClosed_of_union_eq_univ`
does the same for two closed sets that cover the whole space.

## Main results

* `HasFDerivWithinAt.union_of_closure_inter_subset`: the gluing at a point of `s ∪ t`.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {f : E → F}
  {f' : E →L[𝕜] F} {x : E} {s t : Set E}

/-- Let `x ∈ s ∪ t`, where `closure s ∩ t ⊆ s` and `closure t ∩ s ⊆ t`. If `f` has derivative
`f'` within `s` at `x` when `x ∈ s`, and within `t` at `x` when `x ∈ t`, then it has derivative
`f'` within `s ∪ t` at `x`. -/
theorem HasFDerivWithinAt.union_of_closure_inter_subset (hs : x ∈ s → HasFDerivWithinAt f f' s x)
    (ht : x ∈ t → HasFDerivWithinAt f f' t x) (hst : closure s ∩ t ⊆ s)
    (hts : closure t ∩ s ⊆ t) (hx : x ∈ s ∪ t) : HasFDerivWithinAt f f' (s ∪ t) x := by
  classical
  refine .union ?_ ?_
  · exact if h : x ∈ s then hs h else .of_notMem_closure
      fun hc ↦ h (hst ⟨hc, hx.resolve_left h⟩)
  · exact if h : x ∈ t then ht h else .of_notMem_closure
      fun hc ↦ h (hts ⟨hc, hx.resolve_right h⟩)

end
