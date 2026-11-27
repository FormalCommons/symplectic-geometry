/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Uniform smallness on a compact set is an open condition

For jointly continuous maps `f g : Λ × X → E` into a seminormed group and a compact `T ⊆ X`,
the parameters `l` with `‖f (l, x) - g (l, x)‖ < ε` for every `x ∈ T` form an open set
(`IsCompact.isOpen_setOf_forall_norm_sub_lt`). This is Mathlib's
`IsCompact.eventually_forall_of_forall_eventually`, applied to the strict inequality, which holds
near every point `(l, x)` with `x ∈ T` where it holds.

## Main results

* `IsCompact.isOpen_setOf_forall_norm_sub_lt`: the set of parameters at which two jointly
  continuous maps are uniformly `ε`-close on a compact set is open.
-/

public section

open Filter Topology

variable {Λ X E : Type*} [TopologicalSpace Λ] [TopologicalSpace X] [SeminormedAddCommGroup E]

/-- For jointly continuous `f g : Λ × X → E` and a compact `T ⊆ X`, the set of `l` with
`‖f (l, x) - g (l, x)‖ < ε` for every `x ∈ T` is open. -/
theorem IsCompact.isOpen_setOf_forall_norm_sub_lt {T : Set X} (hT : IsCompact T)
    {f g : Λ × X → E} (hf : Continuous f) (hg : Continuous g) (ε : ℝ) :
    IsOpen {l | ∀ x ∈ T, ‖f (l, x) - g (l, x)‖ < ε} :=
  isOpen_iff_eventually.2 fun l hl ↦ hT.eventually_forall_of_forall_eventually fun x hx ↦
    ((hf.sub hg).norm.tendsto (l, x)).eventually (gt_mem_nhds (hl x hx))

end
