/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Uniform
import SymplecticGeometry.Topology.Compactness.Compact

/-!
# Uniform smallness on a compact set is an open condition

For jointly continuous maps `f g : Λ × X → E` into a seminormed group and a compact `T ⊆ X`,
the parameters `l` with `‖f (l, x) - g (l, x)‖ < ε` for every `x ∈ T` form an open set
(`IsCompact.isOpen_setOfPred_forall_norm_sub_lt`). This is the tube lemma
`IsCompact.isOpen_setOfPred_forall_prodMk_mem`, applied to the open set of the points `(l, x)` at
which the strict inequality holds.

## Main results

* `IsCompact.isOpen_setOfPred_forall_norm_sub_lt`: the set of parameters at which two jointly
  continuous maps are uniformly `ε`-close on a compact set is open.
-/

public section

variable {Λ X E : Type*} [TopologicalSpace Λ] [TopologicalSpace X] [SeminormedAddCommGroup E]

/-- For jointly continuous `f g : Λ × X → E` and a compact `T ⊆ X`, the set of `l` with
`‖f (l, x) - g (l, x)‖ < ε` for every `x ∈ T` is open. -/
theorem IsCompact.isOpen_setOfPred_forall_norm_sub_lt {T : Set X} (hT : IsCompact T)
    {f g : Λ × X → E} (hf : Continuous f) (hg : Continuous g) (ε : ℝ) :
    IsOpen {l | ∀ x ∈ T, ‖f (l, x) - g (l, x)‖ < ε} :=
  hT.isOpen_setOfPred_forall_prodMk_mem (W := {p | ‖f p - g p‖ < ε})
    (isOpen_lt (hf.sub hg).norm continuous_const)

end
