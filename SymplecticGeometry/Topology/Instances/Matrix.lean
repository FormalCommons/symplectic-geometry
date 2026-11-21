/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.Matrix

/-!
# Topological facts about matrices

This file complements Mathlib's `Mathlib.Topology.Instances.Matrix`.

## Main results

* `Continuous.isOpen_setOf_isUnit_det`: for a continuous family `f` of square matrices over a
  topological field in which points are closed, the parameters `x` at which `f x` is invertible
  form an open set.

## References

This is standard point-set topology; the file follows no source beyond Mathlib's API.
-/

public section

/-- For a continuous family `f` of square matrices over a topological field whose points are
closed, the set of parameters `x` at which the determinant of `f x` is a unit, that is, at which
`f x` is invertible, is open. -/
theorem Continuous.isOpen_setOf_isUnit_det {X K n : Type*} [TopologicalSpace X] [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [T1Space K] [Fintype n] [DecidableEq n]
    {f : X → Matrix n n K} (hf : Continuous f) : IsOpen {x | IsUnit (f x).det} := by
  simp only [isUnit_iff_ne_zero]
  exact isOpen_ne_fun hf.matrix_det continuous_const

end
