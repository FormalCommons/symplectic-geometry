/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuity of functions on `Fin 1 → α`

A point of `Fin 1 → α` is the one-entry vector `![x 0]` of its only coordinate, and
`Homeomorph.funUnique` identifies `Fin 1 → α` with `α`. So a function `f` on `Fin 1 → α` is
continuous at `x` exactly when the function of one variable `t ↦ f ![t]` is continuous at `x 0`.

## Main results

* `continuousAt_iff_continuousAt_vecCons_fin_one`: continuity at a point.
-/

public section

/-- A function `f` on `Fin 1 → α` is continuous at `x` exactly when `t ↦ f ![t]` is continuous
at `x 0`. -/
theorem continuousAt_iff_continuousAt_vecCons_fin_one {α X : Type*} [TopologicalSpace α]
    [TopologicalSpace X] {f : (Fin 1 → α) → X} {x : Fin 1 → α} :
    ContinuousAt f x ↔ ContinuousAt (fun t ↦ f ![t]) (x 0) := by
  conv_lhs => rw [← show ![x 0] = x from FinVec.etaExpand_eq x]
  simp only [Matrix.vec_single_eq_const]
  exact ((Homeomorph.funUnique (Fin 1) α).symm.comp_continuousAt_iff' f (x 0)).symm

end
