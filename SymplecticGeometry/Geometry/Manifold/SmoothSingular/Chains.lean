/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Chains

/-!
# Integration cochains of finite sums of forms

Tau Ceti's integration cochain `TauCeti.integrationCochain φ` integrates a form `φ` over smooth
singular chains. Tau Ceti proves that it is additive on continuous forms
(`TauCeti.integrationCochain_add`). This file extends that to finite sums: the integration cochain
of a finite sum of continuous forms is the sum of their integration cochains
(`TauCeti.integrationCochain_sum`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 18.
-/

public section

open CategoryTheory

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {R : Type} [Ring R]
  [Module R F] {p : ℕ}

/-- Integration takes a finite sum of continuous forms to the sum of their integration
cochains. -/
theorem integrationCochain_sum {ι : Type*} (φ : ι → RoughForm I M F p) (s : Finset ι)
    (hφ : ∀ i ∈ s, IsSmoothForm I 0 (φ i)) :
    integrationCochain (R := R) (∑ i ∈ s, φ i) = ∑ i ∈ s, integrationCochain (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, integrationCochain_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, integrationCochain_add
      (hφ i (Finset.mem_insert_self i s))
      (IsSmoothForm.sum _ _ fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj)]

end TauCeti

end
