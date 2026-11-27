/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.ODE.Linear

/-!
# Stable subspaces under a change of coordinates

A continuous linear equivalence `e : X ≃L[ℝ] Y` conjugates the flow `exp (t • A)` of an operator
`A` on `X` to the flow of `e A e⁻¹` on `Y`. So it carries Tau Ceti's stable subspace
`ContinuousLinearMap.stableSubspace` of `A` onto that of `e A e⁻¹`.

## Main results

* `ContinuousLinearEquiv.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff`: `e v` is stable
  for `e A e⁻¹` if and only if `v` is stable for `A`.
* `ContinuousLinearEquiv.stableSubspace_conjContinuousAlgEquiv`: the stable subspace of
  `e A e⁻¹` is the image under `e` of that of `A`.
-/

public section

open Filter NormedSpace

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [CompleteSpace X] [CompleteSpace Y]

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence `e` conjugates the flow of `A` to that of `e A e⁻¹`, so `e v`
is stable for `e A e⁻¹` if and only if `v` is stable for `A`. -/
theorem apply_mem_stableSubspace_conjContinuousAlgEquiv_iff (e : X ≃L[ℝ] Y) {A : X →L[ℝ] X}
    {v : X} : e v ∈ (e.conjContinuousAlgEquiv A).stableSubspace ↔ v ∈ A.stableSubspace := by
  have hexp (t : ℝ) : exp (t • e.conjContinuousAlgEquiv A) (e v) = e (exp (t • A) v) := by
    have hA : t • e.conjContinuousAlgEquiv A = e.conjContinuousAlgEquiv (t • A) := by
      ext x
      simp
    rw [hA, ← map_exp_of_mem_ball (𝕂 := ℝ) _ e.conjContinuousAlgEquiv.continuous _
      ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _),
      conjContinuousAlgEquiv_apply_apply, symm_apply_apply]
  simp only [ContinuousLinearMap.mem_stableSubspace, hexp]
  simpa [Function.comp_def] using (e.toHomeomorph.isInducing.tendsto_nhds_iff
    (f := fun t : ℝ ↦ exp (t • A) v) (l := atTop) (y := 0)).symm

/-- The stable subspace of `e A e⁻¹` is the image under `e` of the stable subspace of `A`. -/
theorem stableSubspace_conjContinuousAlgEquiv (e : X ≃L[ℝ] Y) (A : X →L[ℝ] X) :
    (e.conjContinuousAlgEquiv A).stableSubspace = A.stableSubspace.map (e : X →ₗ[ℝ] Y) := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  rw [e.apply_mem_stableSubspace_conjContinuousAlgEquiv_iff]
  simp

end ContinuousLinearEquiv

end
