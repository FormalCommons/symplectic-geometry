/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Quaternion

/-!
# Pure quaternions from vectors of `ℝ³`

A vector `u` of the Euclidean space `ℝ³` gives the pure quaternion `u₀ i + u₁ j + u₂ k`. This map
is a linear isometry onto the pure quaternions, and the square of the pure quaternion of `u` is
`-‖u‖²`; in particular the pure quaternion of a unit vector squares to `-1`.

## Main definitions

* `Quaternion.pureOfEuclideanSpace`: the linear isometry `u ↦ u₀ i + u₁ j + u₂ k` from
  `EuclideanSpace ℝ (Fin 3)` to `ℍ[ℝ]`.

## Main results

* `Quaternion.pureOfEuclideanSpace_mul_self`: the pure quaternion of `u` squares to `-‖u‖²`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace Quaternion

/-- The pure quaternion `u₀ i + u₁ j + u₂ k` of a vector `u` of `ℝ³`, as a linear isometry from
`EuclideanSpace ℝ (Fin 3)` to `ℍ[ℝ]`. -/
noncomputable def pureOfEuclideanSpace : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] ℍ[ℝ] where
  toFun u := ⟨0, u 0, u 1, u 2⟩
  map_add' u v := by ext <;> simp
  map_smul' c u := by ext <;> simp
  norm_map' u := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [sq, ← normSq_eq_norm_mul_self, normSq_def', EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_three]
    simp

/-- The pure quaternion of `u` is `0 + u₀ i + u₁ j + u₂ k`. -/
@[simp]
theorem pureOfEuclideanSpace_apply (u : EuclideanSpace ℝ (Fin 3)) :
    pureOfEuclideanSpace u = ⟨0, u 0, u 1, u 2⟩ :=
  (rfl)

@[simp]
theorem re_pureOfEuclideanSpace (u : EuclideanSpace ℝ (Fin 3)) :
    (pureOfEuclideanSpace u).re = 0 :=
  (rfl)

@[simp]
theorem imI_pureOfEuclideanSpace (u : EuclideanSpace ℝ (Fin 3)) :
    (pureOfEuclideanSpace u).imI = u 0 :=
  (rfl)

@[simp]
theorem imJ_pureOfEuclideanSpace (u : EuclideanSpace ℝ (Fin 3)) :
    (pureOfEuclideanSpace u).imJ = u 1 :=
  (rfl)

@[simp]
theorem imK_pureOfEuclideanSpace (u : EuclideanSpace ℝ (Fin 3)) :
    (pureOfEuclideanSpace u).imK = u 2 :=
  (rfl)

/-- The pure quaternion of `u` squares to `-‖u‖²`. -/
theorem pureOfEuclideanSpace_mul_self (u : EuclideanSpace ℝ (Fin 3)) :
    pureOfEuclideanSpace u * pureOfEuclideanSpace u = -((‖u‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
  rw [← sq, sq_eq_neg_normSq.2 (re_pureOfEuclideanSpace u), normSq_eq_norm_mul_self,
    LinearIsometry.norm_map, sq]

/-- The pure quaternion of a unit vector squares to `-1`. -/
theorem pureOfEuclideanSpace_mul_self_of_norm_eq_one {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ‖u‖ = 1) : pureOfEuclideanSpace u * pureOfEuclideanSpace u = -1 := by
  rw [pureOfEuclideanSpace_mul_self, hu, one_pow, Quaternion.coe_one]

end Quaternion

end
