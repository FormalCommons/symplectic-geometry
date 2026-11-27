/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.Riemannian

import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Trivializations of a continuous Riemannian bundle, read in a Euclidean space

In a continuous Riemannian bundle `E` with finite-dimensional model fibre `F`, the fibre
coordinates of the trivialization at a point `x` are dominated by the bundle norm near `x`, after a
fixed injective continuous linear map from `F` to a Euclidean space
(`exists_injective_norm_trivializationAt_le`). The map is a scaled copy of `toEuclidean`, and the
bound comes from Mathlib's `eventually_norm_trivializationAt_lt`.

Such a map replaces the fibre coordinates, which carry no inner product, by vectors of a Euclidean
space, while losing no information and never increasing the norm near `x`.
-/

public section

open Bundle Filter Function Module
open scoped Topology

variable {B : Type*} (F : Type*) [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

/-- In a continuous Riemannian bundle with finite-dimensional model fibre `F`, there is an
injective continuous linear map `A` from `F` to a Euclidean space such that, for every `y` near
`x` and every `v : E y`, the image under `A` of the fibre coordinates of `v` in the
trivialization at `x` has norm at most `‖v‖`. -/
theorem exists_injective_norm_trivializationAt_le (x : B) :
    ∃ A : F →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)), Injective A ∧
      ∀ᶠ y in 𝓝 x, ∀ v : E y, ‖A (trivializationAt F E x ⟨y, v⟩).2‖ ≤ ‖v‖ := by
  set e := trivializationAt F E x
  obtain ⟨C, hC, hCev⟩ := eventually_norm_trivializationAt_lt F E x
  set T : F →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    (toEuclidean : F ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F))).toContinuousLinearMap
  set c : ℝ := (C * (‖T‖ + 1))⁻¹
  have hc : 0 < c := by positivity
  refine ⟨c • T, ?_, ?_⟩
  · intro v w hvw
    simpa [T, hc.ne'] using hvw
  filter_upwards [hCev, e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E x)]
    with y hy hyb v
  have h1 : ‖(e ⟨y, v⟩).2‖ ≤ C * ‖v‖ := by
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hyb]
    exact ((e.continuousLinearMapAt ℝ y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))
  have h2 : ‖(c • T) (e ⟨y, v⟩).2‖ ≤ c * (‖T‖ * (C * ‖v‖)) := by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg hc.le]
    gcongr
    exact (T.le_opNorm _).trans (by gcongr)
  have hT : c * (‖T‖ * C) ≤ 1 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc ‖(c • T) (e ⟨y, v⟩).2‖ ≤ c * (‖T‖ * C) * ‖v‖ := h2.trans_eq (by ring)
    _ ≤ ‖v‖ := mul_le_of_le_one_left (norm_nonneg _) hT

end
