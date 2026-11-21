/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Injectivity of a linear map with one column added

Over a division ring `K`, a linear map `A : V →ₗ[K] W` and a vector `z : W` give the linear map
`A.coprod (toSpanSingleton K W z) : V × K →ₗ[K] W`, `(v, t) ↦ A v + t • z`. It is injective
exactly when `A` is injective and `z` is not in the range of `A`
(`LinearMap.injective_coprod_toSpanSingleton_iff`).
-/

public section

open Function

/-- Over a division ring, the map `(v, t) ↦ A v + t • z` is injective exactly when `A` is
injective and `z` is not in the range of `A`. -/
theorem LinearMap.injective_coprod_toSpanSingleton_iff {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (A : V →ₗ[K] W) (z : W) :
    Injective (A.coprod (LinearMap.toSpanSingleton K W z)) ↔
      Injective A ∧ z ∉ LinearMap.range A := by
  simp only [injective_iff_map_eq_zero, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
    Prod.forall, Prod.mk_eq_zero, LinearMap.mem_range, not_exists]
  refine ⟨fun h ↦ ⟨fun v hv ↦ (h v 0 (by simp [hv])).1, fun v hv ↦ ?_⟩,
    fun ⟨h, hz⟩ v t hvt ↦ ?_⟩
  · have := (h v (-1) (by simp [hv])).2
    simp at this
  · by_cases ht : t = 0
    · subst ht
      exact ⟨h v (by simpa using hvt), rfl⟩
    · refine absurd ?_ (hz (-t⁻¹ • v))
      rw [map_smul, eq_neg_of_add_eq_zero_left hvt, smul_neg, neg_smul, neg_neg, smul_smul,
        inv_mul_cancel₀ ht, one_smul]

end
