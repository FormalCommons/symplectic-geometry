/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear automorphisms of `ι → K` with a prescribed coordinate

For a nonzero vector `c : ι → K` over a field `K`, the linear form `w ↦ ∑ k, c k * w k` is one
coordinate of some linear automorphism of `ι → K`: `LinearEquiv.exists_apply_eq_sum_mul`. The
other coordinates are those of `w` but one, chosen where `c` does not vanish.
-/

public section

open Function

/-- For a nonzero vector `c` and an index `i`, some linear automorphism of `ι → K` has, as its
coordinate `i`, the linear form `w ↦ ∑ k, c k * w k`. -/
theorem LinearEquiv.exists_apply_eq_sum_mul {ι K : Type*} [Fintype ι] [Field K]
    {c : ι → K} (hc : c ≠ 0) (i : ι) :
    ∃ e : (ι → K) ≃ₗ[K] (ι → K), ∀ w, e w i = ∑ k, c k * w k := by
  classical
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hc
  -- Coordinate `i` is the form; the other coordinates are those of `w` other than `k₀`.
  let f : (ι → K) →ₗ[K] (ι → K) :=
    { toFun w j := if j = i then ∑ k, c k * w k else w (Equiv.swap i k₀ j)
      map_add' w w' := by
        ext j
        split_ifs <;> simp [mul_add, Finset.sum_add_distrib, *]
      map_smul' a w := by
        ext j
        split_ifs <;> simp [Finset.mul_sum, mul_left_comm, *] }
  have hf : Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun w hw ↦ ?_
    have hk : ∀ k ≠ k₀, w k = 0 := fun k hk ↦ by
      have h := congrFun hw (Equiv.swap i k₀ k)
      have hki : Equiv.swap i k₀ k ≠ i := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact hk
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, hki, ite_false, Equiv.swap_apply_self,
        Pi.zero_apply] using h
    have h := congrFun hw i
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, ite_true, Pi.zero_apply] at h
    rw [Finset.sum_eq_single k₀ (fun k _ hk' ↦ by rw [hk k hk', mul_zero]) (by simp)] at h
    ext k
    rcases eq_or_ne k k₀ with rfl | hk'
    · exact (mul_eq_zero.1 h).resolve_left (by simpa using hk₀)
    · exact hk k hk'
  exact ⟨LinearEquiv.ofInjectiveEndo f hf, fun w ↦ by simp [f]⟩

end
