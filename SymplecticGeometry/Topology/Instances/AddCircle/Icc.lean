/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Points of a closed period interval in `AddCircle`

Mathlib's `AddCircle.coe_eq_coe_iff_of_mem_Ico` says that the quotient map `𝕜 → AddCircle p` is
injective on a half-open interval `[a, a + p)`. On the closed interval `[a, a + p]` it identifies
exactly the two ends: two points have the same image only if they are equal or are `a` and
`a + p`.

## Main results

* `AddCircle.coe_eq_coe_iff_of_mem_Icc`: two points of `[a, a + p]` have the same image exactly
  when they are equal or are the two ends.
* `AddCircle.coe_eq_zero_iff_of_mem_Icc`: a point of `[0, p]` has image `0` exactly when it is
  `0` or `p`.
-/

public section

open Set

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  {p : 𝕜} [hp : Fact (0 < p)] {a x y : 𝕜}

/-- Two points of `[a, a + p]` have the same image in `AddCircle p` exactly when they are equal or
are the two ends `a` and `a + p`. -/
theorem coe_eq_coe_iff_of_mem_Icc (hx : x ∈ Icc a (a + p)) (hy : y ∈ Icc a (a + p)) :
    (x : AddCircle p) = y ↔ x = y ∨ x = a ∧ y = a + p ∨ x = a + p ∧ y = a := by
  have ha : a ∈ Ico a (a + p) := ⟨le_rfl, lt_add_of_pos_right a hp.out⟩
  have hI {z : 𝕜} (hz : z ∈ Icc a (a + p)) : z = a + p ∨ z ∈ Ico a (a + p) :=
    hz.2.eq_or_lt.imp id fun h ↦ ⟨hz.1, h⟩
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases hI hx with rfl | hx' <;> rcases hI hy with rfl | hy'
    · exact Or.inl rfl
    · rw [coe_add_period] at h
      exact Or.inr (Or.inr ⟨rfl, ((coe_eq_coe_iff_of_mem_Ico ha hy').1 h).symm⟩)
    · rw [coe_add_period] at h
      exact Or.inr (Or.inl ⟨(coe_eq_coe_iff_of_mem_Ico hx' ha).1 h, rfl⟩)
    · exact Or.inl ((coe_eq_coe_iff_of_mem_Ico hx' hy').1 h)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (coe_add_period p x).symm
    · exact coe_add_period p y

/-- A point of `[0, p]` has image `0` in `AddCircle p` exactly when it is `0` or `p`. -/
theorem coe_eq_zero_iff_of_mem_Icc (hx : x ∈ Icc 0 p) : (x : AddCircle p) = 0 ↔ x = 0 ∨ x = p := by
  have h := coe_eq_coe_iff_of_mem_Icc (a := 0) (x := x) (y := 0) (by rwa [zero_add])
    ⟨le_rfl, by rw [zero_add]; exact hp.out.le⟩
  rw [coe_zero, zero_add] at h
  rw [h]
  have hp0 : (0 : 𝕜) ≠ p := hp.out.ne
  tauto

end AddCircle
