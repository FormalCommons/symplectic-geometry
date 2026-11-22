/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The ranges of two injective linear maps out of the same space

Two injective linear maps `i : M →ₗ[R] N₁` and `j : M →ₗ[R] N₂` identify their ranges with `M`,
through `LinearEquiv.ofInjective`, and so with each other. This file defines that linear
equivalence `LinearEquiv.ofInjectiveRange i j hi hj : range i ≃ₗ[R] range j`, which sends `i x`
to `j x` (`LinearEquiv.ofInjectiveRange_apply`), gives its value on a general element of
`range i` (`LinearEquiv.coe_ofInjectiveRange_apply`), and shows that its inverse is
`LinearEquiv.ofInjectiveRange j i hj hi` and how such equivalences compose.
-/

public section

open Function LinearMap

namespace LinearEquiv

variable {R M N₁ N₂ N₃ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂] [AddCommMonoid N₃]
  [Module R N₃]

/-- For injective linear maps `i : M → N₁` and `j : M → N₂`, the linear equivalence
`range i ≃ range j` that sends `i x` to `j x`, that is, `j ∘ i⁻¹`. -/
noncomputable def ofInjectiveRange (i : M →ₗ[R] N₁) (j : M →ₗ[R] N₂) (hi : Injective i)
    (hj : Injective j) : range i ≃ₗ[R] range j :=
  (ofInjective i hi).symm.trans (ofInjective j hj)

variable (i : M →ₗ[R] N₁) (j : M →ₗ[R] N₂) (k : M →ₗ[R] N₃) (hi : Injective i)
  (hj : Injective j) (hk : Injective k)

theorem ofInjectiveRange_def :
    ofInjectiveRange i j hi hj = (ofInjective i hi).symm.trans (ofInjective j hj) :=
  (rfl)

/-- `ofInjectiveRange i j` sends `i x` to `j x`, as elements of the ranges given by
`LinearEquiv.ofInjective`. -/
@[simp]
theorem ofInjectiveRange_ofInjective (x : M) :
    ofInjectiveRange i j hi hj (ofInjective i hi x) = ofInjective j hj x := by
  rw [ofInjectiveRange_def, trans_apply, symm_apply_apply]

/-- `ofInjectiveRange i j` sends `i x` to `j x`. -/
@[simp]
theorem ofInjectiveRange_apply (x : M) (h : i x ∈ range i) :
    ofInjectiveRange i j hi hj ⟨i x, h⟩ = ⟨j x, mem_range_self j x⟩ := by
  have hx : (⟨i x, h⟩ : range i) = ofInjective i hi x :=
    Subtype.ext (ofInjective_apply i (h := hi) x).symm
  rw [hx, ofInjectiveRange_ofInjective]
  exact Subtype.ext (ofInjective_apply j (h := hj) x)

/-- `ofInjectiveRange i j` sends `y` in the range of `i` to `j x`, where `x` is the unique
preimage of `y` under `i`. -/
theorem coe_ofInjectiveRange_apply (y : range i) :
    (ofInjectiveRange i j hi hj y : N₂) = j ((ofInjective i hi).symm y) := by
  rw [ofInjectiveRange_def, trans_apply, ofInjective_apply]

/-- `ofInjectiveRange i j` sends `i x`, as `i.rangeRestrict x`, to `j.rangeRestrict x`. -/
@[simp]
theorem ofInjectiveRange_rangeRestrict (x : M) :
    ofInjectiveRange i j hi hj (i.rangeRestrict x) = j.rangeRestrict x := by
  have hx : i.rangeRestrict x = ofInjective i hi x :=
    Subtype.ext ((codRestrict_apply _ i x).trans (ofInjective_apply i x).symm)
  rw [hx, ofInjectiveRange_ofInjective]
  exact Subtype.ext ((ofInjective_apply j x).trans (codRestrict_apply _ j x).symm)

/-- The inverse of `ofInjectiveRange i j` is `ofInjectiveRange j i`. -/
@[simp]
theorem ofInjectiveRange_symm : (ofInjectiveRange i j hi hj).symm = ofInjectiveRange j i hj hi := by
  refine LinearEquiv.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (ofInjective j hj).surjective y
  rw [symm_apply_eq, ofInjectiveRange_ofInjective, ofInjectiveRange_ofInjective]

/-- `ofInjectiveRange i i` is the identity of `range i`. -/
@[simp]
theorem ofInjectiveRange_self : ofInjectiveRange i i hi hi = refl R (range i) := by
  rw [ofInjectiveRange_def, symm_trans_self]

/-- `ofInjectiveRange j k ∘ ofInjectiveRange i j = ofInjectiveRange i k`. -/
@[simp]
theorem ofInjectiveRange_trans :
    (ofInjectiveRange i j hi hj).trans (ofInjectiveRange j k hj hk) =
      ofInjectiveRange i k hi hk := by
  refine LinearEquiv.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (ofInjective i hi).surjective y
  rw [trans_apply, ofInjectiveRange_ofInjective, ofInjectiveRange_ofInjective,
    ofInjectiveRange_ofInjective]

end LinearEquiv
