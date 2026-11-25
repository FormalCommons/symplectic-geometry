/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Alternating maps on multiples of one vector

An alternating map vanishes on a family two of whose members are multiples of the same vector
(`AlternatingMap.map_eq_zero_of_eq_smul`). This generalizes `AlternatingMap.map_eq_zero_of_eq`,
the case of two equal members, to which the proof reduces by linearity in those two arguments.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- An alternating map vanishes on a family `v` whose members `v i` and `v j`, for `i ≠ j`, are
multiples `a • x` and `b • x` of the same vector `x`. -/
theorem map_eq_zero_of_eq_smul (f : M [⋀^ι]→ₗ[R] N) {v : ι → M} {i j : ι} (hij : i ≠ j)
    {x : M} {a b : R} (hi : v i = a • x) (hj : v j = b • x) : f v = 0 := by
  classical
  have hv : v = Function.update (Function.update v j (b • x)) i (a • x) := by
    rw [← hi, ← hj, Function.update_eq_self, Function.update_eq_self]
  rw [hv, f.map_update_smul, ← Function.update_comm hij, f.map_update_smul,
    f.map_eq_zero_of_eq _ (i := i) (j := j) (by simp [hij]) hij, smul_zero, smul_zero]

end AlternatingMap

end
