/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Alternating maps of few vectors and on multiples of one vector

An alternating map of one vector is determined by its values on the one-element families `![w]`
(`AlternatingMap.ext_fin_one`), and one of two vectors by its values on the pairs `![v, w]`
(`AlternatingMap.ext_fin_two`). A proof that two such maps agree can then work with vectors
instead of families `Fin 1 → M` or `Fin 2 → M`.

An alternating map vanishes on a family two of whose members are multiples of the same vector
(`AlternatingMap.map_eq_zero_of_eq_smul`). This generalizes `AlternatingMap.map_eq_zero_of_eq`,
the case of two equal members, to which the proof reduces by linearity in those two arguments.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- Two alternating maps of one vector are equal when they agree on every one-element family
`![w]`. -/
@[ext]
theorem ext_fin_one {f g : M [⋀^Fin 1]→ₗ[R] N} (h : ∀ w, f ![w] = g ![w]) : f = g :=
  ext fun v ↦ by
    rw [← FinVec.etaExpand_eq v]
    exact h (v 0)

/-- Two alternating maps of two vectors are equal when they agree on every pair `![v, w]`. -/
@[ext]
theorem ext_fin_two {f g : M [⋀^Fin 2]→ₗ[R] N} (h : ∀ v w, f ![v, w] = g ![v, w]) : f = g :=
  ext fun u ↦ by
    rw [← FinVec.etaExpand_eq u]
    exact h (u 0) (u 1)

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
