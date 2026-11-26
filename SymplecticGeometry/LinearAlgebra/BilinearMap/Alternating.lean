/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Alternating bilinear maps on a plane

An alternating bilinear map `ω` on a module with a basis `b` indexed by `Fin 2` is determined by
its value on the pair `b 0, b 1`: it is that value times the determinant of the coordinates of
its two arguments (`LinearMap.IsAlt.apply_eq_smul_apply_basis`). In particular any two
alternating bilinear forms on a two-dimensional space are proportional
(`LinearMap.IsAlt.apply_mul_eq_mul_apply_of_basis`).

The expansion is Tau Ceti's `LinearMap.IsAlt.apply_smul_add_smul`, applied to the expansions of
the two arguments in the basis.
-/

public section

namespace LinearMap.IsAlt

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An alternating bilinear map on a module with a basis `b` indexed by `Fin 2` is its value on
`b 0, b 1` times the determinant of the coordinates of its arguments. -/
theorem apply_eq_smul_apply_basis {ω : M →ₗ[R] M →ₗ[R] N} (h : ω.IsAlt)
    (b : Module.Basis (Fin 2) R M) (u v : M) :
    ω u v = (b.repr u 0 * b.repr v 1 - b.repr u 1 * b.repr v 0) • ω (b 0) (b 1) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [Fin.sum_univ_two]
  exact h.apply_smul_add_smul _ _ _ _ _ _

/-- Two alternating bilinear forms `B` and `ω` on a module with a basis `b` indexed by `Fin 2` are
proportional: `B u v * ω (b 0) (b 1) = ω u v * B (b 0) (b 1)`. -/
theorem apply_mul_eq_mul_apply_of_basis {B ω : M →ₗ[R] M →ₗ[R] R} (hB : B.IsAlt)
    (hω : ω.IsAlt) (b : Module.Basis (Fin 2) R M) (u v : M) :
    B u v * ω (b 0) (b 1) = ω u v * B (b 0) (b 1) := by
  rw [hB.apply_eq_smul_apply_basis b u v, hω.apply_eq_smul_apply_basis b u v, smul_eq_mul,
    smul_eq_mul]
  ring

end LinearMap.IsAlt

end
