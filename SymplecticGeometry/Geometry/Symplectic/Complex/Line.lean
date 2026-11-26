/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Line
import Mathlib.LinearAlgebra.Complex.Module
import SymplecticGeometry.LinearAlgebra.BilinearMap.Alternating

/-!
# Alternating forms on the complex line

On the real plane `ℂ`, every alternating real bilinear form `B` is a multiple of the standard
symplectic form `ω₀` of Tau Ceti's `TauCeti.stdComplexSymplecticForm`, namely
`B u v = B 1 i * ω₀ u v`, since `ω₀ 1 i = 1`
(`LinearMap.IsAlt.apply_eq_mul_stdComplexSymplecticForm`). It is
`LinearMap.IsAlt.apply_eq_smul_apply_basis` for the basis `(1, i)` of `ℂ`.
-/

public section

namespace LinearMap.IsAlt

/-- An alternating real bilinear form `B` on `ℂ` is `B 1 i` times the standard symplectic form
`ω₀ u v = Re u Im v - Im u Re v`. -/
theorem apply_eq_mul_stdComplexSymplecticForm {B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ} (hB : B.IsAlt)
    (u v : ℂ) : B u v = B 1 Complex.I * TauCeti.stdComplexSymplecticForm u v := by
  rw [hB.apply_eq_smul_apply_basis Complex.basisOneI u v, TauCeti.stdComplexSymplecticForm_apply,
    smul_eq_mul, mul_comm]
  simp

end LinearMap.IsAlt

end
