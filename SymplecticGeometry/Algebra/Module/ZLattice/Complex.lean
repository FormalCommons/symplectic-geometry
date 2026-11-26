/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Algebra.Module.ZLattice.Complex

/-!
# Oriented bases of lattices in the complex plane

For a `ℤ`-basis `b₀, b₁` of a lattice `L` in `ℂ`, the number `Im (conj b₀ * b₁)` is the signed
area of the parallelogram spanned by `b₀` and `b₁`. Its absolute value is the covolume of `L`
(Tau Ceti's `ZLattice.covolume_eq_abs_im`), so it is never zero, and its sign is the orientation
of the basis. Replacing `b₁` by `-b₁` reverses that sign, so every lattice has a positively
oriented basis.

## Main results

* `ZLattice.im_conj_mul_basis_ne_zero`: `Im (conj b₀ * b₁) ≠ 0` for a `ℤ`-basis of a lattice.
* `ZLattice.exists_basis_zero_lt_im_conj_mul`: every lattice in `ℂ` has a `ℤ`-basis with
  `0 < Im (conj b₀ * b₁)`.
-/

public section

open Module ComplexConjugate

namespace ZLattice

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The signed area `Im (conj b₀ * b₁)` of the parallelogram spanned by a `ℤ`-basis of a lattice
in `ℂ` is nonzero. -/
theorem im_conj_mul_basis_ne_zero (b : Basis (Fin 2) ℤ L) : (conj (b 0 : ℂ) * b 1).im ≠ 0 := by
  rw [← abs_pos, ← covolume_eq_abs_im]
  exact covolume_pos L _

/-- Every lattice in `ℂ` has a positively oriented `ℤ`-basis `b₀, b₁`: one with
`0 < Im (conj b₀ * b₁)`. -/
theorem exists_basis_zero_lt_im_conj_mul :
    ∃ b : Basis (Fin 2) ℤ L, 0 < (conj (b 0 : ℂ) * b 1).im := by
  let b := Module.finBasisOfFinrankEq ℤ L
    (by rw [ZLattice.rank ℝ L, Complex.finrank_real_complex])
  rcases (im_conj_mul_basis_ne_zero L b).lt_or_gt with h | h
  · refine ⟨b.unitsSMul ![1, -1], ?_⟩
    simpa [Basis.unitsSMul_apply] using h
  · exact ⟨b, h⟩

end ZLattice

end
