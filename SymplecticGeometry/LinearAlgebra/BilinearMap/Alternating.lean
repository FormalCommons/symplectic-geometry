/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
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

Over a field, if `ω` is moreover left-separating, its value on the basis pair is nonzero
(`LinearMap.IsAlt.apply_basis_ne_zero`), so every alternating form `B` is the ratio of the two
values on the basis pair times `ω` (`LinearMap.IsAlt.apply_eq_div_mul`). Over an ordered field,
if `B` is positive wherever `ω` is, that ratio is positive
(`LinearMap.IsAlt.apply_basis_div_apply_basis_pos`).

Finally, a real bilinear map `B` with `B x y = c * a` and `c > 0` takes the value `a` on
`(√c)⁻¹ • x` and `(√c)⁻¹ • y` (`LinearMap.apply_inv_sqrt_smul_inv_sqrt_smul`): this is how a map
that multiplies a form by `c` is rescaled to one that preserves it.

The expansion is Tau Ceti's `LinearMap.IsAlt.apply_smul_add_smul`, applied to the expansions of
the two arguments in the basis.
-/

public section

namespace LinearMap.IsAlt

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommMonoid M] [Module R M] [AddCommGroup N]
  [Module R N]

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

end CommRing

/-- Over a nontrivial semiring, a left-separating alternating bilinear map on a module with a
basis `b` indexed by `Fin 2` does not vanish on the pair `b 0, b 1`. -/
theorem apply_basis_ne_zero {R M N : Type*} [CommSemiring R] [Nontrivial R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] {ω : M →ₗ[R] M →ₗ[R] N} (h : ω.IsAlt)
    (hω : ω.SeparatingLeft) (b : Module.Basis (Fin 2) R M) : ω (b 0) (b 1) ≠ 0 :=
  fun h0 ↦ one_ne_zero <| h.eq_zero_of_smul_apply_basis_eq_zero b hω ((one_smul R _).trans h0)

section Field

variable {K M : Type*} [Field K] [AddCommMonoid M] [Module K M]

/-- On a module with a basis `b` indexed by `Fin 2`, an alternating bilinear form `B` is
`B (b 0) (b 1) / ω (b 0) (b 1)` times a left-separating alternating bilinear form `ω`. -/
theorem apply_eq_div_mul {B ω : M →ₗ[K] M →ₗ[K] K} (hB : B.IsAlt) (hω : ω.IsAlt)
    (hω' : ω.SeparatingLeft) (b : Module.Basis (Fin 2) K M) (u v : M) :
    B u v = B (b 0) (b 1) / ω (b 0) (b 1) * ω u v := by
  rw [div_mul_eq_mul_div, eq_div_iff (hω.apply_basis_ne_zero hω' b), mul_comm (B (b 0) (b 1))]
  exact hB.apply_mul_eq_mul_apply_of_basis hω b u v

/-- On a module with a basis `b` indexed by `Fin 2` over an ordered field, if an alternating
bilinear form `B` is positive on every pair on which a left-separating alternating bilinear form
`ω` is positive, then the ratio `B (b 0) (b 1) / ω (b 0) (b 1)`, by which `B` is a multiple
of `ω` (`LinearMap.IsAlt.apply_eq_div_mul`), is positive. -/
theorem apply_basis_div_apply_basis_pos [LinearOrder K] [IsStrictOrderedRing K]
    {B ω : M →ₗ[K] M →ₗ[K] K} (hB : B.IsAlt) (hω : ω.IsAlt) (hω' : ω.SeparatingLeft)
    (b : Module.Basis (Fin 2) K M) (hpos : ∀ u v, 0 < ω u v → 0 < B u v) :
    0 < B (b 0) (b 1) / ω (b 0) (b 1) := by
  rcases (hω.apply_basis_ne_zero hω' b).lt_or_gt with hlt | hgt
  · have h10 : 0 < ω (b 1) (b 0) := by
      rw [← hω.neg]
      exact neg_pos.2 hlt
    have h := hpos _ _ h10
    rw [hB.apply_eq_div_mul hω hω' b] at h
    exact pos_of_mul_pos_left h h10.le
  · exact div_pos (hpos _ _ hgt) hgt

end Field

end LinearMap.IsAlt

namespace LinearMap

/-- If a real bilinear map `B` takes the value `c * a` on `x` and `y`, with `c > 0`, then it takes
the value `a` on `(√c)⁻¹ • x` and `(√c)⁻¹ • y`. -/
theorem apply_inv_sqrt_smul_inv_sqrt_smul {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) {c a : ℝ} (hc : 0 < c) {x y : M} (h : B x y = c * a) :
    B ((√c)⁻¹ • x) ((√c)⁻¹ • y) = a := by
  have hs : (√c)⁻¹ * (√c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h]
  rw [← mul_assoc, ← mul_assoc, hs, one_mul]

end LinearMap

end
