/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Laurent monomials on `X × Circle`

For a topological space `X` and a complex normed space `V`, the *Laurent monomial* of degree
`k : ℤ` with coefficient `g : C(X, V)` is the continuous map `(x, u) ↦ u ^ k • g x` on
`X × Circle`. For `V = ℂ` and `g = 1` it is the power `u ^ k` of the circle coordinate; in
particular `laurentMonomial 1 1` is the circle coordinate `(x, u) ↦ u` itself, the one form of
that coordinate the library uses.

This file has only the definition and its algebra. The density of the Laurent polynomials, by the
Stone–Weierstrass theorem, is in `SymplecticGeometry.Topology.ContinuousMap.LaurentApproximation`.

## Main definitions and results

* `ContinuousMap.laurentMonomial k`: the linear map `g ↦ ((x, u) ↦ u ^ k • g x)` from `C(X, V)` to
  `C(X × Circle, V)`.
* `ContinuousMap.laurentMonomial_mul_laurentMonomial` and `ContinuousMap.star_laurentMonomial`:
  products and conjugates of scalar Laurent monomials.

## References

* [A. Hatcher, *Vector Bundles and K-Theory*][Hatcher2017], §2.1
-/

public section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The Laurent monomial of degree `k` with coefficient `g`: the map `(x, u) ↦ u ^ k • g x` on
`X × Circle`, as a linear map in `g`. -/
noncomputable def laurentMonomial (k : ℤ) : C(X, V) →ₗ[ℂ] C(X × Circle, V) where
  toFun g :=
    ⟨fun w => (w.2 : ℂ) ^ k • g w.1,
      ((continuous_subtypeVal.comp continuous_snd).zpow₀ k
        fun w => Or.inl (Circle.coe_ne_zero w.2)).smul (g.continuous.comp continuous_fst)⟩
  map_add' g h := by ext w; exact smul_add _ _ _
  map_smul' a g := by ext w; exact smul_comm _ _ _

@[simp]
theorem laurentMonomial_apply (k : ℤ) (g : C(X, V)) (w : X × Circle) :
    laurentMonomial k g w = (w.2 : ℂ) ^ k • g w.1 :=
  (rfl)

/-- The product of two scalar Laurent monomials is a Laurent monomial. -/
@[simp]
theorem laurentMonomial_mul_laurentMonomial (i j : ℤ) (g h : C(X, ℂ)) :
    laurentMonomial i g * laurentMonomial j h = laurentMonomial (i + j) (g * h) := by
  ext w
  simp only [mul_apply, laurentMonomial_apply, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero w.2)]
  ring

/-- The conjugate of a scalar Laurent monomial is the Laurent monomial of the opposite degree with
the conjugate coefficient. -/
@[simp]
theorem star_laurentMonomial (k : ℤ) (g : C(X, ℂ)) :
    star (laurentMonomial k g) = laurentMonomial (-k) (star g) := by
  ext w
  simp [zpow_neg, ← Circle.coe_inv_eq_conj]

end ContinuousMap

end
