/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Implicit

/-!
# Simple roots of polynomials with Nash coefficients

A continuous function `f` on `σ → ℝ` whose value `f y` is, for every `y` near `x`, a root of the
polynomial obtained from `P : (MvPolynomial σ ℝ)[X]` by evaluating its coefficients at `y`, is a
Nash germ at `x` as soon as that polynomial is separable at `y = x`.

* `TauCeti.isNashAt_of_eventually_isRoot`: the statement above.

The proof writes the equation as a single polynomial in the variables `σ ⊕ Unit`, which is Nash
by `MvPolynomial.isNashAt_eval`, notes that `f x` is a simple root, and applies Tau Ceti's Nash
implicit function theorem `TauCeti.IsNashAt.implicit`. Polynomial relations are written as in
Tau Ceti's `TauCeti.isSemialgebraicOn_of_polynomial_relation_of_not_nullified`.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998, Section 8.1.
-/

public section

open Topology

namespace TauCeti
open _root_.Polynomial

/-- A function `f : (σ → ℝ) → ℝ`, continuous at `x`, whose value `f y` is a root of the
polynomial `P` with coefficients evaluated at `y`, for every `y` near `x`, is a Nash germ at `x`
when that polynomial is separable at `x`. -/
theorem isNashAt_of_eventually_isRoot {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ}
    {P : (MvPolynomial σ ℝ)[X]} {x : σ → ℝ}
    (hcont : ContinuousAt f x)
    (hroot : ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).IsRoot (f y))
    (hsep : (P.map (MvPolynomial.eval x)).Separable) :
    IsNashAt f x := by
  -- The equation `P (y, z) = 0` as a polynomial function of `(y, z)`.
  set F : (σ ⊕ Unit → ℝ) → ℝ :=
    fun p ↦ (P.map (MvPolynomial.eval (p ∘ Sum.inl))).eval (p (.inr ()))
  have hF : F = fun p ↦ MvPolynomial.eval p
      (P.eval₂ (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (.inr ()))) := by
    ext p
    rw [Polynomial.hom_eval₂, ← eval_map]
    simp only [F, MvPolynomial.eval_X]
    congr 2
    ext <;> simp
  have hFN : IsNashAt F (Sum.elim x fun _ ↦ f x) := by
    rw [hF]
    exact MvPolynomial.isNashAt_eval _
  -- The root `f x` of `P (x, ·)` is simple.
  have hd : deriv (fun y ↦ F (Sum.elim x fun _ ↦ y)) (f x) ≠ 0 := by
    simp only [F, Sum.elim_inr, Sum.elim_comp_inl, Polynomial.deriv]
    have := hsep.aeval_derivative_ne_zero (x := f x)
      (by simpa [aeval_def] using hroot.self_of_nhds)
    simpa [aeval_def] using this
  exact hFN.implicit hcont (by simpa [F, Function.comp_def] using hroot) hd

end TauCeti

end
