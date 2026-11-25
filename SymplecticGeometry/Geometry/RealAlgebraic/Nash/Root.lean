/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Rename
public import TauCeti.Geometry.RealAlgebraic.Nash.Implicit

/-!
# Simple roots of polynomials with Nash coefficients

A continuous function `f` on `σ → ℝ` whose value `f y` is, for every `y` near `x`, a root of the
polynomial obtained from `P : (MvPolynomial σ ℝ)[X]` by evaluating its coefficients at `y`, is a
Nash germ at `x` as soon as `f x` is a simple root of that polynomial at `y = x`: its derivative
does not vanish there.

* `TauCeti.isNashAt_of_eventually_isRoot`: the statement above.

The proof writes the equation as a single polynomial in the variables `σ ⊕ Unit`, which is Nash
by `MvPolynomial.isNashAt_eval`, and applies Tau Ceti's Nash
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
when `f x` is a simple root of that polynomial at `x`, that is, its derivative does not vanish
at `f x`. -/
theorem isNashAt_of_eventually_isRoot {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ}
    {P : (MvPolynomial σ ℝ)[X]} {x : σ → ℝ}
    (hcont : ContinuousAt f x)
    (hroot : ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).IsRoot (f y))
    (hd : (P.map (MvPolynomial.eval x)).derivative.eval (f x) ≠ 0) :
    IsNashAt f x := by
  -- The equation `P (y, z) = 0` as a polynomial function of `(y, z)`.
  set F : (σ ⊕ Unit → ℝ) → ℝ :=
    fun p ↦ (P.map (MvPolynomial.eval (p ∘ Sum.inl))).eval (p (.inr ()))
  have hF : F = fun p ↦ MvPolynomial.eval p
      (P.eval₂ (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (.inr ()))) := by
    ext p
    rw [Polynomial.hom_eval₂, ← eval_map, ← Polynomial.map_map, map_eval_map_rename,
      MvPolynomial.eval_X]
  have hFN : IsNashAt F (Sum.elim x fun _ ↦ f x) := by
    rw [hF]
    exact MvPolynomial.isNashAt_eval _
  -- The root `f x` of `P (x, ·)` is simple.
  have hd : deriv (fun y ↦ F (Sum.elim x fun _ ↦ y)) (f x) ≠ 0 := by
    simpa only [F, Sum.elim_inr, Sum.elim_comp_inl, Polynomial.deriv] using hd
  exact hFN.implicit hcont (by simpa [F, Function.comp_def] using hroot) hd

end TauCeti

end
