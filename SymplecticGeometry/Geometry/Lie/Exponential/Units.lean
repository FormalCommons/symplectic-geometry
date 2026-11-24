/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The exponential of the Lie group of units of a normed algebra

For a complete normed real algebra `R`, the Lie group `Rˣ` has the tangent space `R` at `1`, and
its exponential `mulInvariantExp` is the exponential of the algebra, packaged as a unit by Tau
Ceti's `TauCeti.expUnit` (`mulInvariantExp_eq_expUnit`). This is Tau Ceti's
`mulInvariantOneParameterSubgroup_eq_expUnitHom` evaluated at time `1`. For `ℂˣ` the exponential
is `Complex.exp` (`coe_mulInvariantExp_eq_exp_complex`).

The Lie algebra `GroupLieAlgebra 𝓘(ℝ, R) Rˣ` is `R` by definition, but `rw` and `simp` do not
see through `GroupLieAlgebra`. The statements therefore read a tangent vector `v` in `R` through
Tau Ceti's linear equivalence `groupLieAlgebraEquivModelVectorSpace`, so that their right-hand
sides are terms of `R`, to which the lemmas about `R` apply.

## Main results

* `mulInvariantExp_eq_expUnit`: `mulInvariantExp v = TauCeti.expUnit v` on `Rˣ`, with `v` read
  in `R`.
* `coe_mulInvariantExp_eq_exp_complex`: `(mulInvariantExp v : ℂ) = Complex.exp v` on `ℂˣ`, with
  `v` read in `ℂ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 20 (one-parameter subgroups
  and the exponential map of a Lie group).
-/

public section

open Manifold TauCeti
open scoped Manifold ContDiff

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
  TauCeti.normedAlgebraRatOfReal

/-- The exponential of the Lie group `Rˣ` of units of a complete normed real algebra, at a tangent
vector `v` at `1`, is the exponential `TauCeti.expUnit` of the algebra at `v` read in `R`. -/
theorem mulInvariantExp_eq_expUnit {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] (v : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) :
    mulInvariantExp v = TauCeti.expUnit (groupLieAlgebraEquivModelVectorSpace v) := by
  have h := mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul (I := 𝓘(ℝ, R)) (G := Rˣ) v 1
  have h2 := DFunLike.congr_fun (mulInvariantOneParameterSubgroup_eq_expUnitHom (R := R) v)
    (Multiplicative.ofAdd 1)
  rw [one_smul] at h
  refine h.symm.trans (h2.trans ?_)
  exact (expUnitHom_apply (R := R) (v : R) 1).trans (congrArg expUnit (one_smul ℝ (v : R)))

/-- The exponential of the Lie group `ℂˣ`, read in `ℂ`, is `Complex.exp` of the tangent vector
read in `ℂ`. -/
@[simp]
theorem coe_mulInvariantExp_eq_exp_complex (v : GroupLieAlgebra 𝓘(ℝ, ℂ) ℂˣ) :
    ((mulInvariantExp v : ℂˣ) : ℂ) = Complex.exp (groupLieAlgebraEquivModelVectorSpace v) :=
  (congrArg Units.val (mulInvariantExp_eq_expUnit v)).trans
    ((TauCeti.expUnit_coe (R := ℂ) v).trans (congrFun Complex.exp_eq_exp_ℂ v).symm)

end
