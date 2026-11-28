/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Interior
import SymplecticGeometry.Geometry.Lie.GroupLieAlgebraLieHom
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The exponential of the Lie group of units of a normed algebra

For a complete normed real algebra `R`, the Lie group `Rˣ` has the tangent space `R` at `1`, and
its exponential `mulInvariantExp` is the exponential of the algebra, packaged as a unit by Tau
Ceti's `TauCeti.expUnit` (`mulInvariantExp_eq_expUnit`). This is Tau Ceti's
`mulInvariantOneParameterSubgroup_eq_expUnitHom` evaluated at time `1`. For `ℂˣ` the exponential
is `Complex.exp` (`coe_mulInvariantExp_eq_exp_complex`). So a smooth homomorphism `ρ` from a
finite-dimensional Lie group into `Rˣ`, `R` finite-dimensional, carries the exponential to the
exponential of the algebra at the derivative of `ρ` at `1`, read in `R`
(`ContMDiffMonoidMorphism.coe_map_mulInvariantExp`), by the library's
`ContMDiffMonoidMorphism.map_mulInvariantExp`, once that derivative is identified with the Lie
algebra map of `ρ` (`ContMDiffMonoidMorphism.mfderiv_coe_apply_one`).

The Lie algebra `GroupLieAlgebra 𝓘(ℝ, R) Rˣ` is `R` by definition, but `rw` and `simp` do not
see through `GroupLieAlgebra`. The statements therefore read a tangent vector `v` in `R` through
Tau Ceti's linear equivalence `groupLieAlgebraEquivModelVectorSpace`, so that their right-hand
sides are terms of `R`, to which the lemmas about `R` apply.

## Main results

* `mulInvariantExp_eq_expUnit`: `mulInvariantExp v = TauCeti.expUnit v` on `Rˣ`, with `v` read
  in `R`.
* `coe_mulInvariantExp_eq_exp_complex`: `(mulInvariantExp v : ℂ) = Complex.exp v` on `ℂˣ`, with
  `v` read in `ℂ`.
* `ContMDiffMonoidMorphism.contMDiff_coe`: for a smooth homomorphism `ρ` into `Rˣ`, the map
  `g ↦ (ρ g : R)` is smooth.
* `ContMDiffMonoidMorphism.mfderiv_coe_apply_one`: for a smooth homomorphism `ρ` into `Rˣ`, the
  derivative at `1` of `g ↦ (ρ g : R)` is `ρ.groupLieAlgebraLieHom`, read in `R`.
* `ContMDiffMonoidMorphism.coe_map_mulInvariantExp`: `(ρ (mulInvariantExp ξ) : R) = exp (dρ ξ)`
  for a smooth homomorphism `ρ` into `Rˣ`, with `dρ` the derivative at `1` of `g ↦ (ρ g : R)`.

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

section Homomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- For a smooth homomorphism `ρ : G → Rˣ`, the map `g ↦ (ρ g : R)` is smooth. -/
theorem ContMDiffMonoidMorphism.contMDiff_coe (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) :
    ContMDiff I 𝓘(ℝ, R) ∞ (fun g ↦ (ρ g : R)) :=
  Units.contMDiff_val.comp ρ.contMDiff_toFun

/-- For a smooth homomorphism `ρ : G → Rˣ`, the map `g ↦ (ρ g : R)` is differentiable at `1`. -/
theorem ContMDiffMonoidMorphism.mdifferentiableAt_coe_one
    (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) :
    MDifferentiableAt I 𝓘(ℝ, R) (fun g ↦ (ρ g : R)) 1 :=
  (ρ.contMDiff_coe 1).mdifferentiableAt (by simp)

variable [CompleteSpace E] [LieGroup I ∞ G]

/-- **The Lie algebra map of a homomorphism into `Rˣ`, read in `R`.** For a smooth homomorphism
`ρ : G → Rˣ` and `ξ` in the Lie algebra of `G`, the derivative at `1` of `g ↦ (ρ g : R)` at `ξ`
is `ρ.groupLieAlgebraLieHom ξ`, read in `R` through `groupLieAlgebraEquivModelVectorSpace`. -/
theorem ContMDiffMonoidMorphism.mfderiv_coe_apply_one
    (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ) (ξ : GroupLieAlgebra I G) :
    mfderiv I 𝓘(ℝ, R) (fun g ↦ (ρ g : R)) 1 ξ =
      (groupLieAlgebraEquivModelVectorSpace (ρ.groupLieAlgebraLieHom ξ) : R) := by
  have hρ : HasMFDerivAt I 𝓘(ℝ, R) ρ 1 (mfderiv I 𝓘(ℝ, R) ρ 1) :=
    (ρ.contMDiff_toFun.mdifferentiableAt (by simp)).hasMFDerivAt
  rw [show (fun g ↦ (ρ g : R)) = Units.val ∘ ρ from rfl,
    (((Units.hasMFDerivAt_val (𝕜 := ℝ) (ρ 1)).comp 1 hρ).congr_mfderiv
      (ContinuousLinearMap.id_comp _)).mfderiv,
    ContMDiffMonoidMorphism.coe_groupLieAlgebraLieHom, MonoidHom.groupLieAlgebraMap_apply,
    ContMDiffMonoidMorphism.coe_toMonoidHom]
  -- Both sides are `mfderiv I 𝓘(ℝ, R) ρ 1 ξ`: `groupLieAlgebraEquivModelVectorSpace` is
  -- `LinearEquiv.refl`, but `rw` cannot use `LinearEquiv.refl_apply` here, since the tangent
  -- space of `Rˣ` at `ρ 1` and the Lie algebra of `Rˣ` are `R` only by definition.
  rfl

attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **A smooth homomorphism into the units of an algebra carries the exponential to the
exponential of the algebra.** For a smooth homomorphism `ρ : G → Rˣ` and `ξ` in the Lie algebra
of `G`, the element `ρ (exp ξ)` of `R` is `NormedSpace.exp` of the derivative at `1` of
`g ↦ (ρ g : R)` applied to `ξ`. -/
theorem ContMDiffMonoidMorphism.coe_map_mulInvariantExp [FiniteDimensional ℝ E] [T2Space G]
    [FiniteDimensional ℝ R] (ρ : ContMDiffMonoidMorphism I 𝓘(ℝ, R) ∞ G Rˣ)
    (ξ : GroupLieAlgebra I G) :
    ((ρ (mulInvariantExp ξ) : Rˣ) : R) =
      NormedSpace.exp (show R from mfderiv I 𝓘(ℝ, R) (fun g ↦ (ρ g : R)) 1 ξ) := by
  rw [ρ.map_mulInvariantExp, mulInvariantExp_eq_expUnit, TauCeti.expUnit_coe,
    ρ.mfderiv_coe_apply_one]

end Homomorphism

end
