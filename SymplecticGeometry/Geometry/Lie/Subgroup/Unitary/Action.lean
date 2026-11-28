/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Subgroup.Unitary.LieAlgebra
public import TauCeti.Geometry.Lie.FundamentalVectorField
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The linear action of the matrix unitary Lie group

The unitary subgroup `unitarySubgroup (GL n 𝕜)` acts on column vectors `n → 𝕜` through its
inclusion into the matrices, `g • v = g *ᵥ v`. With Tau Ceti's closed-subgroup Lie group
structure on it (`TauCeti.Lie.matrixUnitaryLieGroup`), this file shows that the action is smooth
and computes its fundamental vector fields over `ℂ`: the generator of `ξ` at `y` is `X *ᵥ y`, for
the skew-Hermitian matrix `X = matrixUnitaryLieAlgebraEquiv ξ`.

The smoothness of the action is proved as Tau Ceti proves `Matrix.instContMDiffSMulMulVec` for
the matrices with the `L²` operator norm: `(A, v) ↦ A *ᵥ v` is a real bilinear map of
finite-dimensional spaces, here composed with the inclusion of the group. The computation of
the fundamental vector fields adapts Tau Ceti's `fundamentalLinearMap_symplecticGroup`, for the
symplectic group acting on its model space: the orbit map of `y` is the inclusion into the
matrices followed by the continuous linear map `A ↦ A *ᵥ y`, whose differential is itself.

## Main results

* `TauCeti.Lie.contMDiff_unitarySubgroup_coe_matrix`: the inclusion of the unitary group into the
  matrices is smooth.
* `TauCeti.Lie.instContMDiffSMulUnitarySubgroup`: the action on `n → 𝕜` is smooth.
* `TauCeti.Lie.fundamentalVectorField_unitarySubgroup`: its fundamental vector field of `ξ` at
  `y` is `matrixUnitaryLieAlgebraEquiv ξ *ᵥ y`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 20
  (fundamental vector fields of a Lie group action).
-/

public section

open Manifold
open scoped ContDiff Manifold Matrix Matrix.Norms.Operator TauCeti.Lie.MatrixUnitary

namespace TauCeti.Lie

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The inclusion of the unitary group `unitarySubgroup (GL n 𝕜)`, with Tau Ceti's
closed-subgroup charts, into `Matrix n n 𝕜` is smooth. -/
theorem contMDiff_unitarySubgroup_coe_matrix :
    ContMDiff 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
        (unitarySubgroup (GL n 𝕜))).toSubmodule) 𝓘(ℝ, Matrix n n 𝕜) ∞
      (fun k : unitarySubgroup (GL n 𝕜) ↦ ((k : GL n 𝕜) : Matrix n n 𝕜)) :=
  Units.contMDiff_val.comp
    (matrixUnitaryEmbeddedLieSubgroupData (n := n) (𝕜 := 𝕜)).contMDiff_subtypeVal

/-- The unitary group `unitarySubgroup (GL n 𝕜)` acts smoothly on column vectors,
`g • v = g *ᵥ v`. -/
instance instContMDiffSMulUnitarySubgroup :
    ContMDiffSMul 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
        (unitarySubgroup (GL n 𝕜))).toSubmodule) 𝓘(ℝ, n → 𝕜) ∞
      (unitarySubgroup (GL n 𝕜)) (n → 𝕜) where
  contMDiff_smul := by
    -- The action is the real bilinear map `(A, v) ↦ A *ᵥ v` after the inclusion.
    have hB : ContMDiff (𝓘(ℝ, Matrix n n 𝕜).prod 𝓘(ℝ, n → 𝕜)) 𝓘(ℝ, n → 𝕜) ∞
        fun p : Matrix n n 𝕜 × (n → 𝕜) ↦ p.1 *ᵥ p.2 := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact (Matrix.mulVecBilin ℝ ℝ : Matrix n n 𝕜 →ₗ[ℝ] (n → 𝕜) →ₗ[ℝ] (n → 𝕜))
        |>.toContinuousBilinearMap.isBoundedBilinearMap.contDiff.contMDiff
    exact hB.comp (((contMDiff_unitarySubgroup_coe_matrix (n := n) (𝕜 := 𝕜)).comp
      contMDiff_fst).prodMk contMDiff_snd)

/-- **Generators of the linear unitary action.** The fundamental vector field of `ξ` in the Lie
algebra of `unitarySubgroup (GL n ℂ)` takes at `y` the value `X *ᵥ y`, where `X` is the
skew-Hermitian matrix `matrixUnitaryLieAlgebraEquiv ξ`. -/
theorem fundamentalVectorField_unitarySubgroup
    (ξ : GroupLieAlgebra 𝓘(ℝ, 𝔨[n]) (unitarySubgroup (GL n ℂ))) (y : n → ℂ) :
    fundamentalVectorField 𝓘(ℝ, n → ℂ) ξ y =
      (matrixUnitaryLieAlgebraEquiv ξ : Matrix n n ℂ) *ᵥ y := by
  -- The orbit map of `y` is the inclusion into the matrices followed by `A ↦ A *ᵥ y`.
  let L : Matrix n n ℂ →L[ℝ] n → ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip y)
  have h := L.mvfderiv_comp_apply
    ((contMDiff_unitarySubgroup_coe_matrix (n := n) (𝕜 := ℂ) 1).mdifferentiableAt (by simp)) ξ
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply] at h
  rw [fundamentalVectorField_apply, coe_matrixUnitaryLieAlgebraEquiv_apply]
  have hL : (fun g : unitarySubgroup (GL n ℂ) ↦ g • y) =
      fun k : unitarySubgroup (GL n ℂ) ↦ L ((k : GL n ℂ) : Matrix n n ℂ) := by
    ext1 k
    simp [L, Subgroup.smul_def, Units.smul_def]
  rw [hL]
  exact h

end TauCeti.Lie

end
