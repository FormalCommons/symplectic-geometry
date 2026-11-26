/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Frame
import SymplecticGeometry.LinearAlgebra.Symplectic.Subspace

/-!
# Lagrangian subspaces of `ℂⁿ` transverse to `ℝⁿ`

Tau Ceti attaches to a real `n × n` matrix `S` the subspace
`Matrix.lagrangianChart S = {S y + i y | y ∈ ℝⁿ}` of `ℂⁿ`. It meets `ℝⁿ` only in `0`, it determines
`S`, and for symmetric `S` it is maximal totally real and isotropic for `Im ⟪·, ·⟫`. This file
proves the converse: those properties characterize the subspaces `S.lagrangianChart` with `S`
symmetric (McDuff–Salamon, §2.3).

## Main results

* `Matrix.exists_isSymm_eq_lagrangianChart`: a maximal totally real subspace `V` of `ℂⁿ` on which
  `Im ⟪·, ·⟫` vanishes and with `V ∩ ℝⁿ = 0` is `S.lagrangianChart` for a symmetric real `S`.

An `example` at the end shows that the isotropy hypothesis cannot be dropped: for the
nilpotent `S = !![0, 1; 0, 0]`, `S.lagrangianChart` is maximal totally real and meets `ℝ²` only
in `0`, yet it is the chart subspace of no symmetric matrix.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace Matrix

open TauCeti SymplecticGeometry SymplecticGeometry.StdSpace Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A maximal totally real subspace `V` of `ℂⁿ` that is isotropic for the symplectic form
`Im ⟪·, ·⟫` and meets `ℝⁿ` only in `0` is the subspace `{S y + i y | y ∈ ℝⁿ}` of a symmetric
real matrix `S`. -/
theorem exists_isSymm_eq_lagrangianChart {V : Submodule ℝ (EuclideanSpace ℂ n)}
    (hV : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ) V)
    (hiso : ∀ v ∈ V, ∀ w ∈ V, (inner ℂ v w).im = 0)
    (hreal : V ⊓ realSubspace n = ⊥) :
    ∃ S : Matrix n n ℝ, S.IsSymm ∧ V = S.lagrangianChart := by
  let ε := (complexEuclideanEquiv n).toLinearEquiv
  have hdimV := hV.finrank_eq_finrank_complex
  have hdimR := (isMaximalTotallyReal_realSubspace (n := n)).finrank_eq_finrank_complex
  -- The image of `V` in `StdSpace n` is Lagrangian.
  have hL : (stdForm n).IsLagrangian (V.map ε.toLinearMap) := by
    refine SymplecticForm.isLagrangian_iff_isIsotropic_and_two_mul_finrank_eq.2
      ⟨SymplecticForm.isIsotropic_iff.2 ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      exact (stdForm_apply_eq_im_inner v w).trans (hiso v hv w hw)
    · rw [LinearEquiv.finrank_map_eq, finrank_stdSpace, hdimV, finrank_euclideanSpace]
  -- It is transverse to the horizontal subspace `{y = 0}`, the image of `ℝⁿ`.
  have hcompl : IsCompl (V.map ε.toLinearMap) (LinearMap.ker y) := by
    rw [← map_realSubspace]
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
    · rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, finrank_stdSpace, hdimV,
        hdimR, finrank_euclideanSpace]
      omega
    · rw [disjoint_iff, ← Submodule.map_inf _ ε.injective, hreal, Submodule.map_bot]
  obtain ⟨S, hS, hSV⟩ := exists_eq_graphY_of_isCompl hL hcompl
  refine ⟨S, hS, Submodule.map_injective_of_injective ε.injective ?_⟩
  exact hSV.trans (map_lagrangianChart S).symm

/-- Isotropy for `Im ⟪·, ·⟫` cannot be dropped from `Matrix.exists_isSymm_eq_lagrangianChart`:
for `S = !![0, 1; 0, 0]`, `det (S + i) = -1`, so `S.lagrangianChart` is maximal totally real, and
it meets `ℝ²` only in `0`, but it is not the chart subspace of a symmetric matrix. -/
example : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ (Fin 2)) Complex.I).restrictScalars ℝ)
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).lagrangianChart ∧
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).lagrangianChart ⊓ realSubspace (Fin 2) = ⊥ ∧
    ¬ ∃ T : Matrix (Fin 2) (Fin 2) ℝ, T.IsSymm ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).lagrangianChart = T.lagrangianChart := by
  refine ⟨?_, lagrangianChart_inf_realSubspace _, ?_⟩
  · rw [lagrangianChart_def]
    refine isMaximalTotallyReal_realImage ?_
    simp [lagrangianChartFrame_def, det_fin_two]
  · rintro ⟨T, hT, h⟩
    rw [lagrangianChart_inj] at h
    subst h
    simpa using congrFun (congrFun hT 0) 1

end Matrix

end
