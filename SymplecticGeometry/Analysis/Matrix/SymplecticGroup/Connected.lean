/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import SymplecticGeometry.Analysis.CStarAlgebra.Exponential
public import SymplecticGeometry.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
public import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
public import SymplecticGeometry.Topology.Algebra.Matrix.Realify
public import TauCeti.Analysis.Matrix.Polar.Symplectic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Connected
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary

/-!
# Smooth paths in the real symplectic group

Any two real symplectic matrices are joined by a smooth path of symplectic matrices
(`Matrix.exists_contDiff_path_symplecticGroup`). Tau Ceti's
`Matrix.isPathConnected_symplecticGroup` gives a continuous path; this file makes it smooth.

Left multiplication by `A⁻¹` reduces to joining `1` to a symplectic matrix `C`. Its polar
decomposition `C = P U` has both factors symplectic (`SymplecticGroup.sqrt_mul_star_mem`,
`SymplecticGroup.polarUnitary_mem`). The positive factor is joined to `1` by `t ↦ P ^ t`, which
is symplectic (`SymplecticGroup.rpow_mem`) and smooth in `t` (`CFC.contDiff_const_rpow`). The
orthogonal factor `U` is the realification of a unitary matrix
(`Matrix.symplecticGroup_inf_orthogonalGroup`), which is `exp (I • H)` for a Hermitian `H`
(`Matrix.UnitaryGroup.exists_expUnitary_eq`); it is joined to `1` by
`t ↦ realify (exp (I • t • H))`, which is smooth (`selfAdjoint.contDiff_expUnitary_smul`, and
`Matrix.realifyCLM`, realification as a continuous linear map). The path is
`t ↦ A P ^ t realify (exp (I • t • H))`; the same factors appear in Tau Ceti's
`SymplecticGroup.joinedIn_polarUnitary` and `Matrix.isPathConnected_symplecticGroup`, joined here
by smooth paths instead.

Smoothness is stated for the entrywise norm `Matrix.Norms.Elementwise`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2.
-/

public section

open scoped ContDiff MatrixOrder

open Matrix NormedSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section L2

open scoped Matrix.Norms.L2Operator

/-- The construction behind `Matrix.exists_contDiff_path_symplecticGroup`, with smoothness of each
entry, which does not depend on a norm: the path `t ↦ A P ^ t realify (exp (I • t • H))`, where
`A⁻¹ B = P U` is the polar decomposition and `U = realify (exp (I • H))`. -/
private theorem exists_path_contDiff_apply {A B : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (hB : B ∈ symplecticGroup n ℝ) :
    ∃ γ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, (∀ i j, ContDiff ℝ ∞ fun t ↦ γ t i j) ∧
      (∀ t, γ t ∈ symplecticGroup n ℝ) ∧ γ 0 = A ∧ γ 1 = B := by
  have hA' : A⁻¹ ∈ symplecticGroup n ℝ := SymplecticGroup.inv_mem hA
  obtain ⟨C, hCB⟩ := (isUnit_iff_isUnit_det _).2
    (SymplecticGroup.symplectic_det (Submonoid.mul_mem _ hA' hB))
  have hC : (C : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈ symplecticGroup n ℝ :=
    hCB ▸ Submonoid.mul_mem _ hA' hB
  set P := CFC.sqrt ((C : Matrix (n ⊕ n) (n ⊕ n) ℝ) * star (C : Matrix (n ⊕ n) (n ⊕ n) ℝ))
  have hP : P.PosDef := GeneralLinearGroup.posDef_sqrt_mul_star C
  have hU : (C.polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) ∈
      symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ :=
    ⟨SymplecticGroup.polarUnitary_mem hC, C.polarUnitary.property⟩
  rw [symplecticGroup_inf_orthogonalGroup] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨H, hH⟩ := UnitaryGroup.exists_expUnitary_eq ⟨V, hV⟩
  have hre := (realifyCLM n n ℂ).contDiff (n := ∞)
  rw [coe_realifyCLM] at hre
  refine ⟨fun t ↦ A * P ^ t * ((selfAdjoint.expUnitary (t • H) : Matrix n n ℂ)).realify,
    fun i j ↦ (entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      ((contDiff_const.mul (CFC.contDiff_const_rpow hP.isStrictlyPositive)).mul
        (hre.comp (selfAdjoint.contDiff_expUnitary_smul H))),
      fun t ↦ ?_, ?_, ?_⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hA
      (SymplecticGroup.rpow_mem hP.posSemidef (SymplecticGroup.sqrt_mul_star_mem hC) t))
      (realify_mem_symplecticGroup_iff.2 (selfAdjoint.expUnitary _).property)
  · simp [CFC.rpow_zero P hP.posSemidef.nonneg, selfAdjoint.expUnitary_zero, realify_one]
  · simp only [one_smul, hH, CFC.rpow_one P hP.posSemidef.nonneg, mul_assoc]
    rw [← realifyAlgHom_apply, hVU, Units.sqrt_mul_star_mul_polarUnitary, hCB, ← mul_assoc,
      mul_nonsing_inv A (SymplecticGroup.symplectic_det hA), one_mul]

end L2

open scoped Matrix.Norms.Elementwise in
/-- **Smooth paths in the real symplectic group.** Any two real symplectic matrices `A` and `B`
are joined by a smooth path `γ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ` of symplectic matrices with
`γ 0 = A` and `γ 1 = B`, smooth for the entrywise norm `Matrix.Norms.Elementwise`. -/
theorem exists_contDiff_path_symplecticGroup {A B : Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hA : A ∈ symplecticGroup n ℝ) (hB : B ∈ symplecticGroup n ℝ) :
    ∃ γ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t, γ t ∈ symplecticGroup n ℝ) ∧ γ 0 = A ∧ γ 1 = B := by
  obtain ⟨γ, hγ, h⟩ := exists_path_contDiff_apply hA hB
  exact ⟨γ, contDiff_pi.2 fun i ↦ contDiff_pi.2 fun j ↦ hγ i j, h⟩

end Matrix

end
