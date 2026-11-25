/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.L2OpNorm
public import SymplecticGeometry.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
public import TauCeti.Analysis.Matrix.Polar.Deformation
public import TauCeti.Analysis.Matrix.Polar.Symplectic

/-!
# Smooth polar decomposition of a family of symplectic matrices

For a smooth family `Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ` of symplectic matrices, the polar
decomposition `Ψ t = P_t U_t`, with `P_t = √(Ψ_t Ψ_tᵀ)` positive definite and `U_t` orthogonal,
depends smoothly on `t`, and so does the contraction `(t, s) ↦ P_t ^ s` of the positive factor,
jointly in `t` and `s`. All these matrices are symplectic (Tau Ceti's
`SymplecticGroup.sqrt_mul_star_mem`, `SymplecticGroup.rpow_mem` and
`SymplecticGroup.polarUnitary_mem`), and they are all `1` at the times when `Ψ t = 1`
(`Matrix.exists_contDiff_polar_symplecticGroup`).

The smoothness of `P_t` and `U_t` in `t` comes from that of the polar factors on the general
linear group (Tau Ceti's `Matrix.GeneralLinearGroup.contMDiff_sqrt_mul_star` and
`Matrix.GeneralLinearGroup.contMDiff_coe_polarUnitary`), and the joint smoothness of `P_t ^ s`
from `Matrix.contDiff_rpow_of_posDef`.

Smoothness is stated for the ℓ² operator norm `Matrix.Norms.L2Operator` in
`Matrix.exists_contDiff_polar_symplecticGroup_l2Op`, and for the entrywise norm
`Matrix.Norms.Elementwise` in `Matrix.exists_contDiff_polar_symplecticGroup`, as in
`Matrix.exists_contDiff_path_symplecticGroup`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 and Proposition 7.1.22.
-/

public section

open scoped ContDiff Manifold MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section L2

open scoped Matrix.Norms.L2Operator

/-- **Smooth polar decomposition of a family of symplectic matrices**, for the ℓ² operator norm
`Matrix.Norms.L2Operator`: the form of `Matrix.exists_contDiff_polar_symplecticGroup` in which
both the hypothesis and the conclusion use that norm. -/
theorem exists_contDiff_polar_symplecticGroup_l2Op {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨsp : ∀ t, Ψ t ∈ symplecticGroup n ℝ) :
    ∃ (U : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (Q : ℝ × ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ),
      ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ Q ∧
      (∀ t, U t ∈ symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ) ∧
      (∀ p, Q p ∈ symplecticGroup n ℝ) ∧
      (∀ t, Q (t, 0) = 1) ∧ (∀ t, Ψ t = Q (t, 1) * U t) ∧
      ∀ t, Ψ t = 1 → U t = 1 ∧ ∀ s, Q (t, s) = 1 := by
  -- The invertible matrices `Ψ t`, a smooth curve in the general linear group, and their
  -- positive polar factors `P t`.
  let g : ℝ → GL (n ⊕ n) ℝ := fun t ↦
    ((isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det (hΨsp t))).unit
  have hg (t : ℝ) : (g t : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t := IsUnit.unit_spec _
  have hgs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Matrix (n ⊕ n) (n ⊕ n) ℝ) ∞ g :=
    ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
      (by simpa [Function.comp_def, hg] using hΨ.contMDiff)
  set P : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ CFC.sqrt (Ψ t * star (Ψ t)) with hPdef
  have hP (t : ℝ) : (P t).PosDef := GeneralLinearGroup.posDef_sqrt_mul_star (g t)
  have hPsp (t : ℝ) : P t ∈ symplecticGroup n ℝ := SymplecticGroup.sqrt_mul_star_mem (hΨsp t)
  have hPc : ContDiff ℝ ∞ P := by
    simpa [Function.comp_def, hg] using
      (GeneralLinearGroup.contMDiff_sqrt_mul_star.comp hgs).contDiff
  refine ⟨fun t ↦ (g t).polarUnitary, fun p ↦ P p.1 ^ p.2,
    (GeneralLinearGroup.contMDiff_coe_polarUnitary.comp hgs).contDiff,
    contDiff_rpow_of_posDef (hPc.comp contDiff_fst) contDiff_snd fun p ↦ hP p.1, fun t ↦
    ⟨SymplecticGroup.polarUnitary_mem (hΨsp t), (g t).polarUnitary.property⟩,
    fun p ↦ SymplecticGroup.rpow_mem (hP p.1).posSemidef (hPsp p.1) p.2,
    fun t ↦ CFC.rpow_zero _ (hP t).posSemidef.nonneg, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · beta_reduce
    rw [CFC.rpow_one _ (hP t).posSemidef.nonneg]
    exact (Units.sqrt_mul_star_mul_polarUnitary (g t)).symm
  · have h1 : g t = 1 := Units.ext ((hg t).trans ht)
    simp [hPdef, ht, h1]

end L2

open scoped Matrix.Norms.Elementwise in
/-- **Smooth polar decomposition of a family of symplectic matrices.** For a smooth family
`Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ` of symplectic matrices, there are a smooth family `U` of
symplectic orthogonal matrices and a jointly smooth family `Q : ℝ × ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ`
of symplectic matrices with `Q (t, 0) = 1` and `Ψ t = Q (t, 1) * U t`, such that `U t = 1` and
`Q (t, s) = 1` for every `s` whenever `Ψ t = 1`. Smoothness is for the entrywise norm
`Matrix.Norms.Elementwise`. -/
theorem exists_contDiff_polar_symplecticGroup {Ψ : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨsp : ∀ t, Ψ t ∈ symplecticGroup n ℝ) :
    ∃ (U : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ) (Q : ℝ × ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ),
      ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ Q ∧
      (∀ t, U t ∈ symplecticGroup n ℝ ⊓ orthogonalGroup (n ⊕ n) ℝ) ∧
      (∀ p, Q p ∈ symplecticGroup n ℝ) ∧
      (∀ t, Q (t, 0) = 1) ∧ (∀ t, Ψ t = Q (t, 1) * U t) ∧
      ∀ t, Ψ t = 1 → U t = 1 ∧ ∀ s, Q (t, s) = 1 := by
  obtain ⟨U, Q, hU, hQ, h⟩ :=
    exists_contDiff_polar_symplecticGroup_l2Op (contDiff_l2Op_iff_contDiff_elementwise.2 hΨ) hΨsp
  exact ⟨U, Q, contDiff_l2Op_iff_contDiff_elementwise.1 hU,
    contDiff_l2Op_iff_contDiff_elementwise.1 hQ, h⟩

end Matrix

end
