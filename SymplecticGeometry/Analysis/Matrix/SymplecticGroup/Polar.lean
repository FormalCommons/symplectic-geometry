/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.Matrix.Exponential.Log
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

Joint smoothness of the real powers comes from `P ^ s = exp (s • log P)`
(`Matrix.PosDef.rpow_eq_exp_smul_cfc_log`) and the smoothness of the logarithm on positive definite
matrices (`Matrix.contDiffOn_cfc_log`): for a smooth family `M` of positive definite matrices and a
smooth real function `f`, the map `x ↦ M x ^ f x` is smooth (`Matrix.contDiff_rpow_of_posDef`).
This is the argument of Tau Ceti's `Matrix.GeneralLinearGroup.contMDiff_polarDeformation`, which
proves the smoothness of `(t, A) ↦ √(A A⋆) ^ (1 - t) U_A` on the general linear group.

Smoothness is stated for the ℓ² operator norm `Matrix.Norms.L2Operator` in
`Matrix.contDiff_rpow_of_posDef` and `Matrix.exists_contDiff_polar_symplecticGroup_l2Op`, and for
the entrywise norm `Matrix.Norms.Elementwise` in `Matrix.exists_contDiff_polar_symplecticGroup`,
as in `Matrix.exists_contDiff_path_symplecticGroup`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 and Proposition 7.1.22.
-/

public section

open scoped ContDiff MatrixOrder

open NormedSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section L2

open scoped Matrix.Norms.L2Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ∞ω}

/-- **Joint smoothness of real powers of positive definite matrices.** For a `C^k` family `M` of
positive definite real matrices and a `C^k` real function `f`, the map `x ↦ M x ^ f x` is `C^k`,
for the ℓ² operator norm `Matrix.Norms.L2Operator`. -/
theorem contDiff_rpow_of_posDef {M : E → Matrix n n ℝ} {f : E → ℝ} (hM : ContDiff ℝ k M)
    (hf : ContDiff ℝ k f) (hpos : ∀ x, (M x).PosDef) :
    ContDiff ℝ k fun x ↦ M x ^ f x := by
  have hlog : ContDiff ℝ k fun x ↦ cfc Real.log (M x) :=
    contDiffOn_cfc_log.comp_contDiff hM hpos
  convert (contDiff_exp ℝ).comp (hf.smul hlog) using 1
  funext x
  exact (hpos x).rpow_eq_exp_smul_cfc_log (f x)

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
  -- The invertible matrices `Ψ t` and their positive polar factors `P t`.
  let g : ℝ → GL (n ⊕ n) ℝ := fun t ↦
    ((isUnit_iff_isUnit_det _).2 (SymplecticGroup.symplectic_det (hΨsp t))).unit
  have hg (t : ℝ) : (g t : Matrix (n ⊕ n) (n ⊕ n) ℝ) = Ψ t := IsUnit.unit_spec _
  set P : ℝ → Matrix (n ⊕ n) (n ⊕ n) ℝ := fun t ↦ CFC.sqrt (Ψ t * star (Ψ t)) with hPdef
  have hP (t : ℝ) : (P t).PosDef := GeneralLinearGroup.posDef_sqrt_mul_star (g t)
  have hPsp (t : ℝ) : P t ∈ symplecticGroup n ℝ := SymplecticGroup.sqrt_mul_star_mem (hΨsp t)
  have hPc : ContDiff ℝ ∞ P := by
    have hstar := (starL' ℝ : Matrix (n ⊕ n) (n ⊕ n) ℝ ≃L[ℝ] _).contDiff (n := ∞)
    exact contDiffOn_sqrt.comp_contDiff (hΨ.mul (hstar.comp hΨ))
      fun t ↦ isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_mul_star (g t))
  have hQ : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ P p.1 ^ p.2 :=
    contDiff_rpow_of_posDef (hPc.comp contDiff_fst) contDiff_snd fun p ↦ hP p.1
  -- The orthogonal polar factor is `P t ^ (-1) * Ψ t`.
  have hU (t : ℝ) : ((g t).polarUnitary : Matrix (n ⊕ n) (n ⊕ n) ℝ) = P t ^ (-1 : ℝ) * Ψ t := by
    rw [Units.coe_polarUnitary,
      CFC.inverse_eq_rpow_neg_one (Units.isStrictlyPositive_sqrt_mul_star (g t)), hg]
  refine ⟨fun t ↦ (g t).polarUnitary, fun p ↦ P p.1 ^ p.2, ?_, hQ, fun t ↦
    ⟨SymplecticGroup.polarUnitary_mem (hΨsp t), (g t).polarUnitary.property⟩,
    fun p ↦ SymplecticGroup.rpow_mem (hP p.1).posSemidef (hPsp p.1) p.2,
    fun t ↦ CFC.rpow_zero _ (hP t).posSemidef.nonneg, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · convert (hQ.comp (contDiff_id.prodMk (contDiff_const (c := (-1 : ℝ))))).mul hΨ
      using 1
    funext t
    exact hU t
  · beta_reduce
    rw [CFC.rpow_one _ (hP t).posSemidef.nonneg]
    exact (Units.sqrt_mul_star_mul_polarUnitary (g t)).symm
  · have h1 : P t = 1 := by simp [hPdef, ht]
    refine ⟨?_, fun s ↦ ?_⟩
    · beta_reduce
      rw [hU, h1, ht, CFC.one_rpow, one_mul]
    · simp only [h1, CFC.one_rpow]

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
