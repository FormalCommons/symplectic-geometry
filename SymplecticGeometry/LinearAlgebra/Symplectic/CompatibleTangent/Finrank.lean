/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Matrix.Hermitian
public import SymplecticGeometry.Algebra.Star.Module
public import SymplecticGeometry.LinearAlgebra.Matrix.SelfAdjoint
public import SymplecticGeometry.LinearAlgebra.Symplectic.CompatibleTangent.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix

/-!
# Dimension of the tangent spaces to the space of compatible complex structures

For a symplectic form `ω` on a real vector space `V` of dimension `2 n` and an `ω`-compatible
complex structure `J`, Tau Ceti's `ω.compatibleTangentSpace J`, the endomorphisms `Y` that
anticommute with `J` and are skew-adjoint for `ω`, has dimension `n (n + 1)`, the dimension of
the space of compatible complex structures. McDuff–Salamon, Example 4.3.6, describe these
tangent spaces; the dimension is computed here from that description.

In the standard model `(StdSpace ι, ω₀, J₀)`, with `J₀` the map of `Matrix.J ι ℝ`, the tangent
space at `J₀` consists of the maps of the matrices `fromBlocks X (-Y) (-Y) (-X)` with `X` and `Y`
symmetric. The general case reduces to this one by a symplectomorphism carrying `J₀` to `J`
(`SymplecticGeometry.compatible_iff_exists_isSymplectomorphism_stdForm`).

## Main results

* `SymplecticGeometry.toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff`: the map of a
  matrix `A` lies in the compatible tangent space of `ω₀` at `J₀` if and only if `A`
  anticommutes with `Matrix.J ι ℝ` and is symmetric;
  `SymplecticGeometry.toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff_eq_fromBlocks`
  says the same in blocks: `A = fromBlocks A₁₁ A₁₂ A₁₂ (-A₁₁)` with `A₁₁` and `A₁₂` symmetric.
* `SymplecticGeometry.stdTangentEquiv`: the linear equivalence from pairs of symmetric matrices
  `(X, Y)` to that tangent space, sending `(X, Y)` to the map of `fromBlocks X (-Y) (-Y) (-X)`.
* `TauCeti.SymplecticForm.Compatible.finrank_compatibleTangentSpace`: for `finrank ℝ V = 2 * n`
  and a compatible `J`, the compatible tangent space at `J` has dimension `n * (n + 1)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], Example 4.3.6 (the tangent spaces).
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The map of a real matrix `A` indexed by `ι ⊕ ι` lies in the compatible tangent space of the
standard model at `J₀` if and only if `A` anticommutes with `Matrix.J ι ℝ` and is symmetric. -/
theorem toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    toEuclideanLin A ∈ (stdForm ι).compatibleTangentSpace (stdComplexStructure ι) ↔
      A * J ι ℝ + J ι ℝ * A = 0 ∧ A.IsHermitian := by
  constructor
  · intro h
    have h' := SymplecticForm.compatibleTangentSpace_le_tangentSpace h
    refine ⟨toEuclideanLin_mem_tangentSpace_stdComplexStructure_iff.1 h',
      isSymmetric_toEuclideanLin_iff.1 fun v w ↦ ?_⟩
    have := (SymplecticForm.mem_compatibleTangentSpace_iff_isSelfAdjoint h').1 h v w
    simpa only [SymplecticForm.associatedBilinForm_apply, stdForm_apply_stdComplexStructure] using
      this
  · rintro ⟨h₁, h₂⟩
    refine (SymplecticForm.mem_compatibleTangentSpace_iff_isSelfAdjoint
      (toEuclideanLin_mem_tangentSpace_stdComplexStructure_iff.2 h₁)).2 fun v w ↦ ?_
    simpa only [SymplecticForm.associatedBilinForm_apply, stdForm_apply_stdComplexStructure] using
      isSymmetric_toEuclideanLin_iff.2 h₂ v w

/-- The map of `fromBlocks X (-Y) (-Y) (-X)`, for symmetric `X` and `Y`, lies in the compatible
tangent space of the standard model at `J₀`. -/
theorem toEuclideanLin_fromBlocks_mem_compatibleTangentSpace_stdForm {X Y : Matrix ι ι ℝ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    toEuclideanLin (fromBlocks X (-Y) (-Y) (-X)) ∈
      (stdForm ι).compatibleTangentSpace (stdComplexStructure ι) := by
  refine toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff.2 ⟨?_, ?_⟩
  · simp [J, fromBlocks_multiply, fromBlocks_add]
  · exact hX.fromBlocks (by rw [conjTranspose_neg, hY.eq]) hX.neg

/-- The map of a real matrix `A` indexed by `ι ⊕ ι` lies in the compatible tangent space of the
standard model at `J₀` if and only if `A = fromBlocks A₁₁ A₁₂ A₁₂ (-A₁₁)` with `A₁₁` and `A₁₂`
symmetric. -/
theorem toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff_eq_fromBlocks
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    toEuclideanLin A ∈ (stdForm ι).compatibleTangentSpace (stdComplexStructure ι) ↔
      A = fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₁₂ (-A.toBlocks₁₁) ∧
        A.toBlocks₁₁.IsHermitian ∧ A.toBlocks₁₂.IsHermitian := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, h₁₁, h₁₂⟩ ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff.1 h
    rw [← fromBlocks_toBlocks A, J, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add,
      ← fromBlocks_zero, fromBlocks_inj] at h₁
    rw [IsHermitian, ← fromBlocks_toBlocks A, fromBlocks_conjTranspose, fromBlocks_inj] at h₂
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
      Matrix.neg_mul, zero_add, add_zero] at h₁
    obtain ⟨hQR, hPS, -, -⟩ := h₁
    have hR : A.toBlocks₂₁ = A.toBlocks₁₂ := (add_neg_eq_zero.1 hQR).symm
    have hS : A.toBlocks₂₂ = -A.toBlocks₁₁ := neg_eq_iff_eq_neg.1 (neg_add_eq_zero.1 hPS).symm
    refine ⟨?_, h₂.1, ?_⟩
    · conv_lhs => rw [← fromBlocks_toBlocks A, hR, hS]
    · rw [IsHermitian]
      conv_lhs => rw [← hR]
      exact h₂.2.1
  · rw [hA]
    simpa using toEuclideanLin_fromBlocks_mem_compatibleTangentSpace_stdForm h₁₁ h₁₂.neg

variable (ι) in
/-- The compatible tangent space of the standard model at `J₀` is linearly equivalent to pairs of
symmetric matrices: `(X, Y)` goes to the map of `fromBlocks X (-Y) (-Y) (-X)`. -/
noncomputable def stdTangentEquiv :
    (selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix ι ι ℝ)) ≃ₗ[ℝ]
    (stdForm ι).compatibleTangentSpace (stdComplexStructure ι) where
  toFun p := ⟨toEuclideanLin (fromBlocks (p.1 : Matrix ι ι ℝ) (-(p.2 : Matrix ι ι ℝ))
        (-(p.2 : Matrix ι ι ℝ)) (-(p.1 : Matrix ι ι ℝ))),
    toEuclideanLin_fromBlocks_mem_compatibleTangentSpace_stdForm p.1.property p.2.property⟩
  map_add' p q := by
    ext1
    rw [Submodule.coe_add, ← map_add, fromBlocks_add]
    simp [add_comm]
  map_smul' c p := by
    ext1
    rw [SetLike.val_smul, ← map_smul, fromBlocks_smul]
    simp
  invFun Y := (⟨(toEuclideanLin.symm (Y : Module.End ℝ (StdSpace ι))).toBlocks₁₁,
      (toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff_eq_fromBlocks.1
        (by simp)).2.1⟩,
    ⟨-(toEuclideanLin.symm (Y : Module.End ℝ (StdSpace ι))).toBlocks₁₂,
      (toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff_eq_fromBlocks.1
        (by simp)).2.2.neg⟩)
  left_inv p := by
    ext1 <;> ext1 <;> simp
  right_inv Y := by
    ext1
    have h := (toEuclideanLin_mem_compatibleTangentSpace_stdForm_iff_eq_fromBlocks
      (A := toEuclideanLin.symm (Y : Module.End ℝ (StdSpace ι)))).1 (by simp) |>.1
    simp only [neg_neg]
    rw [← h, LinearEquiv.apply_symm_apply]

@[simp]
theorem coe_stdTangentEquiv_apply (p : selfAdjoint (Matrix ι ι ℝ) × selfAdjoint (Matrix ι ι ℝ)) :
    (stdTangentEquiv ι p : Module.End ℝ (StdSpace ι)) =
      toEuclideanLin (fromBlocks (p.1 : Matrix ι ι ℝ) (-(p.2 : Matrix ι ι ℝ))
        (-(p.2 : Matrix ι ι ℝ)) (-(p.1 : Matrix ι ι ℝ))) :=
  (rfl)

@[simp]
theorem coe_stdTangentEquiv_symm_apply_fst
    (Y : (stdForm ι).compatibleTangentSpace (stdComplexStructure ι)) :
    (((stdTangentEquiv ι).symm Y).1 : Matrix ι ι ℝ) =
      (toEuclideanLin.symm (Y : Module.End ℝ (StdSpace ι))).toBlocks₁₁ :=
  (rfl)

@[simp]
theorem coe_stdTangentEquiv_symm_apply_snd
    (Y : (stdForm ι).compatibleTangentSpace (stdComplexStructure ι)) :
    (((stdTangentEquiv ι).symm Y).2 : Matrix ι ι ℝ) =
      -(toEuclideanLin.symm (Y : Module.End ℝ (StdSpace ι))).toBlocks₁₂ :=
  (rfl)

end SymplecticGeometry

namespace TauCeti.SymplecticForm

open SymplecticGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {n : ℕ}

/-- For a symplectic form `ω` on a real vector space of dimension `2 n` and an `ω`-compatible
complex structure `J`, the compatible tangent space at `J`, of endomorphisms anticommuting with
`J` and skew-adjoint for `ω`, has dimension `n (n + 1)`. -/
theorem Compatible.finrank_compatibleTangentSpace (hJ : ω.Compatible J)
    (hn : Module.finrank ℝ V = 2 * n) :
    Module.finrank ℝ (ω.compatibleTangentSpace J) = n * (n + 1) := by
  obtain ⟨Ψ, hΨ, hΨJ⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm (ι := Fin n)
    (by rw [hn, Fintype.card_fin])).1 hJ
  have hJ' : (stdComplexStructure (Fin n)).transport Ψ = J :=
    (AlmostComplexStructure.transport_eq_iff_isComplexLinearMap Ψ).2 hΨJ
  have hmap : ((stdForm (Fin n)).compatibleTangentSpace (stdComplexStructure (Fin n))).map
      Ψ.conj.toLinearMap = ω.compatibleTangentSpace J := by
    ext Y
    rw [Submodule.mem_map_equiv, ← hΨ.conj_mem_compatibleTangentSpace_iff,
      LinearEquiv.apply_symm_apply, hJ']
  rw [← hmap, LinearEquiv.finrank_map_eq, ← (stdTangentEquiv (Fin n)).finrank_eq,
    Module.finrank_prod, Matrix.finrank_selfAdjoint, Fintype.card_fin, ← two_mul,
    Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]

end TauCeti.SymplecticForm

end
