/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.OrthogonalLast

/-!
# Splitting off the last vector of an orthonormal basis

Let `b` be an orthonormal basis of a real inner product space `E`, indexed by `Fin (n + 1)`, and
`e` a basis of a real normed space `F`, indexed by `Fin n`. Sending `e` to Tau Ceti's
`OrthonormalBasis.orthogonalLast b` gives a continuous linear equivalence `ψ` of `F` with the
orthogonal complement of the last vector `p` of `b`
(`OrthonormalBasis.orthogonalLastEquivOfBasis`), and `(x, t) ↦ ψ x + t • p` is a continuous linear
equivalence `F × ℝ ≃L[ℝ] E` (`OrthonormalBasis.prodEquivOfBasis`). It sends the basis of `F × ℝ`
that lists `e` followed by `(0, 1)` to `b` (`OrthonormalBasis.map_prodEquivOfBasis`), so it
carries the orientation of that basis to the orientation of `b`.
-/

public section

open Module

namespace OrthonormalBasis

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (e : Basis (Fin n) ℝ F)

/-- The continuous linear equivalence of `F` with the orthogonal complement of the last vector of
`b` that sends the basis `e` of `F` to `b.orthogonalLast`. -/
noncomputable def orthogonalLastEquivOfBasis : F ≃L[ℝ] (ℝ ∙ b (Fin.last n))ᗮ :=
  haveI := e.finiteDimensional_of_finite
  (e.equiv b.orthogonalLast.toBasis (Equiv.refl _)).toContinuousLinearEquiv

@[simp]
theorem orthogonalLastEquivOfBasis_apply_basis (i : Fin n) :
    b.orthogonalLastEquivOfBasis e (e i) = b.orthogonalLast i :=
  (e.equiv_apply i b.orthogonalLast.toBasis (Equiv.refl _)).trans (by simp)

theorem map_orthogonalLastEquivOfBasis :
    e.map (b.orthogonalLastEquivOfBasis e).toLinearEquiv = b.orthogonalLast.toBasis :=
  (e.map_equiv b.orthogonalLast.toBasis (Equiv.refl _)).trans b.orthogonalLast.toBasis.reindex_refl

/-- The continuous linear equivalence `F × ℝ ≃L[ℝ] E` that sends `(e i, 0)` to `b i.castSucc` and
`(0, 1)` to the last vector of `b`; it sends `(x, t)` to `b.orthogonalLastEquivOfBasis e x` plus
`t` times the last vector of `b` (`OrthonormalBasis.prodEquivOfBasis_apply`). -/
noncomputable def prodEquivOfBasis : (F × ℝ) ≃L[ℝ] E :=
  haveI := e.finiteDimensional_of_finite
  (((e.prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv).equiv b.toBasis
    (Equiv.refl _)).toContinuousLinearEquiv

theorem map_prodEquivOfBasis :
    ((e.prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv).map
      (b.prodEquivOfBasis e).toLinearEquiv = b.toBasis :=
  (Basis.map_equiv _ b.toBasis (Equiv.refl _)).trans b.toBasis.reindex_refl

theorem prodEquivOfBasis_apply (x : F) (t : ℝ) :
    b.prodEquivOfBasis e (x, t) = b.orthogonalLastEquivOfBasis e x + t • b (Fin.last n) := by
  set B := (e.prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv
  have hB : ∀ i, b.prodEquivOfBasis e (B i) = b i := fun i ↦
    (B.equiv_apply i b.toBasis (Equiv.refl _)).trans (by simp)
  have h₀ : (b.prodEquivOfBasis e : F × ℝ →L[ℝ] E).toLinearMap ∘ₗ LinearMap.inl ℝ F ℝ =
      (ℝ ∙ b (Fin.last n))ᗮ.subtype ∘ₗ
        (b.orthogonalLastEquivOfBasis e : F →L[ℝ] (ℝ ∙ b (Fin.last n))ᗮ).toLinearMap := by
    refine e.ext fun j ↦ ?_
    have h₁ : b.prodEquivOfBasis e (e j, 0) = b j.castSucc := by
      rw [← hB]; simp [B, Basis.prod_apply]
    simp [h₁]
  have h₁ : b.prodEquivOfBasis e (0, 1) = b (Fin.last n) := by
    rw [← hB]; simp [B, Basis.prod_apply]
  have hx : b.prodEquivOfBasis e (x, 0) = b.orthogonalLastEquivOfBasis e x :=
    LinearMap.congr_fun h₀ x
  rw [← hx, ← h₁, ← map_smul, ← map_add, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
    Prod.mk_add_mk, add_zero, zero_add]

end OrthonormalBasis

end
