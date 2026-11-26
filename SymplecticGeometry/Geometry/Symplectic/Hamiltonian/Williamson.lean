/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
import SymplecticGeometry.LinearAlgebra.Matrix.Rank
import TauCeti.Analysis.InnerProductSpace.Nondegenerate

/-!
# Orthogonal Darboux bases and the uniqueness of Williamson's frequencies

Two complements to Tau Ceti's Williamson theorem
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`), which writes a
positive definite quadratic form `Q` on a symplectic vector space `(V, ω)` as `∑ₖ νₖ Iₖ` for a
Darboux basis `(q₁, p₁, …, qₙ, pₙ)`, positive frequencies `νₖ` and the elliptic blocks
`Iₖ = (xₖ² + yₖ²) / 2`.

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_orthogonal`: if `V` is a real inner product
  space of finite dimension, every symplectic form has a Darboux basis whose vectors are pairwise
  orthogonal, with `‖qₖ‖ = ‖pₖ‖`. This is Williamson's theorem for `Q v = ⟪v, v⟫`, since
  `Q (qₖ) = Q (pₖ) = νₖ / 2` and the polar form of `∑ₖ νₖ Iₖ` vanishes on distinct basis vectors.
* `TauCeti.SymplecticForm.IsDarbouxBasis.exists_perm_eq_of_sum_smul_elliptic_eq`: the positive
  frequencies are determined by `Q` up to a permutation. The square of the Hamiltonian
  endomorphism `A_Q` acts on `span(qₖ, pₖ)` as `-νₖ²`, so for `t > 0` the rank of
  `A_Q ^ 2 + t ^ 2` counts the basis vectors with `νₖ ≠ t`; it depends only on `Q`.

The results extend Tau Ceti's file of the same path, in its namespace.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.4
  (Lemmas 2.4.5 and 2.4.6)
-/

public section

open Module

namespace TauCeti.SymplecticForm

section Orthogonal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

open scoped RealInnerProductSpace

/-- **Orthogonal Darboux bases.** If `V` is a real inner product space of finite dimension, a
symplectic form on `V` has a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`, with `qₖ = b (k, 0)` and
`pₖ = b (k, 1)`, whose vectors are pairwise orthogonal and satisfy `‖qₖ‖ = ‖pₖ‖`. -/
theorem exists_isDarbouxBasis_orthogonal (ω : SymplecticForm V) :
    ∃ (m : ℕ) (b : Basis (Fin m × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      (Pairwise fun k l ↦ ⟪b k, b l⟫ = 0) ∧ ∀ k, ‖b (k, 0)‖ = ‖b (k, 1)‖ := by
  set Q : QuadraticForm ℝ V := LinearMap.BilinMap.toQuadraticMap (innerₗ V) with hQdef
  obtain ⟨m, b, ν, hb, -, hQe⟩ :=
    ω.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef TauCeti.posDef_toQuadraticMap_innerₗ
  refine ⟨m, b, hb, fun i j hij ↦ ?_, fun k ↦ ?_⟩
  · have h := ω.apply_hamiltonianEnd Q (b i) (b j)
    rw [hQdef, LinearMap.BilinMap.polar_toQuadraticMap, ← hQdef, hQe] at h
    obtain ⟨k, a⟩ := i
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_fst] at h
      simp [hb.apply_snd, Ne.symm hij] at h
      linarith [real_inner_comm (b j) (b (k, 0))]
    · rw [hb.hamiltonianEnd_sum_smul_elliptic_apply_snd] at h
      simp [hb.apply_fst, Ne.symm hij] at h
      linarith [real_inner_comm (b j) (b (k, 1))]
  · have hval : ∀ a, ‖b (k, a)‖ ^ 2 = ν k / 2 := fun a ↦ by
      have h : Q (b (k, a)) = ν k / 2 := by
        rw [hQe]
        fin_cases a <;> simp [Finsupp.single_apply, mul_ite, div_eq_mul_inv]
      rwa [hQdef, LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply,
        real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ((hval 0).trans (hval 1).symm)

end Orthogonal

section Uniqueness

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {m : ℕ}

/-- In a Darboux basis `b`, for `t > 0` and positive frequencies `ν`, the rank of
`A ^ 2 + t ^ 2`, `A` the Hamiltonian endomorphism of `∑ₖ νₖ Iₖ`, counts the basis vectors whose
frequency differs from `t`. -/
private theorem IsDarbouxBasis.finrank_range_sq_add_sq {b : Basis (Fin m × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) {ν : Fin m → ℝ} (hν : ∀ k, 0 < ν k) {t : ℝ} (ht : 0 < t) :
    finrank ℝ (LinearMap.range (ω.hamiltonianEnd (∑ k, ν k • elliptic b k) ^ 2 +
        t ^ 2 • (1 : Module.End ℝ V))) =
      Fintype.card {i : Fin m × Fin 2 // ν i.1 ≠ t} := by
  rw [LinearMap.finrank_range_eq_card_of_apply_basis_eq_smul b (d := fun i ↦ t ^ 2 - ν i.1 ^ 2)]
  · refine Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
    have := hν i.1
    rw [sub_ne_zero, Ne, Ne, sq_eq_sq₀ ht.le this.le, eq_comm]
  · rintro ⟨k, a⟩
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals
      simp only [LinearMap.add_apply, pow_two, mul_apply_eq_comp, LinearMap.smul_apply,
        one_apply_eq_self, hb.hamiltonianEnd_sum_smul_elliptic_apply_fst, map_smul,
        hb.hamiltonianEnd_sum_smul_elliptic_apply_snd]
      module

/-- For `t > 0` and positive frequencies `ν`, the number of `k` with `νₖ = t` is half the
codimension of the range of `A ^ 2 + t ^ 2`, `A` the Hamiltonian endomorphism of `∑ₖ νₖ Iₖ`. -/
private theorem IsDarbouxBasis.two_mul_card_eq {b : Basis (Fin m × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) {ν : Fin m → ℝ} (hν : ∀ k, 0 < ν k) {t : ℝ} (ht : 0 < t) :
    2 * Fintype.card {k // ν k = t} + finrank ℝ (LinearMap.range
        (ω.hamiltonianEnd (∑ k, ν k • elliptic b k) ^ 2 + t ^ 2 • (1 : Module.End ℝ V))) =
      2 * m := by
  rw [hb.finrank_range_sq_add_sq hν ht, Fintype.card_subtype_compl,
    ← Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun k ↦ ν k = t)).symm]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_prod]
  have : Fintype.card {i : Fin m × Fin 2 // ν i.1 = t} ≤ m * 2 := by
    simpa using Fintype.card_subtype_le (fun i : Fin m × Fin 2 ↦ ν i.1 = t)
  rw [← Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun k ↦ ν k = t)).symm,
    Fintype.card_prod, Fintype.card_fin] at this
  omega

/-- **Uniqueness of Williamson's frequencies.** If `∑ₖ νₖ Iₖ = ∑ₖ μₖ Jₖ` for two Darboux bases
of `(V, ω)` with elliptic blocks `Iₖ` and `Jₖ` and positive frequencies `ν`, `μ`, then `μ` is a
permutation of `ν`. -/
theorem IsDarbouxBasis.exists_perm_eq_of_sum_smul_elliptic_eq {b c : Basis (Fin m × Fin 2) ℝ V}
    (hb : ω.IsDarbouxBasis b) (hc : ω.IsDarbouxBasis c) {ν μ : Fin m → ℝ} (hν : ∀ k, 0 < ν k)
    (hμ : ∀ k, 0 < μ k) (h : ∑ k, ν k • elliptic b k = ∑ k, μ k • elliptic c k) :
    ∃ σ : Equiv.Perm (Fin m), μ = ν ∘ σ := by
  have hcard : ∀ t, Fintype.card {k // μ k = t} = Fintype.card {k // ν k = t} := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · have hμt (k : {k // μ k = t}) : False := not_lt.2 ht (k.property ▸ hμ k.val)
      have hνt (k : {k // ν k = t}) : False := not_lt.2 ht (k.property ▸ hν k.val)
      rw [Fintype.card_eq_zero_iff.2 ⟨hμt⟩, Fintype.card_eq_zero_iff.2 ⟨hνt⟩]
    · have h₁ := hb.two_mul_card_eq hν ht
      have h₂ := hc.two_mul_card_eq hμ ht
      rw [← h] at h₂
      omega
  let σ := Equiv.ofFiberEquiv fun t ↦ Fintype.equivOfCardEq (hcard t)
  exact ⟨σ, funext fun k ↦ (Equiv.ofFiberEquiv_map _ k).symm⟩

end Uniqueness

end TauCeti.SymplecticForm

end
