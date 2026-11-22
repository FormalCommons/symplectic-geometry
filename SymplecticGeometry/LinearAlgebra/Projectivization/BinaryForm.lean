/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.Algebra.Polynomial.Homogenize
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Zeros of binary forms on the projective line

A binary form `F` of degree `d` over an algebraically closed field `K` whose gradient vanishes at
no nonzero zero has exactly `d` zeros on the projective line `ℙ K (Fin 2 → K)`: such a form has no
squared linear factor, so it is a product of `d` pairwise non-proportional linear forms, each of
which vanishes at exactly one point of the line.

## Main results

* `MvPolynomial.IsHomogeneous.ncard_setOf_eval_rep_eq_zero`: the zeros of such a form on
  `ℙ K (Fin 2 → K)` are `d` in number.

The factorization into linear forms is Tau Ceti's
`MvPolynomial.IsHomogeneous.exists_linear_factors`, and the zeros of the linear forms are
compared by Tau Ceti's `Projectivization.mk_eq_mk_iff_forall_mul_eq`.
-/

public section

open Finset
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

namespace MvPolynomial.IsHomogeneous

variable [IsAlgClosed K]

/-- A binary form of degree `d` over an algebraically closed field, some partial derivative of
which is nonzero at a representative of each of its zeros on the projective line, has exactly
`d` such zeros. -/
theorem ncard_setOf_eval_rep_eq_zero {F : MvPolynomial (Fin 2) K} {d : ℕ}
    (hF : F.IsHomogeneous d)
    (hsing : ∀ p : ℙ K (Fin 2 → K), eval p.rep F = 0 → ∃ i, eval p.rep (pderiv i F) ≠ 0) :
    {p : ℙ K (Fin 2 → K) | eval p.rep F = 0}.ncard = d := by
  -- `F` has no squared linear factor: it would make the gradient vanish where the factor does.
  have hsq : ∀ a b : K, (a, b) ≠ (0, 0) → ¬(C a * X 0 + C b * X 1) ^ 2 ∣ F := by
    rintro a b hab ⟨G, rfl⟩
    have hv : ![b, -a] ≠ 0 := fun h ↦ hab <| by
      have := congrFun h 0
      have := congrFun h 1
      simp_all
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K _ hv
    have hℓ : eval (Projectivization.mk K _ hv).rep (C a * X 0 + C b * X 1) = 0 := by
      rw [← hc]; simp [Units.smul_def]; ring
    obtain ⟨i, hi⟩ := hsing (Projectivization.mk K _ hv) (by simp [hℓ])
    exact hi (by simp [hℓ])
  obtain ⟨a, ha, T, hT, hpair, hform, rfl⟩ :=
    hF.exists_linear_factors IsAlgClosed.card_roots_eq_natDegree hsq
  -- Each linear form of the factorization is nonzero, and vanishes at exactly one point.
  have hne : ∀ ℓ ∈ T, ![ℓ.2, -ℓ.1] ≠ 0 := fun ℓ hℓ h ↦ by
    have := congrFun h 0
    have := congrFun h 1
    rcases hform ℓ hℓ with rfl | ⟨α, -, rfl⟩ <;> simp_all
  have heval (v : Fin 2 → K) :
      eval v (C a * ∏ ℓ ∈ T, (C ℓ.1 * X 0 + C ℓ.2 * X 1)) =
        a * ∏ ℓ ∈ T, (ℓ.1 * v 0 + ℓ.2 * v 1) := by
    simp
  let φ : T → ℙ K (Fin 2 → K) := fun ℓ ↦ Projectivization.mk K _ (hne ℓ.val ℓ.property)
  have hφ : {p : ℙ K (Fin 2 → K) | eval p.rep (C a * ∏ ℓ ∈ T, (C ℓ.1 * X 0 + C ℓ.2 * X 1)) = 0} =
      Set.range φ := by
    ext p
    simp only [Set.mem_ofPred_eq, heval, mul_eq_zero, ha, false_or, prod_eq_zero_iff,
      Set.mem_range, Subtype.exists, φ]
    constructor
    · rintro ⟨ℓ, hℓ, h⟩
      refine ⟨ℓ, hℓ, ?_⟩
      rw [← p.mk_rep]
      refine (Projectivization.mk_eq_mk_iff_forall_mul_eq _ _).2 ?_
      simp only [Fin.forall_fin_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        neg_mul, true_and, and_true]
      exact ⟨by linear_combination h, by linear_combination -h⟩
    · rintro ⟨ℓ, hℓ, rfl⟩
      refine ⟨ℓ, hℓ, ?_⟩
      obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K _ (hne ℓ hℓ)
      rw [← hc]
      simp [Units.smul_def]
      ring
  have hinj : Function.Injective φ := by
    rintro ⟨ℓ, hℓ⟩ ⟨ℓ', hℓ'⟩ h
    by_contra hne'
    refine hpair hℓ hℓ' (fun h' ↦ hne' (Subtype.ext h')) ?_
    have := (Projectivization.mk_eq_mk_iff_forall_mul_eq _ _).1 h 0 1
    simp at this
    linear_combination -this
  rw [hφ, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_coe, hT]

end MvPolynomial.IsHomogeneous

end
