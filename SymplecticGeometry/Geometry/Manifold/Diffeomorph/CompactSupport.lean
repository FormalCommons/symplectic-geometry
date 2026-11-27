/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import SymplecticGeometry.Analysis.Calculus.ContDiff.Lipschitz

/-!
# Diffeomorphisms of a normed space that are the identity off a compact set

A diffeomorphism `Φ` of a real normed space that is the identity off a compact set `C` has an
inverse that is the identity off `C` too. So both `Φ` and `Φ.symm` are Lipschitz, by
`ContDiff.exists_lipschitzWith_of_forall_notMem_eq_self`, and the derivative of `Φ.symm` is
bounded by its Lipschitz constant (Mathlib's `norm_fderiv_le_of_lipschitz`).

## Main results

* `Diffeomorph.exists_lipschitzWith_and_norm_fderiv_symm_le`: such a diffeomorphism is
  `L`-Lipschitz and its inverse has derivative of norm at most `L`, for one constant `L ≥ 1`.
-/

public section

open scoped Manifold NNReal

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-- A `C^n` diffeomorphism `Φ`, `n ≠ 0`, of a real normed space that is the identity off a compact
set is `L`-Lipschitz, and the derivative of its inverse has norm at most `L` everywhere, for one
constant `L ≥ 1`. -/
theorem exists_lipschitzWith_and_norm_fderiv_symm_le (Φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hn : n ≠ 0) {C : Set E} (hC : IsCompact C) (hΦ : ∀ x ∉ C, Φ x = x) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ LipschitzWith L Φ ∧ ∀ y, ‖fderiv ℝ Φ.symm y‖ ≤ L := by
  obtain ⟨M₁, hM₁⟩ := Φ.contDiff.exists_lipschitzWith_of_forall_notMem_eq_self hn hC hΦ
  obtain ⟨M₂, hM₂⟩ := Φ.symm.contDiff.exists_lipschitzWith_of_forall_notMem_eq_self hn hC
    fun y hy ↦ Φ.toEquiv.symm_apply_eq.2 (hΦ y hy).symm
  refine ⟨max (max M₁ M₂) 1, le_max_right _ _, hM₁.weaken (by simp), fun y ↦ ?_⟩
  exact (norm_fderiv_le_of_lipschitz ℝ hM₂).trans (by simp)

end Diffeomorph

end
