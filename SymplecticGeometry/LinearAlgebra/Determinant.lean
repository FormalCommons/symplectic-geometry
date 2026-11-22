/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of conjugates written as composites of linear equivalences

Mathlib's `LinearMap.det_conj` says that conjugating an endomorphism by a linear equivalence keeps
its determinant, but it is stated with `∘ₗ`, and `simp` keeps composites `LinearEquiv.trans` of
linear equivalences in their `trans` form. This file states the same fact for automorphisms
written as `trans` chains and read as linear maps, so that `simp` can use it.

## Main results

* `LinearEquiv.det_symm_trans_trans` (`@[simp]`): for `e : N ≃ₗ[R] M` and `g : N ≃ₗ[R] N`, the
  automorphism `e ∘ g ∘ e⁻¹` of `M`, written `e.symm.trans (g.trans e)`, has the determinant
  of `g`;
* `LinearEquiv.det_trans_symm`: for `e f : N ≃ₗ[R] M`, the automorphisms `e⁻¹ ∘ f` of `N` and
  `f ∘ e⁻¹` of `M` have the same determinant.

Both are corollaries of `LinearMap.det_conj`.
-/

public section

namespace LinearEquiv

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Conjugating an automorphism `g` of `N` by a linear equivalence `e : N ≃ₗ[R] M` does not
change its determinant: `det (e ∘ g ∘ e⁻¹) = det g`. -/
@[simp]
theorem det_symm_trans_trans (e : N ≃ₗ[R] M) (g : N ≃ₗ[R] N) :
    LinearMap.det (e.symm.trans (g.trans e) : M →ₗ[R] M) = LinearMap.det (g : N →ₗ[R] N) :=
  LinearMap.det_conj (g : N →ₗ[R] N) e

/-- For linear equivalences `e f : N ≃ₗ[R] M`, the automorphism `e⁻¹ ∘ f` of `N` and the
automorphism `f ∘ e⁻¹` of `M` have the same determinant. -/
theorem det_trans_symm (e f : N ≃ₗ[R] M) :
    LinearMap.det (f.trans e.symm : N →ₗ[R] N) =
      LinearMap.det (e.symm.trans f : M →ₗ[R] M) := by
  rw [← e.det_symm_trans_trans]
  congr 2
  ext v
  simp

end LinearEquiv

end
