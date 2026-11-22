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
written as `trans` chains and read as linear maps.

Since `LinearEquiv.trans_assoc` is not a `simp` lemma, the conjugate `e ∘ g ∘ e⁻¹` gets one
`simp` lemma for each bracketing of its `trans` chain: the left-nested
`(e.symm.trans g).trans e`, which `e.symm ≪≫ₗ g ≪≫ₗ e` denotes and which `simp` makes of
`↑e ∘ₗ ↑g ∘ₗ ↑e.symm`, and the right-nested `e.symm.trans (g.trans e)`.

## Main results

* `LinearEquiv.det_coe_conj` (`@[simp]`) and `LinearEquiv.det_coe_symm_trans_trans`
  (`@[simp]`): for `e : N ≃ₗ[R] M` and `g : N ≃ₗ[R] N`, the automorphism `e ∘ g ∘ e⁻¹` of `M`,
  written `(e.symm.trans g).trans e` or `e.symm.trans (g.trans e)`, has the determinant of `g`;
* `LinearEquiv.det_coe_trans_symm`: for `e f : N ≃ₗ[R] M`, the automorphisms `e⁻¹ ∘ f` of `N`
  and `f ∘ e⁻¹` of `M` have the same determinant.

All are corollaries of `LinearMap.det_conj`. `LinearEquiv.det_coe_conj` has the shape of
Mathlib's `LinearEquiv.det_conj`, which is about the unit-valued `LinearEquiv.det`.
-/

public section

namespace LinearEquiv

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Conjugating an automorphism `g` of `N` by a linear equivalence `e : N ≃ₗ[R] M` does not
change its determinant: `det (e ∘ g ∘ e⁻¹) = det g`, for the conjugate written as the
left-nested chain `(e.symm.trans g).trans e`. -/
@[simp]
theorem det_coe_conj (e : N ≃ₗ[R] M) (g : N ≃ₗ[R] N) :
    LinearMap.det ((e.symm.trans g).trans e : M →ₗ[R] M) = LinearMap.det (g : N →ₗ[R] N) :=
  LinearMap.det_conj (g : N →ₗ[R] N) e

/-- Conjugating an automorphism `g` of `N` by a linear equivalence `e : N ≃ₗ[R] M` does not
change its determinant: `det (e ∘ g ∘ e⁻¹) = det g`, for the conjugate written as the
right-nested chain `e.symm.trans (g.trans e)`. -/
@[simp]
theorem det_coe_symm_trans_trans (e : N ≃ₗ[R] M) (g : N ≃ₗ[R] N) :
    LinearMap.det (e.symm.trans (g.trans e) : M →ₗ[R] M) = LinearMap.det (g : N →ₗ[R] N) :=
  LinearMap.det_conj (g : N →ₗ[R] N) e

/-- For linear equivalences `e f : N ≃ₗ[R] M`, the automorphism `e⁻¹ ∘ f` of `N` and the
automorphism `f ∘ e⁻¹` of `M` have the same determinant. -/
theorem det_coe_trans_symm (e f : N ≃ₗ[R] M) :
    LinearMap.det (f.trans e.symm : N →ₗ[R] N) =
      LinearMap.det (e.symm.trans f : M →ₗ[R] M) := by
  rw [← e.det_coe_symm_trans_trans]
  congr 2
  ext v
  simp

end LinearEquiv

end
