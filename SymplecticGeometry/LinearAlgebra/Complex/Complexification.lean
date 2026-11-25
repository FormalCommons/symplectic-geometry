/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Conjugate
public import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Complex.RealForm

/-!
# The complexification of a complex vector space

Let `W` be a complex vector space, seen as a real one. Its complexification `ℂ ⊗[ℝ] W` is the
direct sum of `W` and of its conjugate: `z ⊗ w ↦ (z • w, z̄ • w)` is a complex-linear isomorphism
`ℂ ⊗[ℝ] W ≃ W × Conjugate W`. In the real coordinates `u = 1 ⊗ x + i ⊗ y` of the
complexification it is `(x, y) ↦ (x + i y, x - i y)`, with inverse
`(a, c) ↦ ((a + c) / 2, i (c - a) / 2)`.

## Main definitions

* `TauCeti.Conjugate.complexificationEquiv`: the complex-linear isomorphism
  `ℂ ⊗[ℝ] W ≃ W × Conjugate W`, `z ⊗ w ↦ (z • w, z̄ • w)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §15 (the complexification of a complex vector space is isomorphic to the
  sum of the space and its conjugate).
-/

public section

noncomputable section

open ComplexConjugate Complex
open scoped TensorProduct

namespace TauCeti.Conjugate

variable (W : Type*) [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]

/-- The complex-linear isomorphism `ℂ ⊗[ℝ] W ≃ W × Conjugate W`, `z ⊗ w ↦ (z • w, z̄ • w)`,
for a complex vector space `W`. Its inverse sends `(a, c)` to the vector with real part
`(a + c) / 2` and imaginary part `i (c - a) / 2`. -/
def complexificationEquiv : ℂ ⊗[ℝ] W ≃ₗ[ℂ] W × Conjugate W where
  __ := LinearMap.prod ((LinearMap.id : W →ₗ[ℝ] W).liftBaseChange ℂ)
    ((toConjₗ' : W ≃ₗ[ℝ] Conjugate W).toLinearMap.liftBaseChange ℂ)
  invFun p := 1 ⊗ₜ[ℝ] ((2⁻¹ : ℂ) • (p.1 + ofConj p.2)) +
    I ⊗ₜ[ℝ] ((2⁻¹ : ℂ) • (I • ofConj p.2 - I • p.1))
  left_inv u := by
    refine complexification_ext ?_ ?_ <;>
    · simp [LinearMap.liftBaseChange_complex_apply, smul_add, smul_smul]
      module
  right_inv p := by
    ext
    · simp [LinearMap.liftBaseChange_complex_apply, smul_add, smul_sub, smul_smul]
      linear_combination (norm := module) I_sq • ((2⁻¹ : ℂ) • (ofConj p.2 - p.1))
    · apply ofConj.injective
      simp [LinearMap.liftBaseChange_complex_apply, smul_add, smul_sub, smul_smul]
      linear_combination (norm := module) I_sq • ((2⁻¹ : ℂ) • (p.1 - ofConj p.2))

variable {W}

/-- On a pure tensor, `complexificationEquiv W` is `z ⊗ w ↦ (z • w, z̄ • w)`. -/
@[simp]
theorem complexificationEquiv_tmul (z : ℂ) (w : W) :
    complexificationEquiv W (z ⊗ₜ[ℝ] w) = (z • w, toConj (conj z • w)) := by
  simp [complexificationEquiv]

/-- The first component of `complexificationEquiv W u` is `x + i y`, for `x` and `y` the real
and imaginary parts of `u`. -/
@[simp]
theorem complexificationEquiv_apply_fst (u : ℂ ⊗[ℝ] W) :
    (complexificationEquiv W u).1 = realPart W u + I • imaginaryPart W u := by
  simp [complexificationEquiv, LinearMap.liftBaseChange_complex_apply]

/-- The second component of `complexificationEquiv W u`, read in `W`, is `x - i y`, for `x` and
`y` the real and imaginary parts of `u`. -/
@[simp]
theorem ofConj_complexificationEquiv_apply_snd (u : ℂ ⊗[ℝ] W) :
    ofConj (complexificationEquiv W u).2 = realPart W u - I • imaginaryPart W u := by
  simp [complexificationEquiv, LinearMap.liftBaseChange_complex_apply, sub_eq_add_neg]

/-- The inverse of `complexificationEquiv W`, in real coordinates. -/
theorem complexificationEquiv_symm_apply (p : W × Conjugate W) :
    (complexificationEquiv W).symm p = 1 ⊗ₜ[ℝ] ((2⁻¹ : ℂ) • (p.1 + ofConj p.2)) +
      I ⊗ₜ[ℝ] ((2⁻¹ : ℂ) • (I • ofConj p.2 - I • p.1)) :=
  (rfl)

/-- The real part of `(complexificationEquiv W).symm (a, c)` is `(a + c) / 2`. -/
@[simp]
theorem realPart_complexificationEquiv_symm (p : W × Conjugate W) :
    realPart W ((complexificationEquiv W).symm p) = (2⁻¹ : ℂ) • p.1 + (2⁻¹ : ℂ) • ofConj p.2 := by
  simp [complexificationEquiv_symm_apply]

/-- The imaginary part of `(complexificationEquiv W).symm (a, c)` is `i (c - a) / 2`. -/
@[simp]
theorem imaginaryPart_complexificationEquiv_symm (p : W × Conjugate W) :
    imaginaryPart W ((complexificationEquiv W).symm p) =
      (2⁻¹ : ℂ) • I • ofConj p.2 - (2⁻¹ : ℂ) • I • p.1 := by
  simp [complexificationEquiv_symm_apply, smul_sub]

end TauCeti.Conjugate

end
