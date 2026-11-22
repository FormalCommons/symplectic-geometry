/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Complexification

/-!
# Complexification of real-linear maps of smooth forms

Through `TauCeti.SmoothForm.complexificationEquiv`, complex forms are the base change to `ℂ` of
real forms. A real-linear map `f` from real `k`-forms to real `l`-forms therefore extends to a
complex-linear map `TauCeti.SmoothForm.complexifyₗ f` of complex forms, the base change of `f`.
This file shows that it applies `f` to the real and imaginary parts of a complex form, that it
extends `f` from real forms, and that it respects identities and composition. Tau Ceti proves
the first two facts for the exterior derivative and for pullback,
`TauCeti.SmoothForm.complexificationEquiv_baseChange_mextDerivₗ` and
`TauCeti.SmoothForm.complexificationEquiv_baseChange_mpullback`; here they hold for an arbitrary
real-linear map.

It also records that a complex form is determined by its real and imaginary parts.

## Main definitions

* `TauCeti.SmoothForm.complexifyₗ`: the complex-linear extension of a real-linear map of real
  forms to complex forms.

## Main results

* `TauCeti.SmoothForm.complexifyₗ_apply`: `complexifyₗ f φ = f (Re φ) + i f (Im φ)`.
* `TauCeti.SmoothForm.mapCoeff_reCLM_complexifyₗ` and
  `TauCeti.SmoothForm.mapCoeff_imCLM_complexifyₗ`: its real and imaginary parts.
* `TauCeti.SmoothForm.complexifyₗ_mapCoeff_ofRealCLM`: on real forms it is `f`.
* `TauCeti.SmoothForm.complexifyₗ_id` and `TauCeti.SmoothForm.complexifyₗ_comp`.
* `TauCeti.SmoothForm.eq_zero_iff_realPart_imaginaryPart`: a complex form vanishes exactly when
  its real and imaginary parts do.
-/

public section

noncomputable section

open scoped Manifold TensorProduct

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k l n : ℕ}

/-! ### Real and imaginary parts of real forms -/

/-- The real part of a real form, viewed as a complex form, is the form itself. -/
@[simp]
theorem mapCoeff_reCLM_mapCoeff_ofRealCLM (α : SmoothForm I M ℝ k) :
    mapCoeff Complex.reCLM (mapCoeff Complex.ofRealCLM α) = α := by
  simpa using realPart_ofReal_add_I_smul_ofReal α 0

/-- The imaginary part of a real form, viewed as a complex form, is zero. -/
@[simp]
theorem mapCoeff_imCLM_mapCoeff_ofRealCLM (α : SmoothForm I M ℝ k) :
    mapCoeff Complex.imCLM (mapCoeff Complex.ofRealCLM α) = 0 := by
  simpa using imaginaryPart_ofReal_add_I_smul_ofReal α 0

/-- A complex form vanishes exactly when its real and imaginary parts vanish. -/
theorem eq_zero_iff_realPart_imaginaryPart (ω : SmoothForm I M ℂ k) :
    ω = 0 ↔ mapCoeff Complex.reCLM ω = 0 ∧ mapCoeff Complex.imCLM ω = 0 := by
  refine ⟨fun h ↦ by simp [h], fun ⟨hre, him⟩ ↦ ?_⟩
  rw [← ofReal_realPart_add_I_smul_ofReal_imaginaryPart ω, hre, him, map_zero, smul_zero,
    add_zero]

/-! ### The complexification of a real-linear map -/

/-- The complexification of a real-linear map `f` of real forms: the complex-linear map of
complex forms that is the base change of `f` to `ℂ`, read through `complexificationEquiv`. -/
def complexifyₗ (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) :
    SmoothForm I M ℂ k →ₗ[ℂ] SmoothForm I M ℂ l :=
  complexificationEquiv.toLinearMap ∘ₗ f.baseChange ℂ ∘ₗ complexificationEquiv.symm.toLinearMap

/-- The complexification of `f` is its base change, read through `complexificationEquiv`. -/
theorem complexifyₗ_def (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) :
    complexifyₗ f =
      complexificationEquiv.toLinearMap ∘ₗ f.baseChange ℂ ∘ₗ
        complexificationEquiv.symm.toLinearMap :=
  (rfl)

/-- Read through `complexificationEquiv`, the complexification of `f` is the base change of `f`. -/
theorem complexifyₗ_complexificationEquiv (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (u : ℂ ⊗[ℝ] SmoothForm I M ℝ k) :
    complexifyₗ f (complexificationEquiv u) = complexificationEquiv (f.baseChange ℂ u) := by
  rw [complexifyₗ_def, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The complexification of `f` sends `φ` to `f (Re φ) + i f (Im φ)`. -/
theorem complexifyₗ_apply (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (φ : SmoothForm I M ℂ k) :
    complexifyₗ f φ =
      mapCoeff Complex.ofRealCLM (f (mapCoeff Complex.reCLM φ)) +
        Complex.I • mapCoeff Complex.ofRealCLM (f (mapCoeff Complex.imCLM φ)) := by
  simp [complexifyₗ_def]

/-- The real part of the complexification of `f` is `f` of the real part. -/
@[simp]
theorem mapCoeff_reCLM_complexifyₗ (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.reCLM (complexifyₗ f φ) = f (mapCoeff Complex.reCLM φ) := by
  rw [complexifyₗ_apply, realPart_ofReal_add_I_smul_ofReal]

/-- The imaginary part of the complexification of `f` is `f` of the imaginary part. -/
@[simp]
theorem mapCoeff_imCLM_complexifyₗ (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.imCLM (complexifyₗ f φ) = f (mapCoeff Complex.imCLM φ) := by
  rw [complexifyₗ_apply, imaginaryPart_ofReal_add_I_smul_ofReal]

/-- On real forms, the complexification of `f` is `f`. -/
@[simp]
theorem complexifyₗ_mapCoeff_ofRealCLM (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l)
    (α : SmoothForm I M ℝ k) :
    complexifyₗ f (mapCoeff Complex.ofRealCLM α) = mapCoeff Complex.ofRealCLM (f α) := by
  rw [complexifyₗ_apply, mapCoeff_reCLM_mapCoeff_ofRealCLM, mapCoeff_imCLM_mapCoeff_ofRealCLM,
    map_zero, map_zero, smul_zero, add_zero]

/-- The complexification of the identity is the identity. -/
@[simp]
theorem complexifyₗ_id : complexifyₗ (LinearMap.id : SmoothForm I M ℝ k →ₗ[ℝ] _) =
    LinearMap.id :=
  LinearMap.ext fun φ ↦ by simp [complexifyₗ_apply]

/-- Complexification respects composition. -/
theorem complexifyₗ_comp (g : SmoothForm I M ℝ l →ₗ[ℝ] SmoothForm I M ℝ n)
    (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) :
    complexifyₗ (g ∘ₗ f) = complexifyₗ g ∘ₗ complexifyₗ f := by
  refine LinearMap.ext fun φ ↦ ?_
  rw [LinearMap.comp_apply, complexifyₗ_apply (g ∘ₗ f), complexifyₗ_apply g,
    mapCoeff_reCLM_complexifyₗ, mapCoeff_imCLM_complexifyₗ, LinearMap.comp_apply,
    LinearMap.comp_apply]

end TauCeti.SmoothForm

end

end
