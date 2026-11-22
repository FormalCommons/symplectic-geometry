/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Complexification

/-!
# Base change of real-linear maps of smooth forms

Through `TauCeti.SmoothForm.complexificationEquiv`, a real-linear map `f` from real `k`-forms to
real `l`-forms gives, by base change to `ℂ`, a complex-linear map of complex forms. This file
shows that this map applies `f` to the real and imaginary parts of a complex form, and that it
extends `f` from real forms. These are the facts that Tau Ceti proves for the exterior
derivative and for pullback, `TauCeti.SmoothForm.complexificationEquiv_baseChange_mextDerivₗ`
and `TauCeti.SmoothForm.complexificationEquiv_baseChange_mpullback`, stated here for an
arbitrary real-linear map.

## Main results

* `TauCeti.SmoothForm.complexificationEquiv_baseChange_complexificationEquiv_symm`: the base
  change of `f` sends `φ` to `f (Re φ) + i f (Im φ)`.
* `TauCeti.SmoothForm.mapCoeff_reCLM_complexificationEquiv_baseChange` and
  `TauCeti.SmoothForm.mapCoeff_imCLM_complexificationEquiv_baseChange`: its real and imaginary
  parts.
* `TauCeti.SmoothForm.complexificationEquiv_baseChange_symm_mapCoeff_ofRealCLM`: on real forms
  it is `f`.
-/

public section

noncomputable section

open scoped Manifold TensorProduct

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k l : ℕ}

/-- The base change of a real-linear map `f` of real forms, read on complex forms through
`complexificationEquiv`, applies `f` to the real and imaginary parts. -/
theorem complexificationEquiv_baseChange_complexificationEquiv_symm
    (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) (φ : SmoothForm I M ℂ k) :
    complexificationEquiv (f.baseChange ℂ (complexificationEquiv.symm φ)) =
      mapCoeff Complex.ofRealCLM (f (mapCoeff Complex.reCLM φ)) +
        Complex.I • mapCoeff Complex.ofRealCLM (f (mapCoeff Complex.imCLM φ)) := by
  simp

/-- The real part of the base change of `f`, read on complex forms, is `f` of the real part. -/
theorem mapCoeff_reCLM_complexificationEquiv_baseChange
    (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.reCLM
        (complexificationEquiv (f.baseChange ℂ (complexificationEquiv.symm φ))) =
      f (mapCoeff Complex.reCLM φ) := by
  rw [complexificationEquiv_baseChange_complexificationEquiv_symm,
    realPart_ofReal_add_I_smul_ofReal]

/-- The imaginary part of the base change of `f`, read on complex forms, is `f` of the imaginary
part. -/
theorem mapCoeff_imCLM_complexificationEquiv_baseChange
    (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) (φ : SmoothForm I M ℂ k) :
    mapCoeff Complex.imCLM
        (complexificationEquiv (f.baseChange ℂ (complexificationEquiv.symm φ))) =
      f (mapCoeff Complex.imCLM φ) := by
  rw [complexificationEquiv_baseChange_complexificationEquiv_symm,
    imaginaryPart_ofReal_add_I_smul_ofReal]

/-- The base change of `f`, read on complex forms, extends `f` from real forms. -/
theorem complexificationEquiv_baseChange_symm_mapCoeff_ofRealCLM
    (f : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l) (α : SmoothForm I M ℝ k) :
    complexificationEquiv (f.baseChange ℂ
        (complexificationEquiv.symm (mapCoeff Complex.ofRealCLM α))) =
      mapCoeff Complex.ofRealCLM (f α) := by
  rw [← one_smul ℂ (mapCoeff Complex.ofRealCLM α), ← complexificationEquiv_tmul,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, complexificationEquiv_tmul,
    one_smul]

end TauCeti.SmoothForm

end

end
