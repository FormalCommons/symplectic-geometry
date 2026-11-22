/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.ProjectiveLine
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The affine coordinate of the Riemann sphere as a real chart

Tau Ceti charts the Riemann sphere `OnePoint ℂ` by its affine coordinate, whose inverse is the
inclusion `ℂ → OnePoint ℂ`, and by the inverted coordinate. This file records how the inclusion
reads for the underlying real surface, modelled on `𝓘(ℝ, ℂ)`:

* `OnePoint.contMDiff_coe_real`: the inclusion is real-analytic;
* `OnePoint.mfderiv_coe_apply`: its derivative is the identity of `ℂ`, the tangent spaces at
  `z` and at `(z : OnePoint ℂ)` being `ℂ`;
* `OnePoint.mvfderiv_coe_apply`: so the derivative at a finite point of a map from the sphere to
  a normed space is the derivative of its restriction to `ℂ`;
* `OnePoint.equivProjectivization_coe_eq_affineParam`: under Mathlib's identification of
  `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)`, the inclusion is Tau Ceti's affine coordinate
  `t ↦ [t : 1]` of the projective line.

The derivative is computed in charts, as in the proof of Tau Ceti's
`OnePoint.mfderiv_smul_coe_apply`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1.5.
-/

public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace OnePoint

/-- The inclusion `ℂ → OnePoint ℂ` is real-analytic for the underlying real surfaces. -/
theorem contMDiff_coe_real : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω ((↑) : ℂ → OnePoint ℂ) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_coe (𝕜 := ℂ)).restrictScalars ℝ

/-- The real derivative of the inclusion `ℂ → OnePoint ℂ` at `z` is the identity of `ℂ`: the
inclusion is the inverse of the affine chart, through which the tangent space at `z` is read. -/
theorem mfderiv_coe_apply (z v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((↑) : ℂ → OnePoint ℂ) z v = v := by
  rw [((contMDiff_coe_real z).mdifferentiableAt (by simp)).mfderiv]
  simp only [writtenInExtChartAt, chartAt_coe, affineChart_coe, fderivWithin_univ,
    Function.comp_def, mfld_simps]
  rw [fderiv_fun_id, ContinuousLinearMap.id_comp]
  -- The casts `tangentSpaceCastModel` between the tangent spaces and `ℂ` are identities.
  rfl

/-- At a finite point `z`, the derivative of a map `F` from the Riemann sphere to a real normed
space is the derivative of `F` restricted to `ℂ`. -/
theorem mvfderiv_coe_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : OnePoint ℂ → E} {z : ℂ} (hF : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z) (a : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) F z a = fderiv ℝ (F ∘ (↑)) z a :=
  (congrArg (mvfderiv 𝓘(ℝ, ℂ) F z) (mfderiv_coe_apply z a)).symm.trans
    ((mvfderiv_comp_apply z hF ((contMDiff_coe_real z).mdifferentiableAt (by simp)) a).symm.trans
      (TauCeti.mvfderiv_eq_fderiv_apply _ z a))

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)`, `t ↦ [t : 1]` and
`∞ ↦ [1 : 0]`, is real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_real :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ω (equivProjectivization ℂ) := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_equivProjectivization (𝕜 := ℂ)).restrictScalars ℝ

/-- The inverse of Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` is
real-analytic for the underlying real surfaces. -/
theorem contMDiff_equivProjectivization_symm_real :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) ω (equivProjectivization ℂ).symm := by
  simpa only [modelWithCornersSelf_restrictScalars] using
    (contMDiff_equivProjectivization_symm (𝕜 := ℂ)).restrictScalars ℝ

/-- Mathlib's identification of `OnePoint ℂ` with `ℙ ℂ (Fin 2 → ℂ)` sends a finite point `t` to
`[t : 1]`, the value at `t` of Tau Ceti's affine coordinate at the coordinate `1`. -/
theorem equivProjectivization_apply_coe_eq_affineParam (t : ℂ) :
    equivProjectivization ℂ t = TauCeti.ProjectiveLine.affineParam 1 t := by
  rw [equivProjectivization_apply_coe, TauCeti.ProjectiveLine.affineParam_eq]
  congr 1
  ext k
  fin_cases k <;> simp

end OnePoint

end
