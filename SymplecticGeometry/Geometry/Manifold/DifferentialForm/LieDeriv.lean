/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv

/-!
# Linearity of the Lie derivative of forms in the vector field

Tau Ceti's `TauCeti.lieDerivFormWithin` and `TauCeti.mlieDerivFormWithin` are additive in the
vector field (`TauCeti.lieDerivFormWithin_add_left`, `TauCeti.mlieDerivFormWithin_add_left`).
This file adds the rest of their linearity in the field: they vanish along the zero field and
commute with constant multiples of the field, `L_{c V} φ = c L_V φ`. Neither needs any
differentiability of the field or of the form, since the derivative of a constant multiple is the
constant multiple of the derivative (`fderivWithin_const_smul_field`).

The proofs follow Tau Ceti's `TauCeti.mlieBracket_const_smul_left_field`.

## Main declarations

* `TauCeti.lieDerivFormWithin_zero_left`, `TauCeti.lieDerivForm_zero_left`,
  `TauCeti.mlieDerivFormWithin_zero_left`, `TauCeti.mlieDerivForm_zero_left`: the Lie derivative
  along the zero field.
* `TauCeti.lieDerivFormWithin_const_smul_left`, `TauCeti.lieDerivForm_const_smul_left`,
  `TauCeti.mlieDerivFormWithin_const_smul_left`, `TauCeti.mlieDerivForm_const_smul_left`:
  homogeneity in the field.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open Set VectorField

namespace TauCeti

section Flat

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {k : ℕ} {s : Set E} {x : E}

/-- The Lie derivative within a set of a form along the zero vector field vanishes. -/
@[simp]
theorem lieDerivFormWithin_zero_left (ω : E → E [⋀^Fin k]→L[𝕜] F) (s : Set E) (x : E) :
    lieDerivFormWithin 0 ω s x = 0 := by
  simp [lieDerivFormWithin_def, fderivWithin_zero]

/-- The Lie derivative of a form along the zero vector field vanishes. -/
@[simp]
theorem lieDerivForm_zero_left (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivForm 0 ω = 0 := by
  rw [← lieDerivFormWithin_univ]
  exact funext (lieDerivFormWithin_zero_left ω univ)

/-- The Lie derivative within a set commutes with constant multiples of the vector field, where
derivatives within the set are unique. -/
@[simp]
theorem lieDerivFormWithin_const_smul_left (c : 𝕜) (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivFormWithin (c • V) ω s x = c • lieDerivFormWithin V ω s x := by
  simp only [lieDerivFormWithin_def, fderivWithin_const_smul_field c hs, Pi.smul_apply, map_smul,
    smul_add]

/-- The Lie derivative commutes with constant multiples of the vector field:
`L_{c V} ω = c L_V ω`. -/
@[simp]
theorem lieDerivForm_const_smul_left (c : 𝕜) (V : E → E) (ω : E → E [⋀^Fin k]→L[𝕜] F) :
    lieDerivForm (c • V) ω = c • lieDerivForm V ω := by
  ext x : 1
  simpa only [lieDerivFormWithin_univ, Pi.smul_apply] using
    lieDerivFormWithin_const_smul_left c V ω (uniqueDiffWithinAt_univ (x := x))

end Flat

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The Lie derivative within a set of a form along the zero vector field vanishes. -/
@[simp]
theorem mlieDerivFormWithin_zero_left (φ : RoughForm I M F k) (s : Set M) (x : M) :
    mlieDerivFormWithin (0 : (x : M) → TangentSpace I x) φ s x = 0 := by
  rw [mlieDerivFormWithin_def, VectorField.mpullbackWithin_zero]
  exact lieDerivFormWithin_zero_left _ _ _

/-- The Lie derivative of a form along the zero vector field vanishes. -/
@[simp]
theorem mlieDerivForm_zero_left (φ : RoughForm I M F k) :
    mlieDerivForm (0 : (x : M) → TangentSpace I x) φ = 0 := by
  rw [← mlieDerivFormWithin_univ]
  exact funext (mlieDerivFormWithin_zero_left φ univ)

/-- The Lie derivative within a set commutes with constant multiples of the vector field, where
derivatives within the set are unique. -/
@[simp]
theorem mlieDerivFormWithin_const_smul_left (c : ℝ) (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F k) {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivFormWithin (c • V) φ s x = c • mlieDerivFormWithin V φ s x := by
  simp only [mlieDerivFormWithin_def, VectorField.mpullbackWithin_const_smul]
  exact lieDerivFormWithin_const_smul_left c _ _ hs

/-- The Lie derivative commutes with constant multiples of the vector field:
`L_{c V} φ = c L_V φ`. -/
@[simp]
theorem mlieDerivForm_const_smul_left (c : ℝ) (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F k) :
    mlieDerivForm (c • V) φ = c • mlieDerivForm V φ := by
  rw [← mlieDerivFormWithin_univ, ← mlieDerivFormWithin_univ]
  exact funext fun _ ↦ mlieDerivFormWithin_const_smul_left c V φ (uniqueMDiffWithinAt_univ I)

end TauCeti

end
