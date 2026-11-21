/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv

/-!
# Linearity of the Lie derivative of forms on a manifold in the vector field

Tau Ceti's `TauCeti.mlieDerivFormWithin` and `TauCeti.mlieDerivForm` are additive in the vector
field (`TauCeti.mlieDerivFormWithin_add_left`, `TauCeti.mlieDerivForm_add_left`). This file adds
the rest of their linearity in the field: they vanish along the zero field and commute with
constant multiples of the field, `L_{c V} φ = c L_V φ`, with no differentiability asked of the
field or of the form. Both are read in charts from the flat statements
`TauCeti.lieDerivFormWithin_zero_left` and `TauCeti.lieDerivFormWithin_const_smul_left` of
`SymplecticGeometry.Analysis.Calculus.DifferentialForm.LieDeriv`. The proofs follow Tau Ceti's
`TauCeti.mlieBracket_const_smul_left_field`.

## Main declarations

* `TauCeti.mlieDerivFormWithin_zero_left`, `TauCeti.mlieDerivForm_zero_left`: the Lie derivative
  along the zero field.
* `TauCeti.mlieDerivFormWithin_const_smul_left`, `TauCeti.mlieDerivForm_const_smul_left`:
  homogeneity in the field.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open Set VectorField

namespace TauCeti

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
