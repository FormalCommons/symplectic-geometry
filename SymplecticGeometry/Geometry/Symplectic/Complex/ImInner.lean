/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic

/-!
# The form `Im ⟪·, ·⟫_ℂ` in real coordinates

On `ℂⁿ`, written `z = x + i y` through Tau Ceti's `TauCeti.complexEuclideanEquivRealProd`, the
symplectic form `TauCeti.imInnerSymplecticForm` is `⟪x₁, y₂⟫ - ⟪y₁, x₂⟫`.

## Main results

* `TauCeti.imInnerSymplecticForm_apply_eq_inner_complexEuclideanEquivRealProd`: the formula
  above. It is read off Tau Ceti's `TauCeti.isSymplectomorphism_complexEuclideanEquivRealProd_symm`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- The form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ` in the real coordinates `z = x + i y` of
`TauCeti.complexEuclideanEquivRealProd`: `ω (x₁ + i y₁, x₂ + i y₂) = ⟪x₁, y₂⟫ - ⟪y₁, x₂⟫`. -/
theorem imInnerSymplecticForm_apply_eq_inner_complexEuclideanEquivRealProd {ι : Type*}
    [Fintype ι] (z z' : EuclideanSpace ℂ ι) :
    imInnerSymplecticForm (EuclideanSpace ℂ ι) z z' =
      ⟪(complexEuclideanEquivRealProd ι z).1, (complexEuclideanEquivRealProd ι z').2⟫_ℝ -
        ⟪(complexEuclideanEquivRealProd ι z).2, (complexEuclideanEquivRealProd ι z').1⟫_ℝ := by
  simpa using SymplecticForm.isSymplectomorphism_iff.1
    (isSymplectomorphism_complexEuclideanEquivRealProd_symm (ι := ι))
    (complexEuclideanEquivRealProd ι z) (complexEuclideanEquivRealProd ι z')

end TauCeti

end
