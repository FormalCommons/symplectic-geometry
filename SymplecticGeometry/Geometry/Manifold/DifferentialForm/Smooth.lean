/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth

/-!
# The bilinear forms of smooth two-forms under the module operations

Tau Ceti's `TauCeti.SmoothForm.bilinFormAt` reads the value at `x` of a real smooth two-form
`σ` on `M` as a bilinear form `σ_x` on the tangent space `T_x M`. This file shows that the map
`σ ↦ σ_x` is compatible with the module structure of the smooth two-forms: it sends sums,
real multiples, zero, negatives and differences of two-forms to the same operations on their
bilinear forms. All these lemmas are `@[simp]`.

The same family exists for the two-forms on a vector bundle of this library, in
`SymplecticGeometry/Geometry/Manifold/VectorBundle/Symplectic/Basic.lean`
(`SymplecticGeometry.ContMDiffTwoForm.bilinFormAt_add` and its neighbours).

## Main results

* `TauCeti.SmoothForm.bilinFormAt_add`, `TauCeti.SmoothForm.bilinFormAt_smul`,
  `TauCeti.SmoothForm.bilinFormAt_zero`, `TauCeti.SmoothForm.bilinFormAt_neg`,
  `TauCeti.SmoothForm.bilinFormAt_sub`.
-/

public section

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]

/-- The bilinear form of a sum of two-forms is the sum of their bilinear forms. -/
@[simp]
theorem bilinFormAt_add (σ τ : SmoothForm I M ℝ 2) (x : M) :
    (σ + τ).bilinFormAt x = σ.bilinFormAt x + τ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of a real multiple of a two-form is the same multiple of its bilinear
form. -/
@[simp]
theorem bilinFormAt_smul (c : ℝ) (σ : SmoothForm I M ℝ 2) (x : M) :
    (c • σ).bilinFormAt x = c • σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of the zero two-form is zero. -/
@[simp]
theorem bilinFormAt_zero (x : M) : (0 : SmoothForm I M ℝ 2).bilinFormAt x = 0 := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of the negative of a two-form is the negative of its bilinear form. -/
@[simp]
theorem bilinFormAt_neg (σ : SmoothForm I M ℝ 2) (x : M) :
    (-σ).bilinFormAt x = -σ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

/-- The bilinear form of a difference of two-forms is the difference of their bilinear forms. -/
@[simp]
theorem bilinFormAt_sub (σ τ : SmoothForm I M ℝ 2) (x : M) :
    (σ - τ).bilinFormAt x = σ.bilinFormAt x - τ.bilinFormAt x := by
  ext v w
  simp [SmoothBundleForm.eval₂_apply]

end TauCeti.SmoothForm

end
