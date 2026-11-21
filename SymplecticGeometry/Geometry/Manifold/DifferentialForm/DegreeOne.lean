/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Smooth one-forms evaluated on smooth vector fields

The value `x ↦ α_x (X x)` of a smooth real one-form `α` on a smooth vector field `X` is a smooth
function (`TauCeti.SmoothForm.contMDiff_apply_contMDiffSection`). Through Tau Ceti's
`TauCeti.SmoothForm.degreeOneEquiv`, `α` is a smooth section of the cotangent bundle, and the
pairing of smooth sections of a dual bundle and of the bundle is smooth
(`ContMDiffAt.clm_bundle_apply_scalar`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The value `α(X)` of a smooth one-form on a smooth vector field is a smooth function. -/
theorem contMDiff_apply_contMDiffSection (α : SmoothForm I M ℝ 1)
    (X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ fun x ↦ α.val x ![X x] := fun x ↦ by
  simpa [degreeOneEquiv_apply_apply_vec] using
    ((degreeOneEquiv α).contMDiff x).clm_bundle_apply_scalar (X.contMDiff x)

end TauCeti.SmoothForm

end
