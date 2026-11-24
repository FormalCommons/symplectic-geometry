/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The covariant derivative of an almost complex structure

Let `cov` be a covariant derivative on the tangent bundle of `M` and `J` a smooth almost complex
structure. The covariant derivative `∇J` of `J` is Tau Ceti's induced connection on the
endomorphism bundle, `cov.hom cov J.toEndomorphism`, applied to the section `J.toEndomorphism`:
for a vector field `s` differentiable at `x`,
`(∇_v J) (s x) = ∇_v (J s) - J (∇_v s)`.

Differentiating `J² = -1` shows that each `∇_v J` anticommutes with `J`, for every covariant
derivative on `TM`, with no metric and no condition on the torsion. That is Tau Ceti's
`CovariantDerivative.hom_apply_apply_anticomm`, stated for a section of `End(V)` squaring to `-1`
on any vector bundle; the lemma of this file gives its differentiability hypothesis for `J`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.mdifferentiableAt_toEndomorphism`: `J` is differentiable
  as a section of the endomorphism bundle, so that `CovariantDerivative.hom_apply` evaluates `∇J`
  and `CovariantDerivative.hom_apply_apply_anticomm` applies to it.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)

/-- A smooth almost complex structure is differentiable at every point as a section of the
endomorphism bundle of `TM`. -/
theorem mdifferentiableAt_toEndomorphism (x : M) :
    MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (J.toEndomorphism y)) x :=
  J.toEndomorphism.contMDiff.mdifferentiable (by simp) x

end SmoothAlmostComplexStructure

end TauCeti

end
