/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Composition
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Basic

/-!
# The covariant derivative of an almost complex structure

Let `cov` be a covariant derivative on the tangent bundle of `M` and `J` a smooth almost complex
structure. The covariant derivative `∇J` of `J` is Tau Ceti's induced connection on the
endomorphism bundle, `cov.hom cov J.toEndomorphism`, applied to the section `J.toEndomorphism`:
for a vector field `s` differentiable at `x`,
`(∇_v J) (s x) = ∇_v (J s) - J (∇_v s)`.

Differentiating `J² = -1` with the product rule `CovariantDerivative.hom_comp` shows that each
`∇_v J` anticommutes with `J`: `(∇_v J) ∘ J + J ∘ (∇_v J) = 0`. This holds for every covariant
derivative on `TM`, with no metric and no condition on the torsion.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.mdifferentiableAt_toEndomorphism`: `J` is differentiable
  as a section of the endomorphism bundle, so that `CovariantDerivative.hom_apply` evaluates `∇J`.
* `TauCeti.SmoothAlmostComplexStructure.hom_toEndomorphism_comp_add_comp_hom`: the
  anticommutation `(∇_v J) ∘ J + J ∘ (∇_v J) = 0`.
* `TauCeti.SmoothAlmostComplexStructure.apply_hom_toEndomorphism_apply`: its pointwise form
  `J ((∇_v J) u) = -(∇_v J) (J u)`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 4.2.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (J : SmoothAlmostComplexStructure I M)
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

omit [FiniteDimensional ℝ E] in
/-- A smooth almost complex structure is differentiable at every point as a section of the
endomorphism bundle of `TM`. -/
theorem mdifferentiableAt_toEndomorphism (x : M) :
    MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y (J.toEndomorphism y)) x :=
  J.toEndomorphism.contMDiff.mdifferentiable (by simp) x

/-- The covariant derivative `∇_v J` of an almost complex structure anticommutes with `J`:
`(∇_v J) ∘ J + J ∘ (∇_v J) = 0`, for every covariant derivative on `TM`. It is the derivative of
`J² = -1`. -/
theorem hom_toEndomorphism_comp_add_comp_hom (x : M) (v : TangentSpace I x) :
    (cov.hom cov J.toEndomorphism x v).comp (J.toEndomorphism x) +
      (J.toEndomorphism x).comp (cov.hom cov J.toEndomorphism x v) = 0 := by
  have hJ := J.mdifferentiableAt_toEndomorphism x
  rw [← cov.hom_comp cov cov hJ hJ v]
  have hsq : (fun y ↦ (J.toEndomorphism y).comp (J.toEndomorphism y)) =
      -fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y) :=
    funext J.square_neg
  have hid : MDiffAt (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z) y
        (ContinuousLinearMap.id ℝ (TangentSpace I y))) x := by
    have h := mdifferentiableAt_neg_section (hJ.clm_bundle_comp hJ)
    rw [hsq] at h
    simpa using h
  rw [hsq, (cov.hom cov).isCovariantDerivativeOnUniv.neg hid, cov.hom_id, neg_zero, zero_apply]

/-- The covariant derivative `∇_v J` anticommutes with `J`, pointwise:
`J ((∇_v J) u) = -(∇_v J) (J u)`. -/
theorem apply_hom_toEndomorphism_apply (x : M) (v u : TangentSpace I x) :
    J x (cov.hom cov J.toEndomorphism x v u) = -cov.hom cov J.toEndomorphism x v (J x u) := by
  have h := congr($(J.hom_toEndomorphism_comp_add_comp_hom cov x v) u)
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h

end SmoothAlmostComplexStructure

end TauCeti

end
