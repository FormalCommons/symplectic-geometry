/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic

/-!
# `(0,1)`-forms as sections and as one-forms

Tau Ceti writes an `F`-valued `(0,1)`-form of an almost complex manifold `(M, J)` in two ways:
pointwise, as a real linear map `η : T_x M → F` with `η (J v) = -(i • η v)`
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm` for the trivial bundle with fibre `F`),
and globally, as a smooth one-form `α : SmoothForm I M F 1` of type `(0,1)`
(`TauCeti.SmoothForm.IsOfType`). A smooth section `β` of `x ↦ (T_x M →L[ℝ] F)` becomes a
one-form through `TauCeti.SmoothForm.degreeOneEquiv`. This file links the two descriptions.

## Main results

* `TauCeti.SmoothForm.isOfType_zero_one_iff_isZeroOneForm`: a one-form `α` has type `(0,1)`
  exactly when its section `degreeOneEquiv α` is a `(0,1)`-form at every point.
* `TauCeti.SmoothForm.isOfType_zero_one_degreeOneEquiv_symm_iff`: the same, for the one-form of
  a smooth section `β`.
* `TauCeti.SmoothAlmostComplexStructure.degreeOneEquiv_delBar`: for a smooth function `f`, the
  section of `∂bar f` at `x` is `TauCeti.SmoothAlmostComplexStructure.dbarFunction` of `f` at `x`.
* `TauCeti.SmoothAlmostComplexStructure.delBar_eq_degreeOneEquiv_symm_iff`: for a smooth function
  `f`, the one-form `∂bar f` is the one-form of `β` exactly when `dbarFunction` of `f` is `β x`
  at every point `x`.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  2nd ed.][McDuffSalamon2012], Appendix C.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {J : SmoothAlmostComplexStructure I M}

namespace SmoothForm

/-- A one-form `α` has type `(0,1)` exactly when its section `degreeOneEquiv α` is a
`(0,1)`-form at every point `x`. -/
theorem isOfType_zero_one_iff_isZeroOneForm {α : SmoothForm I M F 1} :
    α.IsOfType J 0 1 ↔
      ∀ x, J.IsZeroOneForm (V := Bundle.Trivial M F) (degreeOneEquiv α x) := by
  simp [isOfType_zero_one_iff, SmoothAlmostComplexStructure.isZeroOneForm_iff]

/-- The one-form of a smooth section `β` of `x ↦ (T_x M →L[ℝ] F)` has type `(0,1)` exactly when
`β x` is a `(0,1)`-form at every point `x`. -/
theorem isOfType_zero_one_degreeOneEquiv_symm_iff
    {β : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)} :
    (degreeOneEquiv.symm β).IsOfType J 0 1 ↔
      ∀ x, J.IsZeroOneForm (V := Bundle.Trivial M F) (β x) := by
  simp [isOfType_zero_one_iff_isZeroOneForm]

end SmoothForm

namespace SmoothAlmostComplexStructure

/-- For a smooth function `f`, seen as a `0`-form, the section of `∂bar f` at `x` is `∂bar` of
the function `y ↦ f y` at `x`. -/
@[simp]
theorem degreeOneEquiv_delBar (f : SmoothForm I M F 0) (x : M) :
    SmoothForm.degreeOneEquiv (J.delBar f) x = J.dbarFunction (fun y ↦ f.val y 0) x := by
  ext v
  simp [delBar_apply_apply_eq_dbarFunction]

/-- For a smooth function `f`, seen as a `0`-form, `∂bar f` is the one-form of a smooth section
`β` of `x ↦ (T_x M →L[ℝ] F)` exactly when `∂bar` of the function `y ↦ f y` is `β x` at every
point `x`. -/
theorem delBar_eq_degreeOneEquiv_symm_iff (f : SmoothForm I M F 0)
    {β : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x : M ↦ TangentSpace I x →L[ℝ] F)} :
    J.delBar f = SmoothForm.degreeOneEquiv.symm β ↔
      ∀ x, J.dbarFunction (fun y ↦ f.val y 0) x = β x := by
  simp [LinearEquiv.eq_symm_apply, ContMDiffSection.ext_iff]

end SmoothAlmostComplexStructure

end TauCeti

end
