/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual

/-!
# The one-form metrically dual to a smooth vector field

On a manifold `M` whose tangent bundle carries a smooth Riemannian metric `g`, a smooth vector
field `X` defines the smooth real one-form `X♭ = g(X, ·)`, the musical "flat" of `X`
(`TauCeti.SmoothForm.flat`). It is built as the smooth section `x ↦ g_x(X x, ·)` of the bundle
of linear maps from the tangent bundle to `ℝ` (Tau Ceti's `ContMDiffWithinAt.innerSL_bundle`),
read as a one-form through Tau Ceti's `TauCeti.SmoothForm.degreeOneEquiv`. Neither a
finite-dimensional model nor a boundaryless one is needed.

Tau Ceti's `TauCeti.RoughForm.metricDual` goes the other way, from one-forms to vector fields,
and `TauCeti.ContMDiffNondegenerateMetric.flat` is the pointwise linear map, not a smooth form.

## Main results

* `TauCeti.SmoothForm.flat`: the smooth one-form `g(X, ·)` of a smooth vector field `X`.
* `TauCeti.SmoothForm.flat_apply`: `X♭_x(v) = g_x(X x, v)`.
* `TauCeti.SmoothForm.mpullback_flat`: a map that preserves the metrics and carries `X` to `Y`
  pulls `Y♭` back to `X♭`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer, 2018, Chapter 2 (the musical isomorphisms).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The smooth one-form `g(X, ·)` metrically dual to a smooth vector field `X`: its value at `x`
sends `v` to the inner product `g_x(X x, v)`. -/
def flat (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))) :
    SmoothForm I M ℝ 1 :=
  degreeOneEquiv.symm ⟨fun x ↦ innerSL ℝ (X x), fun x ↦
    contMDiffWithinAt_univ.1 <| ContMDiffWithinAt.innerSL_bundle (I := I) (F := E)
      (V := fun x : M ↦ TangentSpace I x) (contMDiffWithinAt_univ.2 (hX x))⟩

variable {X : (x : M) → TangentSpace I x}
  {hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))}

/-- The flat of `X` sends a tangent vector `v` at `x` to `g_x(X x, v)`. -/
@[simp]
theorem flat_apply (x : M) (v : TangentSpace I x) : (flat X hX).val x ![v] = inner ℝ (X x) v := by
  rw [flat, degreeOneEquiv_symm_apply_apply]
  exact innerSL_apply_apply ℝ (X x) v

/-- The section of the flat of `X` sends a tangent vector `v` at `x` to `g_x(X x, v)`. -/
theorem degreeOneEquiv_flat_apply (x : M) (v : TangentSpace I x) :
    degreeOneEquiv (flat X hX) x v = inner ℝ (X x) v := by
  rw [degreeOneEquiv_apply_apply_vec, flat_apply]

/-- The flat of `X` evaluated on `X` itself is the squared length of `X`. -/
theorem flat_apply_self (x : M) : (flat X hX).val x ![X x] = ‖X x‖ ^ 2 := by
  rw [flat_apply, real_inner_self_eq_norm_sq]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  [IsContMDiffRiemannianBundle I' ∞ E' (fun x : M' ↦ TangentSpace I' x)]

/-- If a smooth map `f` preserves the Riemannian metrics and its differential carries `X` to
`Y`, then `f` pulls the flat of `Y` back to the flat of `X`. -/
theorem mpullback_flat {f : M → M'} (hf : ContMDiff I I' ∞ f)
    {Y : (y : M') → TangentSpace I' y}
    {hY : ContMDiff I' I'.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M'))}
    (hinner : ∀ (x : M) (v w : TangentSpace I x),
      inner ℝ (mfderiv I I' f x v) (mfderiv I I' f x w) = inner ℝ v w)
    (hXY : ∀ x, mfderiv I I' f x (X x) = Y (f x)) :
    mpullback f hf (flat Y hY) = flat X hX :=
  degreeOneEquiv.injective <| ContMDiffSection.ext fun x ↦ ContinuousLinearMap.ext fun v ↦ by
    rw [degreeOneEquiv_mpullback_apply, degreeOneEquiv_flat_apply, degreeOneEquiv_flat_apply,
      ← hXY, hinner]

end TauCeti.SmoothForm

end
