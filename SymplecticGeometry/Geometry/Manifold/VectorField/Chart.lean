/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Chart.Linearization
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The coordinate field of a vector field at the centre of its chart

Let `V` be a vector field on a manifold with a boundaryless model `I`, and let `e` be the
extended chart at `x`. The coordinate field of `V` in `e` is the pullback
`VectorField.mpullback 𝓘(𝕜, E) I e.symm V`, a vector field on the model space `E`. This file
relates it to `V` near the centre `x`, and gives its first-order data at the chart image `e x`:

* `VectorField.mpullback_extChartAt_symm_self`: its value at `e x` is `V x`;
* `ContMDiffAt.contDiffAt_mpullback_extChartAt_symm`: it is `C^n` at `e x` when `V`, as a section
  of the tangent bundle, is `C^n` at `x`;
* `VectorField.eventually_mfderiv_extChartAt_apply_eq_mpullback`: near `x`, the derivative of `e`
  carries `V` to it, so that `V` and its coordinate field are related by `e`;
* `MDifferentiableAt.hasFDerivAt_mpullback_extChartAt_symm`: when `V` is differentiable at `x`,
  its derivative at `e x` is Tau Ceti's linearization `TauCeti.sectionLinearization I id V x`.

So at a zero `x` of a `C¹` field, the coordinate field is a field on `E` vanishing at `e x` whose
linear part there is the linearization of `V`: the setting of the local theory of a rest point
in a normed space. The first, second and fourth statements are Tau Ceti's
`VectorField.mpullbackWithin_extChartAt_symm_self`,
`ContMDiffWithinAt.contDiffWithinAt_mpullbackWithin_extChartAt_symm` and
`MDifferentiableAt.differentiableAt_mpullbackWithin_extChartAt_symm` on a boundaryless model,
where the pullback within the model range is the pullback, together with
`TauCeti.sectionLinearization_eq_vectorFieldChartDerivative`. The third is Mathlib's
`VectorField.eventuallyEq_mpullback_mpullbackWithin_extChartAt` on a boundaryless model, read
through the invertibility of the chart's derivative, `isInvertible_mfderiv_extChartAt`.

Away from the centre, and over any model with corners,
`HasMFDerivWithinAt.hasDerivWithinAt_extChartAt_comp_mpullbackWithin` says that a curve moving
with the velocity of `V` within a set of times moves, read in the extended chart, with the
coordinate field of `V`. It is Tau Ceti's `HasMFDerivAt.hasDerivAt_extChartAt_comp_mpullbackWithin`
for derivatives within a set, with the same proof, from Tau Ceti's
`HasMFDerivWithinAt.hasDerivWithinAt_extChartAt_comp`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013), Chapter 8
  (vector fields in coordinates).
-/

public section

open Set VectorField
open scoped Manifold ContDiff

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] {V : (x : M) → TangentSpace I x} {x : M}

/-- On a boundaryless model, the coordinate field of `V` in the extended chart at `x` takes the
value `V x` at the chart image of `x`. -/
theorem VectorField.mpullback_extChartAt_symm_self (V : (x : M) → TangentSpace I x) (x : M) :
    mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V (extChartAt I x x) = V x := by
  simpa [I.range_eq_univ, mpullbackWithin_univ] using mpullbackWithin_extChartAt_symm_self V x

variable [IsManifold I 1 M]

/-- On a boundaryless model, if the vector field `V` is `C^n` at `x` as a section of the tangent
bundle, its coordinate field in the extended chart at `x` is `C^n` at the chart image of `x`. -/
theorem ContMDiffAt.contDiffAt_mpullback_extChartAt_symm {n : WithTop ℕ∞}
    (hV : ContMDiffAt I I.tangent n (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x) :
    ContDiffAt 𝕜 n (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x) := by
  have h := hV.contMDiffWithinAt (s := univ).contDiffWithinAt_mpullbackWithin_extChartAt_symm
  rw [I.range_eq_univ, mpullbackWithin_univ, inter_univ, preimage_univ] at h
  exact contDiffWithinAt_univ.1 h

/-- On a boundaryless model, near `x` the derivative of the extended chart at `x` carries `V`
to its coordinate field: `V` and its coordinate field are related by the chart near `x`. -/
theorem VectorField.eventually_mfderiv_extChartAt_apply_eq_mpullback
    (V : (x : M) → TangentSpace I x) (x : M) :
    ∀ᶠ y in nhds x, mfderiv I 𝓘(𝕜, E) (extChartAt I x) y (V y) =
      mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V (extChartAt I x y) := by
  have h := eventuallyEq_mpullback_mpullbackWithin_extChartAt (s := univ) (x := x) V
  rw [nhdsWithin_univ, I.range_eq_univ, mpullbackWithin_univ] at h
  filter_upwards [h, extChartAt_source_mem_nhds (I := I) x] with y hy hys
  rw [hy, mpullback_apply, (isInvertible_mfderiv_extChartAt hys).self_apply_inverse]

/-- On a boundaryless model, if the vector field `V` is differentiable at `x` as a section of the
tangent bundle, its coordinate field in the extended chart at `x` has, at the chart image of `x`,
the derivative `TauCeti.sectionLinearization I id V x`, the linearization of `V` at `x`. -/
theorem MDifferentiableAt.hasFDerivAt_mpullback_extChartAt_symm
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) x) :
    HasFDerivAt (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V)
      (TauCeti.sectionLinearization (F := E) I id V x) (extChartAt I x x) := by
  have hU := hV.differentiableAt_mpullbackWithin_extChartAt_symm
  rw [I.range_eq_univ, mpullbackWithin_univ] at hU
  have hA : TauCeti.sectionLinearization (F := E) I id V x =
      fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x).symm V) (extChartAt I x x) :=
    ContinuousLinearMap.coe_injective (by
      rw [TauCeti.sectionLinearization_eq_vectorFieldChartDerivative,
        TauCeti.vectorFieldChartDerivative_def])
  rw [hA]
  exact hU.hasFDerivAt

omit [I.Boundaryless] in
/-- Let `e` be the extended chart at `x`. If a curve `γ` has velocity `V (γ t)` within a set `s`
of times at a time `t` with `γ t` in the chart source, then `e ∘ γ` has, within `s` at `t`, the
derivative `mpullbackWithin 𝓘(𝕜, E) I e.symm V (range I) (e (γ t))`, the coordinate field of
`V` at `e (γ t)`. -/
theorem HasMFDerivWithinAt.hasDerivWithinAt_extChartAt_comp_mpullbackWithin {γ : 𝕜 → M}
    {s : Set 𝕜} {t : 𝕜}
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (V (γ t))))
    (hsrc : γ t ∈ (extChartAt I x).source) :
    HasDerivWithinAt (extChartAt I x ∘ γ)
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) (extChartAt I x (γ t)))
      s t := by
  refine (hγ.hasDerivWithinAt_extChartAt_comp hsrc).congr_deriv ?_
  rw [mpullbackWithin_extChartAt_symm_apply V hsrc]
  -- `tangentCoordChange` is by definition this fibre coordinate of the trivialization
  -- (`TangentBundle.trivializationAt_apply`, `tangentCoordChange_def`).
  rfl

end
