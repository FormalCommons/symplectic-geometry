/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# An analytic Riemannian metric on a finite-dimensional normed space

A finite-dimensional real normed space `E` need not be an inner product space, but Mathlib's
continuous linear equivalence `toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))`
carries the flat metric of the Euclidean space over to it. This file defines that metric, as the
pull-back of `riemannianMetricVectorSpace` along `toEuclidean`, and computes its inner product:
`⟪v, w⟫ = ⟪toEuclidean v, toEuclidean w⟫` at every point. Like `riemannianMetricVectorSpace`, the
metric is analytic (of smoothness `ω`); `ContMDiffRiemannianMetric.ofLE` gives it at any lower
smoothness.

## Main declarations

* `SymplecticGeometry.riemannianMetricToEuclidean`: the analytic Riemannian metric on `E` carried
  over by `toEuclidean`, with `SymplecticGeometry.riemannianMetricToEuclidean_def`.
* `SymplecticGeometry.riemannianMetricToEuclidean_inner`: its inner product.
-/

public section

open Bundle
open scoped ContDiff Manifold InnerProductSpace

namespace SymplecticGeometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The analytic Riemannian metric on a finite-dimensional real normed space `E` that
`toEuclidean` carries over from the flat metric of `EuclideanSpace ℝ (Fin (finrank ℝ E))`. -/
noncomputable def riemannianMetricToEuclidean :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) ω E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  (riemannianMetricVectorSpace _).pullback (toEuclidean (E := E))
    toEuclidean.contDiff.contMDiff fun x ↦ by
      rw [ContinuousLinearEquiv.mfderiv_eq]; exact (toEuclidean (E := E)).injective

/-- `riemannianMetricToEuclidean E` is the pull-back of `riemannianMetricVectorSpace` along
`toEuclidean`. -/
theorem riemannianMetricToEuclidean_def :
    riemannianMetricToEuclidean E = (riemannianMetricVectorSpace _).pullback
      (toEuclidean (E := E)) toEuclidean.contDiff.contMDiff fun x ↦ by
        rw [ContinuousLinearEquiv.mfderiv_eq]; exact (toEuclidean (E := E)).injective :=
  (rfl)

variable {E}

/-- The metric `riemannianMetricToEuclidean E` pairs two tangent vectors by the Euclidean inner
product of their images under `toEuclidean`. -/
@[simp]
theorem riemannianMetricToEuclidean_inner (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    (riemannianMetricToEuclidean E).inner x v w = ⟪toEuclidean v, toEuclidean w⟫_ℝ := by
  rw [riemannianMetricToEuclidean_def, ContMDiffRiemannianMetric.pullback_inner,
    TauCeti.riemannianMetricVectorSpace_inner, ContinuousLinearEquiv.mfderiv_eq]
  -- `NormedSpace.fromTangentSpace` is the identity of `EuclideanSpace` by definition, and Mathlib
  -- has no lemma that evaluates it.
  rfl

end SymplecticGeometry

end
