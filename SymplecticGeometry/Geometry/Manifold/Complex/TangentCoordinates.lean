/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange

/-!
# Tangent coordinates on a complex manifold

On a complex manifold `M` modelled on `E`, viewed as a real manifold, the changes of tangent
coordinates are differentials of holomorphic chart transitions: the real ones agree with the
complex ones (Tau Ceti's `TauCeti.tangentCoordChange_modelWithCornersSelf_restrictScalars_apply`),
so they are complex linear. This file records a consequence for reading families of maps into
`T M` in tangent coordinates (`inTangentCoordinates`).

## Main results

* `SymplecticGeometry.inTangentCoordinates_complexExtension_eq`: near a point, reading the
  complex-linear extensions `x + i y ↦ ϕ x + i ϕ y` of maps `ϕ : ℝᵏ → T M` in tangent
  coordinates gives the complex-linear extensions of the maps read in tangent coordinates.
-/

public section

noncomputable section

open Manifold

namespace SymplecticGeometry

open TauCeti ContinuousLinearMap

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- Near `x₀`, reading the complex-linear extensions of a family of real maps
`ϕ x : ℝᵏ → T_{g x} M` in tangent coordinates gives the complex-linear extensions of the family
read in tangent coordinates: the tangent coordinate changes of the complex manifold `M` are
complex linear. The coordinates on the source, a model space, play no role. -/
theorem inTangentCoordinates_complexExtension_eq
    {N : Type*} {f : N → EuclideanSpace ℂ (Fin k)} {f' : N → EuclideanSpace ℝ (Fin k)}
    {g : N → M} (ϕ : ∀ x, EuclideanSpace ℝ (Fin k) →L[ℝ] TangentSpace 𝓘(ℝ, E) (g x))
    {x₀ x : N} (hx : g x ∈ (chartAt E (g x₀)).source) :
    inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k)) 𝓘(ℝ, E) f g
        (fun x ↦ complexExtension (Fin k) E (ϕ x)) x₀ x =
      complexExtension (Fin k) E
        (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) f' g ϕ x₀ x) := by
  -- The family of extensions is only type-correct up to `TangentSpace 𝓘(ℝ, E) (g x) = E`, which
  -- `rw` does not see through, so the first step is a `trans`.
  refine (inTangentCoordinates_eq f g (fun x ↦ complexExtension (Fin k) E (ϕ x)) (by simp)
    hx).trans ?_
  rw [inTangentCoordinates_eq f' g ϕ (by simp) hx]
  simp only [tangentBundleCore_coordChange_model_space]
  -- The coordinate change of `M` from `g x` to `g x₀` is complex linear.
  refine comp_complexExtension _ (fun v ↦ ?_) _
  have h := (⟨mem_chart_source E (g x), hx⟩ :
    g x ∈ (chartAt E (g x)).source ∩ (chartAt E (g x₀)).source)
  rw [tangentCoordChange_modelWithCornersSelf_restrictScalars_apply ℝ (𝕜' := ℂ) h,
    tangentCoordChange_modelWithCornersSelf_restrictScalars_apply ℝ (𝕜' := ℂ) h, map_smul]

end SymplecticGeometry
