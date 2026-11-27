/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange

/-!
# Tangent coordinates on a complex manifold

Regard a complex manifold `M`, with model space `E`, also as a real one. Its changes of tangent
coordinates are differentials of holomorphic chart transitions: the real ones agree with the
complex ones (Tau Ceti's `TauCeti.tangentCoordChange_modelWithCornersSelf_restrictScalars_apply`),
so they are complex linear. This file records this and two consequences: for reading families of
maps into `T M` in tangent coordinates (`inTangentCoordinates`), and for reading a map into `M`
in a chart.

## Main results

* `SymplecticGeometry.tangentCoordChange_complex_smul`: the real tangent coordinate changes of `M`
  are complex linear.
* `SymplecticGeometry.inTangentCoordinates_complexExtension_eq`: near a point, reading the
  complex-linear extensions `x + i y ↦ ϕ x + i ϕ y` of maps `ϕ : ℝᵏ → T M` in tangent
  coordinates gives the complex-linear extensions of the maps read in tangent coordinates.
* `SymplecticGeometry.fderiv_extChartAt_comp_I_smul`: if the real differential of a map
  `f : V → M` from a complex normed space commutes with multiplication by `i` at a point, so does
  the derivative there of `f` read in a chart of `M`.
* `SymplecticGeometry.fderiv_extChartAt_comp_comp_I_smul`: the same for `f` after a
  complex-linear map.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

noncomputable section

open Manifold

namespace SymplecticGeometry

open TauCeti ContinuousLinearMap

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- The changes of real tangent coordinates of the complex manifold `M` are complex linear: on the
overlap of the charts at `x` and `y`, the coordinate change from `x` to `y` commutes with
multiplication by every complex number. -/
theorem tangentCoordChange_complex_smul {x y z : M}
    (h : z ∈ (chartAt E x).source ∩ (chartAt E y).source) (c : ℂ) (w : E) :
    tangentCoordChange 𝓘(ℝ, E) x y z (c • w) = c • tangentCoordChange 𝓘(ℝ, E) x y z w := by
  rw [tangentCoordChange_modelWithCornersSelf_restrictScalars_apply ℝ (𝕜' := ℂ) h,
    tangentCoordChange_modelWithCornersSelf_restrictScalars_apply ℝ (𝕜' := ℂ) h, map_smul]

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
  exact comp_complexExtension _
    (fun v ↦ tangentCoordChange_complex_smul ⟨mem_chart_source E (g x), hx⟩ _ v) _

/-- Let `f : V → M` be a map from a complex normed space into the complex manifold `M`, continuous
at `q`, whose real differential at `q` commutes with multiplication by `i`. Then the derivative at
`q` of `f` read in the chart of `M` at `x₀`, whose source contains `f q`, also commutes with
multiplication by `i`. -/
theorem fderiv_extChartAt_comp_I_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → M} {q : V} (hf : ContinuousAt f q)
    (hfI : ∀ v : V, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q (Complex.I • v) =
      Complex.I • (show E from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v))
    {x₀ : M} (hx : f q ∈ (chartAt E x₀).source) (v : V) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ f) q (Complex.I • v) =
      Complex.I • fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ f) q v := by
  have hx' : f q ∈ (extChartAt 𝓘(ℝ, E) x₀).source := by rwa [extChartAt_source]
  -- The chart reading is `mfderiv f q` followed by the coordinate change from `f q` to `x₀`,
  -- which agrees with the complex one, so it is complex linear.
  rw [hf.fderiv_extChartAt_comp_apply hx', hf.fderiv_extChartAt_comp_apply hx', hfI,
    extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
    mfderiv_chartAt_eq_tangentCoordChange hx]
  exact tangentCoordChange_complex_smul ⟨mem_chart_source E (f q), hx⟩ _ _

/-- Let `f : V → M` be a map from a complex normed space into the complex manifold `M`,
differentiable at `L q` for a complex-linear map `L : W →L[ℂ] V`, whose real differential at
`L q` commutes with multiplication by `i`. Then the derivative at `q` of `f ∘ L` read in the chart
of `M` at `x₀`, whose source contains `f (L q)`, also commutes with multiplication by `i`. -/
theorem fderiv_extChartAt_comp_comp_I_smul {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {f : V → M} (L : W →L[ℂ] V)
    {q : W} (hf : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) f (L q))
    (hfI : ∀ v : V, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (L q) (Complex.I • v) =
      Complex.I • (show E from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (L q) v))
    {x₀ : M} (hx : f (L q) ∈ (chartAt E x₀).source) (v : W) :
    fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ f ∘ L) q (Complex.I • v) =
      Complex.I • fderiv ℝ (extChartAt 𝓘(ℝ, E) x₀ ∘ f ∘ L) q v := by
  have hL : HasFDerivAt L (L.restrictScalars ℝ) q := (L.restrictScalars ℝ).hasFDerivAt
  have hd (w : W) : mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (f ∘ L) q w =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (L q) (L w) := by
    rw [mfderiv_comp q hf hL.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, hL.fderiv]
    -- `mfderiv_eq_fderiv` only inserts the identifications of the tangent spaces of a normed
    -- space with the space itself, which are the identity.
    rfl
  exact fderiv_extChartAt_comp_I_smul (hf.continuousAt.comp L.continuous.continuousAt)
    (fun w ↦ by rw [hd, hd, map_smul, hfI]) hx v

end SymplecticGeometry
