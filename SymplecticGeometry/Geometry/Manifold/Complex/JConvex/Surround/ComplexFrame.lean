/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Tangent.CoordChange

/-!
# Complex frames along a totally real disc

Let `M` be a complex manifold modelled on `E` and `ι : ℝᵏ → M` a smooth map whose tangent images
are totally real for the complex structure of `M` (Tau Ceti's `TauCeti.IsTotallyReal`, in the
weak sense of `SymplecticGeometry.isTotallyReal_range_mfderiv_modelDisc`). The first step in
building a complex chart along `ι`, as Cieliebak and Eliashberg do for their model handle, is a
complex-linear map from `ℂᵏ` onto the complex span of each tangent image: the complex-linear
extension `x + i y ↦ dι x + i dι y` of the differential (`ContinuousLinearMap.complexExtension`).
It is complex linear (`ContinuousLinearMap.complexExtension_apply_I_smul`) and restricts to the
differential on the real points (`ContinuousLinearMap.complexExtension_apply_symm_real`). This
file shows that it is injective when `dι` is, and that it depends smoothly on the point when read
in tangent coordinates, as Tau Ceti's `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`
asks of a prescribed differential.

## Main results

* `SymplecticGeometry.injective_complexExtension_mfderiv`: the complex-linear extension of an
  injective differential with totally real image is injective.
* `SymplecticGeometry.inTangentCoordinates_complexExtension_eq`: near a point, the extension
  commutes with reading in tangent coordinates, since the tangent coordinate changes of a complex
  manifold are complex linear (Tau Ceti's `ModelWithCorners.tangentCoordChange_smul`).
* `SymplecticGeometry.contMDiffAt_inTangentCoordinates_complexExtension_mfderiv`: the extension
  of the differential of a smooth `ι` is smooth in tangent coordinates.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Proposition 5.55 and its proof (a chart along a totally real disc).
-/

public section

noncomputable section

open Manifold Set Filter
open scoped ContDiff Topology TauCeti.ComplexManifold

namespace SymplecticGeometry

open TauCeti ContinuousLinearMap

variable {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The complex-linear extension `x + i y ↦ dι x + i dι y` of an injective differential of
`ι : ℝᵏ → M` into a complex manifold, whose image is totally real for the complex structure of
`M`, is injective. -/
theorem injective_complexExtension_mfderiv {ι : EuclideanSpace ℝ (Fin k) → M}
    {x : EuclideanSpace ℝ (Fin k)}
    (hι : Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x))
    (hιR : IsTotallyReal ((SmoothAlmostComplexStructure.ofComplexManifold E M).toEndomorphism
        (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap)) :
    Function.Injective
      (complexExtension (Fin k) E (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)) := by
  rw [SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold] at hιR
  exact injective_complexExtension hι hιR

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
  simpa only [modelWithCornersSelf_restrictScalars] using
    𝓘(ℂ, E).tangentCoordChange_smul ℝ ⟨mem_chart_source E (g x), hx⟩ Complex.I v

/-- For a smooth map `ι : ℝᵏ → M` into a complex manifold, the complex-linear extensions
`x + i y ↦ dι x + i dι y` of its differentials form a smooth family of maps `ℂᵏ → T M` along
`ι`: read in tangent coordinates at `x₀`, they are smooth at `x₀`. -/
theorem contMDiffAt_inTangentCoordinates_complexExtension_mfderiv
    {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℂ (Fin k)) (x₀ : EuclideanSpace ℝ (Fin k)) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℂ (Fin k) →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k)) 𝓘(ℝ, E) f ι
        (fun x ↦ complexExtension (Fin k) E
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)) x₀) x₀ := by
  have hD := (hι x₀).mfderiv_const (m := ∞) (by simp)
  have hnear : ∀ᶠ x in 𝓝 x₀, ι x ∈ (chartAt E (ι x₀)).source :=
    (hι.continuous.continuousAt).preimage_mem_nhds
      ((chartAt E (ι x₀)).open_source.mem_nhds (mem_chart_source E (ι x₀)))
  refine ((complexExtension (Fin k) E).contMDiff.contMDiffAt.comp x₀ hD).congr_of_eventuallyEq ?_
  filter_upwards [hnear] with x hx
  exact inTangentCoordinates_complexExtension_eq _ hx

end SymplecticGeometry
