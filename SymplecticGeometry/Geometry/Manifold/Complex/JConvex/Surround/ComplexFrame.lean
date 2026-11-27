/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Contractible
public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SymplecticGeometry.Geometry.Manifold.Complex.TangentCoordinates
import SymplecticGeometry.Topology.VectorBundle.Complement
import SymplecticGeometry.Topology.VectorBundle.Frame
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Complex frames along a totally real disc

Let `M` be a complex manifold modelled on `E` and `ι : ℝᵏ → M` a smooth map whose tangent images
are totally real for the complex structure of `M` (Tau Ceti's `TauCeti.IsTotallyReal`, in the
weak sense of `SymplecticGeometry.isTotallyReal_range_mfderiv_modelDisc`). The first step in
building a complex chart along `ι`, as Cieliebak and Eliashberg do for their model handle, is a
complex-linear map from `ℂᵏ` onto the complex span of each tangent image: the complex-linear
extension `x + i y ↦ dι x + i dι y` of the differential (`ContinuousLinearMap.complexExtension`).
It is complex linear (`ContinuousLinearMap.complexExtension_apply_smul`) and restricts to the
differential on the real points (`ContinuousLinearMap.complexExtension_apply_symm_real`). This
file shows that it is injective when `dι` is, and that it depends smoothly on the point when read
in tangent coordinates, as Tau Ceti's `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq`
asks of a prescribed differential.

The other factor of such a frame is a complement of these images. For `f : Y → M` a continuous
map from a contractible paracompact R₁ space, such as a disc, and `E` finite-dimensional, the file
completes a continuous family of injective complex-linear maps `L y : G₁ → T_(f y) M` to a
continuous family of complex-linear isomorphisms `G₁ × G₂ → T_(f y) M`, for `G₂` of the
complementary dimension.

The tangent spaces of the underlying real manifold are those of the complex manifold, and
multiplication by `i` on them is the almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold`. Tau Ceti's
`TauCeti.ContMDiffAlmostComplexStructure.exists_continuous_frame` gives a continuous
complex-linear frame `φ y : E ≃ T_(f y) M` along `f`. The maps `(φ y)⁻¹ ∘ L y : G₁ → E` are then
a continuous family of injective complex-linear maps into the fixed space `E`
(`SymplecticGeometry.Bundle.continuous_frame_symm_comp`), and a continuous complement of their
ranges (`Continuous.exists_continuous_isInvertible_coprod`), carried back by `φ y`, gives the
second factor.

## Main results

* `SymplecticGeometry.complexExtension_mfderiv_injective`: the complex-linear extension of an
  injective differential with totally real image is injective.
* `SymplecticGeometry.contMDiffAt_inTangentCoordinates_complexExtension_mfderiv`: the extension
  of the differential of a map `ι` smooth at a point is smooth in tangent coordinates there. It
  rests on `SymplecticGeometry.inTangentCoordinates_complexExtension_eq`: the tangent coordinate
  changes of a complex manifold are complex linear, so they commute with the extension.
* `SymplecticGeometry.exists_continuous_isInvertible_coprod_tangentSpace`: a continuous family of
  injective complex-linear maps into the tangent spaces along a map from a contractible space
  extends to a continuous family of complex-linear isomorphisms.

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
theorem complexExtension_mfderiv_injective {ι : EuclideanSpace ℝ (Fin k) → M}
    {x : EuclideanSpace ℝ (Fin k)}
    (hι : Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x))
    (hιR : IsTotallyReal ((SmoothAlmostComplexStructure.ofComplexManifold E M).toEndomorphism
        (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap)) :
    Function.Injective
      (complexExtension (Fin k) E (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)) := by
  rw [SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold] at hιR
  exact complexExtension_injective hι hιR

/-- For a map `ι : ℝᵏ → M` into a complex manifold, smooth at `x₀`, the complex-linear extensions
`x + i y ↦ dι x + i dι y` of its differentials form a smooth family of maps `ℂᵏ → T M` along
`ι`: read in tangent coordinates at `x₀`, they are smooth at `x₀`. -/
theorem contMDiffAt_inTangentCoordinates_complexExtension_mfderiv
    {ι : EuclideanSpace ℝ (Fin k) → M} {x₀ : EuclideanSpace ℝ (Fin k)}
    (hι : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι x₀)
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℂ (Fin k)) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, EuclideanSpace ℂ (Fin k) →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k)) 𝓘(ℝ, E) f ι
        (fun x ↦ complexExtension (Fin k) E
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)) x₀) x₀ := by
  have hD := hι.mfderiv_const (m := ∞) (by simp)
  have hnear : ∀ᶠ x in 𝓝 x₀, ι x ∈ (chartAt E (ι x₀)).source :=
    hι.continuousAt.preimage_mem_nhds
      ((chartAt E (ι x₀)).open_source.mem_nhds (mem_chart_source E (ι x₀)))
  refine ((complexExtension (Fin k) E).contMDiff.contMDiffAt.comp x₀ hD).congr_of_eventuallyEq ?_
  filter_upwards [hnear] with x hx
  exact inTangentCoordinates_complexExtension_eq _ hx

section ContinuousComplement

open _root_.Bundle Function Module TauCeti.SmoothAlmostComplexStructure

variable [FiniteDimensional ℂ E]
  {Y : Type*} [TopologicalSpace Y] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]

/-- The underlying real manifold of the complex manifold `M`. -/
private local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

/-- **A continuous complex complement along a map from a contractible space.** Let `M` be a
complex manifold modelled on a finite-dimensional space `E`, `Y` a contractible paracompact R₁
space and `L y : G₁ → T_(f y) M` injective complex-linear maps, continuous as a map
`Y × G₁ → TM`. If `dim G₁ + dim G₂ = dim E`, there are complex-linear maps
`K y : G₂ → T_(f y) M`, continuous as a map `Y × G₂ → TM`, such that each
`(L y, K y) : G₁ × G₂ → T_(f y) M` is an isomorphism.

Complex linearity is stated with `ofComplexManifold E M`, which is multiplication by `i` on each
tangent space (`ofComplexManifold_apply`). The real manifold structure `IsManifold 𝓘(ℝ, E) 1 M`,
which the complex one implies, gives `TM` its topology. -/
theorem exists_continuous_isInvertible_coprod_tangentSpace [IsManifold 𝓘(ℝ, E) 1 M]
    (hdim : finrank ℂ E = finrank ℂ G₁ + finrank ℂ G₂) {f : Y → M}
    {L : ∀ y, G₁ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f y)}
    (hL : Continuous fun q : Y × G₁ ↦ (⟨f q.1, L q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hLI : ∀ y v, L y (Complex.I • v) = ofComplexManifold E M (f y) (L y v))
    (hinj : ∀ y, Injective (L y)) :
    ∃ K : ∀ y, G₂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (f y),
      Continuous (fun q : Y × G₂ ↦ (⟨f q.1, K q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y v, K y (Complex.I • v) = ofComplexManifold E M (f y) (K y v)) ∧
      ∀ y, ((L y).coprod (K y)).IsInvertible := by
  have hf : Continuous f := (FiberBundle.continuous_proj E _).comp (hL.comp
    (Continuous.prodMk_left 0))
  have : Fact (finrank ℝ E = 2 * finrank ℂ E) := ⟨finrank_real_of_complex E⟩
  -- A continuous frame of `TM` along `f` carrying multiplication by `i` to itself.
  obtain ⟨φ, hφ, hφI⟩ := ((TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M).toContMDiff
    ⊤).exists_continuous_frame (G := E) hf
  simp only [toContMDiff_toEndomorphism_apply] at hφI
  -- In the frame, `L` becomes a continuous family of injective complex-linear maps `G₁ → E`.
  have hjI (y : Y) (v : G₁) : (φ y).symm (L y (Complex.I • v)) =
      Complex.I • (φ y).symm (L y v) := by
    rw [hLI]
    beta_reduce
    rw [ContinuousLinearEquiv.symm_apply_eq, hφI, ContinuousLinearEquiv.apply_symm_apply]
  let j : Y → G₁ →L[ℂ] E := fun y ↦
    ((φ y).symm.toContinuousLinearMap.comp (L y)).complexOfMapISmul (hjI y)
  have hjv (y : Y) : ⇑(j y) = (φ y).symm ∘ L y :=
    ContinuousLinearMap.coe_complexOfMapISmul _ (hjI y)
  have hjR := Bundle.continuous_frame_symm_comp hφ hL
  have hj : Continuous j := continuous_clm_apply.2 fun v ↦
    (hjR.clm_apply (continuous_const (y := v))).congr fun y ↦ by simp [hjv]
  have hjinj (y : Y) : Injective (j y) := by
    rw [hjv]
    exact (φ y).symm.injective.comp (hinj y)
  obtain ⟨k, hk, hkj⟩ := hj.exists_continuous_isInvertible_coprod hdim.symm hjinj
  refine ⟨fun y ↦ (φ y).toContinuousLinearMap.comp ((k y).restrictScalars ℝ),
    (hφ.comp (continuous_fst.prodMk ((hk.comp continuous_fst).clm_apply continuous_snd))).congr
      fun q ↦ rfl, fun y v ↦ ?_, fun y ↦ ?_⟩
  · simp [hφI]
  · obtain ⟨e, he⟩ := hkj y
    refine ⟨(e.restrictScalars' ℝ).trans (φ y), ?_⟩
    have he' (p : G₁ × G₂) : e p = (j y).coprod (k y) p := congrArg (· p) he
    ext v <;> simp [he', hjv]

end ContinuousComplement

end SymplecticGeometry
