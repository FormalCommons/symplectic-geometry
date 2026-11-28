/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Contractible
public import SymplecticGeometry.Analysis.InnerProductSpace.Euclidean.ComplexExtension
public import SymplecticGeometry.Geometry.Manifold.Complex.JConvex.Surround.Shape
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.Analysis.Normed.Operator.Perturbation
import SymplecticGeometry.Geometry.Manifold.Complex.TangentCoordinates
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Pullback
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Tangent.Coordinates
import SymplecticGeometry.LinearAlgebra.Complex.Finrank
import SymplecticGeometry.Topology.VectorBundle.Complement
import SymplecticGeometry.Topology.VectorBundle.Frame
import TauCeti.Geometry.Manifold.VectorBundle.Pullback
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

For `ι` smooth, such a complement can be taken smooth in tangent coordinates when `L` is. Near
each point `x₀`, the frame `B₀ x₀` carried to the nearby tangent spaces by the tangent coordinate
changes is smooth (`SymplecticGeometry.contMDiffAt_inTangentCoordinates_tangentCoordChange_comp`)
and complex linear, and it stays close to `B₀` in the sense that
`(L y, B₀ y)⁻¹ ∘ (B - B₀ y) ∘ snd` has norm less than `1`. That condition is convex in `B`, does
not depend on charts, and keeps `(L y, B)` invertible
(`ContinuousLinearMap.IsInvertible.of_norm_inverse_comp_sub_lt_one`). Mathlib's
`exists_contMDiffSection_forall_mem_convex_of_local` glues these local frames to a smooth section
of the bundle of maps from the trivial bundle with fibre `G₂` to the pullback of `TM` along `ι`,
which is smooth in tangent coordinates
(`Bundle.Pullback.contMDiffAt_hom_trivial_section_iff_inTangentCoordinates`). The gluing follows
that of Tau Ceti's `Bundle.Pullback.exists_contMDiff_hom_map_I_eq_cast`.

Together the two factors give the frame along a smooth immersion `ι : ℝᵏ → M`, such as a disc,
with totally real tangent images, when `dim_ℂ E = k + m`. The differential of an immersion is
injective, so the extension of `dι x` is injective on `ℂᵏ`. It is smooth in tangent
coordinates, and hence continuous as a map `ℝᵏ × ℂᵏ → TM`
(`SymplecticGeometry.continuous_of_continuousAt_inTangentCoordinates`), and `ℝᵏ` is
contractible, so it has a smooth complex complement `B`. The frame
`A x = (extension of dι x, B x) : ℂᵏ × ℂᵐ → T_(ι x) M` then agrees with `dι x` on the image
`ℝᵏ × 0` of the model disc `SymplecticGeometry.modelDisc`.

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
* `SymplecticGeometry.exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod_of_continuous`:
  along a smooth map, a continuous complex complement of a family smooth in tangent coordinates
  can be replaced by one smooth in tangent coordinates.
* `SymplecticGeometry.exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod`: over a
  contractible manifold, a family of injective complex-linear maps into the tangent spaces, smooth
  in tangent coordinates, extends to a family of complex-linear isomorphisms smooth in tangent
  coordinates.
* `SymplecticGeometry.exists_complexFrame_mfderiv`: along a smooth immersion of `ℝᵏ` with totally
  real tangent images there is a frame `ℂᵏ × ℂᵐ → T_(ι x) M`, invertible, complex linear and
  smooth in tangent coordinates, that restricts to `dι x` along the model disc.

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

/-- The underlying real manifold of the complex manifold `M`. -/
private local instance : IsManifold 𝓘(ℝ, E) ∞ M :=
  IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) ∞ M)

section ContinuousComplement

open _root_.Bundle Function Module TauCeti.SmoothAlmostComplexStructure

variable [FiniteDimensional ℂ E]
  {Y : Type*} [TopologicalSpace Y] [R1Space Y] [ParacompactSpace Y] [ContractibleSpace Y]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]

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
  have := Complex.fact_finrank_real_eq_two_mul_finrank E
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

section Smoothing

open _root_.Bundle Function Module TauCeti.SmoothAlmostComplexStructure

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]

/-- On a neighbourhood `U` of each point `x₀` there is a family `s` of complex-linear maps,
smooth in tangent coordinates at the points of `U`, whose defect
`(L y, B₀ y)⁻¹ ∘ (s y - B₀ y) ∘ snd` from `B₀` has norm less than `1`: the map `B₀ x₀`, carried
to the tangent spaces along `ι` by the tangent coordinate changes. This is the local step of
`exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod_of_continuous`, with the maps read
in the model space `E`. -/
private theorem exists_mem_nhds_frame_near [IsManifold 𝓘(ℝ, E) 1 M]
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [FiniteDimensional ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    {ι : X → M} (hι : ContMDiff IX 𝓘(ℝ, E) ∞ ι) {f₁ : X → G₁} {L : X → G₁ →L[ℝ] E}
    (hL : ∀ x₀, ContMDiffAt IX 𝓘(ℝ, G₁ →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, G₁) 𝓘(ℝ, E) f₁ ι L x₀) x₀)
    {B₀ : X → G₂ →L[ℝ] E}
    (hB₀ : Continuous fun q : X × G₂ ↦ (⟨ι q.1, B₀ q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hB₀I : ∀ x v, B₀ x (Complex.I • v) = Complex.I • B₀ x v)
    (hB₀L : ∀ x, ((L x).coprod (B₀ x)).IsInvertible) (x₀ : X) :
    ∃ U ∈ 𝓝 x₀, ∃ s : X → G₂ →L[ℝ] E,
      (∀ y ∈ U, ContMDiffAt IX 𝓘(ℝ, G₂ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, G₂) 𝓘(ℝ, E) (0 : X → G₂) ι s y) y) ∧
      ∀ y ∈ U, (∀ v, s y (Complex.I • v) = Complex.I • s y v) ∧
        ((L y).coprod (B₀ y)).inverse ∘L (s y - B₀ y) ∘L snd ℝ G₁ G₂ ∈ Metric.ball 0 1 := by
  -- Near `x₀`, read everything in the tangent coordinates at `ι x₀`.
  let Ω : Set X := ι ⁻¹' (chartAt E (ι x₀)).source
  have hΩ : IsOpen Ω := (chartAt E (ι x₀)).open_source.preimage hι.continuous
  have hx₀Ω : x₀ ∈ Ω := mem_chart_source E (ι x₀)
  let T (y : X) : E →L[ℝ] E := tangentCoordChange 𝓘(ℝ, E) (ι y) (ι x₀) (ι y)
  let R (y : X) : E →L[ℝ] E := tangentCoordChange 𝓘(ℝ, E) (ι x₀) (ι y) (ι y)
  have hsrc (y : X) (hy : y ∈ Ω) :
      ι y ∈ (extChartAt 𝓘(ℝ, E) (ι x₀)).source ∧ ι y ∈ (extChartAt 𝓘(ℝ, E) (ι y)).source :=
    ⟨by rwa [extChartAt_source], mem_extChartAt_source (ι y)⟩
  have hRT (y : X) (hy : y ∈ Ω) : R y ∘L T y = .id ℝ E :=
    tangentCoordChange_comp_tangentCoordChange _ (hsrc y hy).2 (hsrc y hy).1
  have hTinv (y : X) (hy : y ∈ Ω) : (T y).IsInvertible :=
    isInvertible_tangentCoordChange _ (hsrc y hy).2 (hsrc y hy).1
  have hTinverse (y : X) (hy : y ∈ Ω) : (T y).inverse = R y :=
    inverse_tangentCoordChange _ (hsrc y hy).2 (hsrc y hy).1
  have hT₀ : T x₀ = .id ℝ E := by
    ext v
    exact tangentCoordChange_self (hsrc x₀ hx₀Ω).1
  -- The coordinates of `L` and `B₀` are continuous at `x₀`.
  have hLc : ContinuousAt (fun y ↦ T y ∘L L y) x₀ :=
    (hL x₀).continuousAt.congr (Filter.eventually_of_mem (hΩ.mem_nhds hx₀Ω)
      fun y hy ↦ inTangentCoordinates_eq_tangentCoordChange_comp _ L hy)
  have hBc : ContinuousAt (fun y ↦ T y ∘L B₀ y) x₀ :=
    (continuousAt_inTangentCoordinates_of_continuous 𝓘(ℝ, E) (f := (0 : X → G₂)) hB₀ x₀).congr
      (Filter.eventually_of_mem (hΩ.mem_nhds hx₀Ω)
        fun y hy ↦ inTangentCoordinates_eq_tangentCoordChange_comp _ B₀ hy)
  let A' (y : X) : G₁ × G₂ →L[ℝ] E := (T y ∘L L y).coprod (T y ∘L B₀ y)
  have hA' (y : X) : A' y = T y ∘L (L y).coprod (B₀ y) := (comp_coprod _ _ _).symm
  have hA'c : ContinuousAt A' x₀ :=
    (coprodEquivL (S := ℝ)).continuous.continuousAt.comp (f := fun y ↦ (_, _)) (hLc.prodMk hBc)
  have hA'₀ : A' x₀ = (L x₀).coprod (B₀ x₀) := by rw [hA', hT₀, ContinuousLinearMap.id_comp]
  have hinvc : ContinuousAt (fun y ↦ (A' y).inverse) x₀ := by
    have hinv : ContinuousAt (ContinuousLinearMap.inverse : (G₁ × G₂ →L[ℝ] E) → _) (A' x₀) := by
      rw [hA'₀]
      exact ((hB₀L x₀).contDiffAt_map_inverse (n := 0)).continuousAt
    exact hinv.comp hA'c
  -- The defect of the local section, in coordinates.
  let Q (y : X) : G₁ × G₂ →L[ℝ] G₁ × G₂ :=
    (A' y).inverse ∘L (B₀ x₀ - T y ∘L B₀ y) ∘L snd ℝ G₁ G₂
  have hQc : ContinuousAt Q x₀ :=
    hinvc.clm_comp ((continuousAt_const.sub hBc).clm_comp continuousAt_const)
  have hQ₀ : Q x₀ = 0 := by simp [Q, hT₀]
  refine ⟨Ω ∩ Q ⁻¹' Metric.ball 0 1, inter_mem (hΩ.mem_nhds hx₀Ω)
    (hQc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by simp [hQ₀]))),
    fun y ↦ R y ∘L B₀ x₀, fun y₁ hy₁ ↦
      contMDiffAt_inTangentCoordinates_tangentCoordChange_comp 𝓘(ℝ, E) (hι y₁) hy₁.1 (B₀ x₀), ?_⟩
  rintro y ⟨hy, hQy⟩
  have hy' : ι y ∈ (chartAt E (ι x₀)).source ∩ (chartAt E (ι y)).source :=
    ⟨hy, mem_chart_source E (ι y)⟩
  refine ⟨fun v ↦ ?_, ?_⟩
  · simp only [ContinuousLinearMap.comp_apply]
    rw [hB₀I, tangentCoordChange_complex_smul hy']
  · have hPQ : ((L y).coprod (B₀ y)).inverse ∘L (R y ∘L B₀ x₀ - B₀ y) ∘L snd ℝ G₁ G₂ = Q y := by
      simp only [Q, hA' y, (hTinv y hy).inverse_comp_of_left, hTinverse y hy,
        ContinuousLinearMap.comp_assoc]
      have hRTv (w : E) : R y (T y w) = w := by
        rw [← ContinuousLinearMap.comp_apply, hRT y hy, ContinuousLinearMap.id_apply]
      ext p <;> simp [hRTv]
    rw [hPQ]
    exact hQy

/-- **Smoothing a complex complement.** Let `ι : X → M` be a smooth map from a σ-compact
Hausdorff finite-dimensional manifold into a complex manifold, `L x : G₁ → T_(ι x) M` a family of
real-linear maps smooth in tangent coordinates, and `B₀ x : G₂ → T_(ι x) M` complex-linear maps,
continuous as a map `X × G₂ → TM`, such that each `(L x, B₀ x) : G₁ × G₂ → T_(ι x) M` is an
isomorphism. Then there are complex-linear maps `B x : G₂ → T_(ι x) M`, smooth in tangent
coordinates, such that each `(L x, B x)` is again an isomorphism.

The family `B` is a smooth section, glued by a partition of unity
(`exists_contMDiffSection_forall_mem_convex_of_local`), of the bundle of maps from the trivial
bundle `ι^* G₂` to `ι^* TM`, with values in the convex sets of complex-linear maps `B` for which
`(L x, B₀ x)⁻¹ ∘ (B - B₀ x) ∘ snd` has norm less than `1`. -/
theorem exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod_of_continuous
    [IsManifold IX ∞ X] [FiniteDimensional ℝ EX] [T2Space X] [SigmaCompactSpace X]
    [IsManifold 𝓘(ℝ, E) 1 M]
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [FiniteDimensional ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    {ι : X → M} (hι : ContMDiff IX 𝓘(ℝ, E) ∞ ι) {f₁ : X → G₁}
    {L : ∀ x, G₁ →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x)}
    (hL : ∀ x₀, ContMDiffAt IX 𝓘(ℝ, G₁ →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, G₁) 𝓘(ℝ, E) f₁ ι L x₀) x₀)
    {B₀ : ∀ x, G₂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x)}
    (hB₀ : Continuous fun q : X × G₂ ↦ (⟨ι q.1, B₀ q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M))
    (hB₀I : ∀ x v, B₀ x (Complex.I • v) = ofComplexManifold E M (ι x) (B₀ x v))
    (hB₀L : ∀ x, ((L x).coprod (B₀ x)).IsInvertible) :
    ∃ B : ∀ x, G₂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x),
      (∀ (f₂ : X → G₂) x₀, ContMDiffAt IX 𝓘(ℝ, G₂ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, G₂) 𝓘(ℝ, E) f₂ ι B x₀) x₀) ∧
      (∀ x v, B x (Complex.I • v) = ofComplexManifold E M (ι x) (B x v)) ∧
      ∀ x, ((L x).coprod (B x)).IsInvertible := by
  -- `L` and `B₀` as families of maps into the fixed space `E`.
  let L' (x : X) : G₁ →L[ℝ] E := L x
  let B₀' (x : X) : G₂ →L[ℝ] E := B₀ x
  replace hB₀I (x : X) (v : G₂) : B₀' x (Complex.I • v) = Complex.I • B₀' x v :=
    (hB₀I x v).trans (ofComplexManifold_apply _ _)
  let ιc : C(X, M) := ⟨ι, hι.continuous⟩
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := G₂) (E := Trivial M G₂)
    (IB := 𝓘(ℝ, E)) (f := ιc) hι
  have := Bundle.Pullback.contMDiffVectorBundle (n := ∞) (F := E)
    (E := TangentSpace 𝓘(ℝ, E)) (IB := 𝓘(ℝ, E)) (f := ιc) hι
  let Z (x : X) :=
    ((ιc : X → M) *ᵖ (Trivial M G₂)) x →L[ℝ] ((ιc : X → M) *ᵖ (TangentSpace 𝓘(ℝ, E))) x
  -- The fibres of `Z` are those of `G₂ →L[ℝ] E`.
  let toE (x : X) (B : Z x) : G₂ →L[ℝ] E := B
  -- The defect of `B` from `B₀ x`, read in the frame `(L x, B₀ x)`.
  let P (x : X) (B : G₂ →L[ℝ] E) : G₁ × G₂ →L[ℝ] G₁ × G₂ :=
    ((L' x).coprod (B₀' x)).inverse ∘L (B - B₀' x) ∘L snd ℝ G₁ G₂
  let t (x : X) : Set (Z x) := {B | (∀ v, toE x B (Complex.I • v) =
    Complex.I • toE x B v) ∧ P x (toE x B) ∈ Metric.ball 0 1}
  have hconv (x : X) : Convex ℝ (t x) := by
    rintro B ⟨hBI, hBP⟩ B' ⟨hB'I, hB'P⟩ a b ha hb hab
    have hE : toE x (a • B + b • B') = a • toE x B + b • toE x B' := rfl
    refine ⟨fun v ↦ ?_, ?_⟩
    · rw [hE, add_apply, smul_apply, smul_apply, hBI, hB'I, add_apply, smul_apply, smul_apply,
        smul_add, smul_comm a, smul_comm b]
    · obtain rfl : b = 1 - a := by linarith
      have hPab : P x (toE x (a • B + (1 - a) • B')) =
          a • P x (toE x B) + (1 - a) • P x (toE x B') := by
        have hsub : a • toE x B + (1 - a) • toE x B' - B₀' x =
            a • (toE x B - B₀' x) + (1 - a) • (toE x B' - B₀' x) := by module
        simp only [hE, P, hsub, comp_add, comp_smul, add_comp, smul_comp]
      rw [hPab]
      exact convex_ball 0 1 hBP hB'P ha hb hab
  have hloc (x₀ : X) : ∃ U ∈ 𝓝 x₀, ∃ s : ∀ x, Z x,
      ContMDiffOn IX (IX.prod 𝓘(ℝ, G₂ →L[ℝ] E)) ∞
        (fun x ↦ TotalSpace.mk' (G₂ →L[ℝ] E) x (s x)) U ∧ ∀ y ∈ U, s y ∈ t y := by
    obtain ⟨U, hU, s, hs, hst⟩ :=
      exists_mem_nhds_frame_near hι (L := L') hL hB₀ hB₀I hB₀L x₀
    exact ⟨U, hU, s, fun y hy ↦
      ((Bundle.Pullback.contMDiffAt_hom_trivial_section_iff_inTangentCoordinates ιc (hι y) 0
        s).2 (hs y hy)).contMDiffWithinAt, hst⟩
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local IX Z t hconv hloc
  refine ⟨fun x ↦ σ x, fun f₂ x₀ ↦ ?_,
    fun x v ↦ ((hσ x).1 v).trans (ofComplexManifold_apply _ _).symm, fun x ↦ ?_⟩
  · exact (Bundle.Pullback.contMDiffAt_hom_trivial_section_iff_inTangentCoordinates ιc (hι x₀) f₂
      (fun x ↦ σ x)).1 (σ.contMDiff x₀)
  · -- Read the maps in the normed space `E`, which the tangent spaces are only up to unfolding.
    change ((L' x).coprod (toE x (σ x))).IsInvertible
    refine (show ((L' x).coprod (B₀' x)).IsInvertible from
      hB₀L x).of_norm_inverse_comp_sub_lt_one ?_
    have hsub : (L' x).coprod (toE x (σ x)) - (L' x).coprod (B₀' x) =
        (toE x (σ x) - B₀' x) ∘L snd ℝ G₁ G₂ := by
      ext p <;> simp
    rw [hsub]
    exact mem_ball_zero_iff.1 (hσ x).2

/-- **A smooth complex complement along a map from a contractible manifold.** Let `ι : X → M` be
a smooth map from a contractible σ-compact Hausdorff finite-dimensional manifold into a complex
manifold modelled on a finite-dimensional space `E`, and `L x : G₁ → T_(ι x) M` injective
complex-linear maps, smooth in tangent coordinates. If `dim G₁ + dim G₂ = dim E`, there are
complex-linear maps `B x : G₂ → T_(ι x) M`, smooth in tangent coordinates, such that each
`(L x, B x) : G₁ × G₂ → T_(ι x) M` is an isomorphism.

This is `exists_continuous_isInvertible_coprod_tangentSpace`, made smooth by
`exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod_of_continuous`. The continuity of
`L` as a map `X × G₁ → TM` that the former asks for follows from its smoothness in tangent
coordinates (`continuous_of_continuousAt_inTangentCoordinates`). -/
theorem exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod
    [IsManifold IX ∞ X] [FiniteDimensional ℝ EX] [T2Space X] [SigmaCompactSpace X]
    [ContractibleSpace X] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℝ, E) 1 M]
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    (hdim : finrank ℂ E = finrank ℂ G₁ + finrank ℂ G₂)
    {ι : X → M} (hι : ContMDiff IX 𝓘(ℝ, E) ∞ ι) {f₁ : X → G₁}
    {L : ∀ x, G₁ →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x)}
    (hL : ∀ x₀, ContMDiffAt IX 𝓘(ℝ, G₁ →L[ℝ] E) ∞
      (inTangentCoordinates 𝓘(ℝ, G₁) 𝓘(ℝ, E) f₁ ι L x₀) x₀)
    (hLI : ∀ x v, L x (Complex.I • v) = ofComplexManifold E M (ι x) (L x v))
    (hinj : ∀ x, Injective (L x)) :
    ∃ B : ∀ x, G₂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (ι x),
      (∀ (f₂ : X → G₂) x₀, ContMDiffAt IX 𝓘(ℝ, G₂ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, G₂) 𝓘(ℝ, E) f₂ ι B x₀) x₀) ∧
      (∀ x v, B x (Complex.I • v) = ofComplexManifold E M (ι x) (B x v)) ∧
      ∀ x, ((L x).coprod (B x)).IsInvertible := by
  have := Manifold.locallyCompact_of_finiteDimensional IX (M := X)
  have hLc : Continuous fun q : X × G₁ ↦ (⟨ι q.1, L q.1 q.2⟩ : TangentBundle 𝓘(ℝ, E) M) :=
    continuous_of_continuousAt_inTangentCoordinates 𝓘(ℝ, E) hι.continuous fun x₀ ↦
      (hL x₀).continuousAt
  obtain ⟨B₀, hB₀, hB₀I, hB₀L⟩ :=
    exists_continuous_isInvertible_coprod_tangentSpace (G₂ := G₂) hdim hLc hLI hinj
  exact exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod_of_continuous hι hL hB₀
    hB₀I hB₀L

end Smoothing

section Frame

open Function Module TauCeti.SmoothAlmostComplexStructure

variable {m : ℕ} [FiniteDimensional ℂ E]

/-- **Complex frames along a totally real disc.** Let `M` be a complex manifold modelled on `E`,
with `dim_ℂ E = k + m`, and `ι : ℝᵏ → M` a smooth immersion whose tangent images are totally
real. There are real-linear maps `A x : ℂᵏ × ℂᵐ → T_(ι x) M`, smooth in tangent coordinates along
the model disc `modelDisc k m`, each invertible and complex linear, such that `A x` composed
with the differential of `modelDisc k m` at `x` is the differential of `ι` at `x`.

For an embedding `ι`, these are the data that Tau Ceti's
`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mfderiv_eq` asks for to extend
`ι ∘ (modelDisc k m)⁻¹` to a partial diffeomorphism with differential `A x` along the disc.
Complex linearity is stated with `ofComplexManifold E M`, which is multiplication by `i` on each
tangent space (`ofComplexManifold_apply`). -/
theorem exists_complexFrame_mfderiv {ι : EuclideanSpace ℝ (Fin k) → M}
    (hι : IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ∞ ι)
    (hιR : ∀ x, IsTotallyReal ((ofComplexManifold E M).toEndomorphism (ι x)).toLinearMap
      (LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x).toLinearMap))
    (hdim : finrank ℂ E = k + m) :
    ∃ A : ∀ x, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ]
        TangentSpace 𝓘(ℝ, E) (ι x),
      (∀ x₀, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
        𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m))
          𝓘(ℝ, E) (modelDisc k m) ι A x₀) x₀) ∧
      (∀ x, (A x).IsInvertible) ∧
      (∀ x v, A x (Complex.I • v) = ofComplexManifold E M (ι x) (A x v)) ∧
      ∀ x, (A x).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
          𝓘(ℝ, EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m)) (modelDisc k m) x) =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x := by
  have hιs := hι.contMDiff
  -- The first factor: the complex-linear extension of the differential of `ι`.
  let L (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℂ (Fin k) →L[ℝ] E :=
    complexExtension (Fin k) E (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, E) ι x)
  have hL (f₁ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℂ (Fin k)) x₀ :=
    contMDiffAt_inTangentCoordinates_complexExtension_mfderiv (hιs x₀) f₁
  have hLI (x : EuclideanSpace ℝ (Fin k)) (v : EuclideanSpace ℂ (Fin k)) :
      L x (Complex.I • v) = Complex.I • L x v :=
    complexExtension_apply_I_smul _ v
  have hinj (x : EuclideanSpace ℝ (Fin k)) : Injective (L x) :=
    complexExtension_mfderiv_injective (hι.mfderiv_injective (by simp) x) (hιR x)
  -- The second factor: a smooth complex complement.
  obtain ⟨B, hB, hBI, hBL⟩ := exists_contMDiffAt_inTangentCoordinates_isInvertible_coprod
    (G₂ := EuclideanSpace ℂ (Fin m)) (by simp [hdim]) hιs (hL 0)
    (fun x v ↦ (hLI x v).trans (ofComplexManifold_apply _ _).symm) hinj
  -- Read `B` as a family of maps into the model space `E`, as `L` is.
  let B' (x : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℂ (Fin m) →L[ℝ] E := B x
  have hBI' (x : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℂ (Fin m)) :
      B' x (Complex.I • w) = Complex.I • B' x w :=
    (hBI x w).trans (ofComplexManifold_apply _ _)
  let A (x : EuclideanSpace ℝ (Fin k)) :
      EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin m) →L[ℝ] E :=
    (L x).coprod (B' x)
  have hA (x : EuclideanSpace ℝ (Fin k)) (z : EuclideanSpace ℂ (Fin k))
      (w : EuclideanSpace ℂ (Fin m)) : A x (z, w) = L x z + B' x w :=
    coprod_apply _ _ _
  refine ⟨A, fun x₀ ↦ ?_, hBL, fun x v ↦ ?_, fun x ↦ ?_⟩
  · exact (hL (fun x ↦ (modelDisc k m x).1) x₀).inTangentCoordinates_clm_coprod (A := L)
      (B := B) 𝓘(ℝ, E) (hB (fun x ↦ (modelDisc k m x).2) x₀)
  · -- `A x` takes values in `E`, which the tangent space is only up to unfolding.
    refine (?_ : A x (Complex.I • v) = Complex.I • A x v).trans (ofComplexManifold_apply _ _).symm
    obtain ⟨z, w⟩ := v
    rw [Prod.smul_mk, hA, hA, hLI, hBI', smul_add]
  · ext x'
    rw [mfderiv_modelDisc]
    have hAx : A x (modelDisc k m x') = L x (modelDisc k m x').1 := by
      rw [show modelDisc k m x' = ((modelDisc k m x').1, 0) from
        Prod.ext rfl (modelDisc_apply_snd x'), hA, map_zero, add_zero]
    have hx' : (modelDisc k m x').1 = (complexEuclideanEquivRealProd (Fin k)).symm (x', 0) :=
      (complexEuclideanEquivRealProd (Fin k)).eq_symm_apply.mpr
        (complexEuclideanEquivRealProd_modelDisc_fst x')
    refine (ContinuousLinearMap.comp_apply _ _ _).trans (hAx.trans ?_)
    rw [hx']
    exact complexExtension_apply_symm_real _ x'

end Frame

end SymplecticGeometry
