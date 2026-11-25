/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Measure
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.MeasureTheory.Measure.Haar.InnerProductSpace
import SymplecticGeometry.MeasureTheory.Measure.Lebesgue.HalfSqRadius

/-!
# Integrating the symplectic volume form

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M` modelled on a space of dimension
`2 * n`, with its symplectic orientation
(`TauCeti.SmoothTwoForm.IsNondegenerate.volumeOrientation`),
the orientation on which the volume form `σⁿ / n!` is positive. This file shows that integrating
the top form `f σⁿ / n!` against the symplectic orientation is integrating `f` against the
Liouville measure `|σⁿ / n!|` (`TauCeti.SmoothTwoForm.liouvilleMeasure`), for every continuous
compactly supported function `f`:

`∫_M f σⁿ / n! = ∫ f dλ_σ`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_smul_volumeForm`). It is the case of the
symplectic volume form of `TauCeti.integralTopForm_smul_eq_integral_measure`, and holds in every
dimension, including dimension `0`.

It also computes Liouville integrals in symplectic coordinates. A partial diffeomorphism
`Φ : N → M` that pulls `σ` back to a two-form `τ` on its source carries the Liouville measure of
`τ` on the source to that of `σ` on the target
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn.map_restrict_liouvilleMeasure`), so that
`∫ f dλ_σ = ∫_{Φ.source} f ∘ Φ dλ_τ` for every `f` vanishing outside the target
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn.integral_liouvilleMeasure`). The manifolds `N` and `M`
may be modelled on different spaces of the same dimension; the proof restricts `Φ` to its open
source and applies `MeasurableEmbedding.map_measure_mpullback` there. On the standard
space `StdSpace ι` with the constant form `ω₀ = stdForm ι`, the Liouville measure is Lebesgue
measure (`SymplecticGeometry.liouvilleMeasure_constSmooth_stdForm`), so a symplectic chart from
`StdSpace (Fin n)` turns a Liouville integral into a Lebesgue integral over the chart's source
(`SymplecticGeometry.integral_liouvilleMeasure_of_isSymplecticMapOn_stdForm`). The proof of
`liouvilleMeasure_constSmooth_stdForm` follows that of Tau Ceti's
`TauCeti.SymplecticForm.liouvilleMeasure_constSmooth_stdSymplecticForm`: the Darboux basis
`SymplecticGeometry.stdDarbouxBasisOf` is the coordinate basis, reindexed, and the Haar measure
of an orthonormal basis is `volume`.

One Lebesgue integral over `StdSpace ι` is computed here, the one that the Liouville integral of
a localizing form near a fixed point comes to: for weights `wⱼ > 0` and `F` of class `C^m`
with compact support, `m` the number of elements of `ι`,
`∫ F⁽ᵐ⁾(-∑ⱼ wⱼ (xⱼ² + yⱼ²)) dz = F(0) πᵐ / ∏ⱼ wⱼ`
(`SymplecticGeometry.integral_stdSpace_iteratedDeriv_neg_sum_mul_sq`). It is
`MeasureTheory.integral_iteratedDeriv_neg_sum_mul_sq` read through
`EuclideanSpace.sumEquivProd`, which preserves Lebesgue measure
(`EuclideanSpace.volume_preserving_sumEquivProd`).

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press (2017), §5.6.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 16.
-/

public section

noncomputable section

open Module MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [hn : Fact (finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M}

/-- **Integrating the symplectic volume form is integrating against the Liouville measure.** For
a fiberwise nondegenerate two-form `σ` on a manifold modelled on a space of dimension `2 * n`,
and a continuous compactly supported function `f`, the integral of the top form `f σⁿ / n!`
against the symplectic orientation is the integral of `f` against the Liouville measure. -/
theorem IsNondegenerate.integralTopForm_smul_volumeForm (h : σ.IsNondegenerate) {f : M → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    integralTopForm (h.volumeOrientation hn.out) (fun x ↦ f x • (σ.volumeForm n).val x) =
      ∫ x, f x ∂σ.liouvilleMeasure n := by
  rw [liouvilleMeasure_def]
  -- The volume form is positive exactly on the bases of the symplectic orientation.
  exact integralTopForm_smul_eq_integral_measure _ ((σ.volumeForm n).isSmoothForm.of_le bot_le)
    (signBasis_orientationAt_mul_nonneg_of_iff _
      fun _ c ↦ h.orientation_eq_orientationAt_volumeOrientation_iff hn.out c) hf hc


/-! ### Change of variables along a symplectic partial diffeomorphism -/

section PartialDiffeomorph

open Set TopologicalSpace

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (finrank ℝ E' = 2 * n)] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N]
  [HereditarilyLindelofSpace N] {τ : SmoothTwoForm J N} {Φ : PartialDiffeomorph J I N M ∞}

/-- **Liouville measure through a symplectic partial diffeomorphism.** If a partial
diffeomorphism `Φ : N → M` pulls `σ` back to `τ` on its source, then `Φ`, restricted to its
source, carries the Liouville measure of `τ` on the source to the Liouville measure of `σ` on the
target. The two manifolds may be modelled on different spaces of the same dimension `2 * n`. -/
theorem IsSymplecticMapOn.map_comap_subtypeVal_liouvilleMeasure
    (hΦ : τ.IsSymplecticMapOn σ Φ Φ.source) :
    ((τ.liouvilleMeasure n).comap (Subtype.val : Φ.source → N)).map (Φ.source.domRestrict Φ) =
      (σ.liouvilleMeasure n).restrict Φ.target := by
  -- The source as an open submanifold of `N`; `U` is `Φ.source` by definition.
  set U : Opens N := ⟨Φ.source, Φ.open_source⟩
  set g : U → M := U.carrier.domRestrict Φ
  have hg : MeasurableEmbedding g :=
    Φ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.measurableEmbedding
  have hgs : ContMDiff J I ∞ g := fun x ↦
    (Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds x.property)).comp x
      contMDiff_subtypeVal.contMDiffAt
  -- `g` pulls `σ` back to the restriction of `τ` to the source.
  have hpull : SmoothForm.mpullback g hgs σ =
      SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal τ :=
    (isSymplecticMap_iff_mpullback_eq hgs).1 <| isSymplecticMapOn_univ.1 <|
      hΦ.comp ((isSymplecticMap_mpullback τ _).isSymplecticMapOn _) (fun x _ ↦ x.property)
        (fun x _ ↦ Φ.mdifferentiableAt (by simp) x.property)
        (fun x _ ↦ contMDiff_subtypeVal.mdifferentiable one_ne_zero x)
  have h : mpullback J I g σ.val =
      (SmoothForm.mpullback (Subtype.val : U → N) contMDiff_subtypeVal τ).val := by
    rw [← hpull, SmoothForm.coe_mpullback]
  have hmap := hg.map_measure_mpullback (hgs.mdifferentiable (by simp)) (σ.volumeForm n).val
  rw [mpullback_volumeForm h, ← liouvilleMeasure_def, liouvilleMeasure_mpullback_subtypeVal,
    ← liouvilleMeasure_def] at hmap
  rwa [show range g = Φ.target from
    (range_domRestrict _ _).trans Φ.toPartialEquiv.image_source_eq_target] at hmap

/-- **Liouville measure through a symplectic partial diffeomorphism.** If a partial
diffeomorphism `Φ : N → M` pulls `σ` back to `τ` on its source, then it carries the Liouville
measure of `τ` restricted to its source to the Liouville measure of `σ` restricted to its
target. -/
theorem IsSymplecticMapOn.map_restrict_liouvilleMeasure (hΦ : τ.IsSymplecticMapOn σ Φ Φ.source) :
    ((τ.liouvilleMeasure n).restrict Φ.source).map Φ =
      (σ.liouvilleMeasure n).restrict Φ.target := by
  have hs := Φ.open_source.measurableSet
  have hΦm : AEMeasurable Φ ((τ.liouvilleMeasure n).restrict Φ.source) :=
    Φ.contMDiffOn.continuousOn.aemeasurable hs
  rw [← map_comap_subtypeVal hs] at hΦm ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hΦm (measurable_subtypeVal.aemeasurable)]
  exact hΦ.map_comap_subtypeVal_liouvilleMeasure

/-- **Integrals against the Liouville measure through a symplectic partial diffeomorphism.** If a
partial diffeomorphism `Φ : N → M` pulls `σ` back to `τ` on its source, then a function `f` that
vanishes outside the target of `Φ` has the same integral against the Liouville measure of `σ` as
`f ∘ Φ` has over the source against the Liouville measure of `τ`. -/
theorem IsSymplecticMapOn.integral_liouvilleMeasure {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hΦ : τ.IsSymplecticMapOn σ Φ Φ.source) {f : M → F}
    (hf : ∀ x ∉ Φ.target, f x = 0) :
    ∫ x, f x ∂σ.liouvilleMeasure n = ∫ z in Φ.source, f (Φ z) ∂τ.liouvilleMeasure n := by
  have hg : MeasurableEmbedding (Φ.source.domRestrict Φ) :=
    Φ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.measurableEmbedding
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf,
    ← hΦ.map_comap_subtypeVal_liouvilleMeasure, hg.integral_map,
    ← integral_subtype_comap Φ.open_source.measurableSet]
  simp only [domRestrict_apply]

end PartialDiffeomorph

end SmoothTwoForm

end TauCeti

namespace SymplecticGeometry

open TauCeti

/-! ### The standard symplectic space -/

/-- **The Liouville measure of the standard symplectic space is Lebesgue measure.** On
`StdSpace ι`, of dimension `2 * m`, with the constant standard form `ω₀ = ∑ᵢ dxᵢ ∧ dyᵢ`, the
Liouville measure `|ω₀ᵐ / m!|` is `volume`. -/
theorem liouvilleMeasure_constSmooth_stdForm {ι : Type*} [Fintype ι] {m : ℕ}
    [hm : Fact (finrank ℝ (StdSpace ι) = 2 * m)] :
    (stdForm ι).constSmooth.liouvilleMeasure m = volume := by
  classical
  have hι : Fintype.card ι = m := by
    have := hm.out
    rw [finrank_stdSpace] at this
    omega
  rw [SymplecticForm.liouvilleMeasure_constSmooth _
      (isDarbouxBasis_stdDarbouxBasisOf (Fintype.equivFinOfCardEq hι).symm),
    stdDarbouxBasisOf_eq_reindex, Basis.addHaar_reindex, OrthonormalBasis.addHaar_eq_volume]

/-- For weights `wⱼ > 0` and `F` of class `C^m` with compact support, where `m` is the number of
elements of `ι`, the integral over `StdSpace ι` of `F⁽ᵐ⁾(-∑ⱼ wⱼ (xⱼ² + yⱼ²))` is
`F 0 * π ^ m / ∏ⱼ wⱼ`. -/
theorem integral_stdSpace_iteratedDeriv_neg_sum_mul_sq {ι : Type*} [Fintype ι] {F : ℝ → ℝ}
    (hF : ContDiff ℝ (Fintype.card ι) F) (hFc : HasCompactSupport F) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) :
    ∫ z : StdSpace ι, iteratedDeriv (Fintype.card ι) F (-∑ j, w j * (z.x j ^ 2 + z.y j ^ 2)) =
      F 0 * Real.pi ^ Fintype.card ι / ∏ j, w j := by
  rw [← integral_iteratedDeriv_neg_sum_mul_sq hF hFc hw,
    ← (EuclideanSpace.volume_preserving_sumEquivProd _ _).integral_comp
      EuclideanSpace.sumEquivProd.toHomeomorph.measurableEmbedding]
  simp only [StdSpace.sumEquivProd_apply_fst, StdSpace.sumEquivProd_apply_snd]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [Fact (finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M}

/-- **Integrals against the Liouville measure through a symplectic chart.** If a partial
diffeomorphism `Φ` from `StdSpace (Fin n)` to `M` pulls `σ` back to the standard form on its
source, then a function `f` that vanishes outside the target of `Φ` has the same integral against
the Liouville measure of `σ` as `f ∘ Φ` has over the source against Lebesgue measure. -/
theorem integral_liouvilleMeasure_of_isSymplecticMapOn_stdForm
    {Φ : PartialDiffeomorph 𝓘(ℝ, StdSpace (Fin n)) I (StdSpace (Fin n)) M ∞}
    (hΦ : SmoothTwoForm.IsSymplecticMapOn (stdForm (Fin n)).constSmooth σ Φ Φ.source)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F}
    (hf : ∀ x ∉ Φ.target, f x = 0) :
    ∫ x, f x ∂σ.liouvilleMeasure n = ∫ z in Φ.source, f (Φ z) := by
  have : Fact (finrank ℝ (StdSpace (Fin n)) = 2 * n) := ⟨by rw [finrank_stdSpace, Fintype.card_fin]⟩
  rw [hΦ.integral_liouvilleMeasure hf, liouvilleMeasure_constSmooth_stdForm]

end SymplecticGeometry

end
