/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev
import SymplecticGeometry.Analysis.Complex.Beltrami.ZeroOnePart
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.ZeroOnePart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Tames

/-!
# Local form of the kernel of `D_J` on `𝒪(1)`

This file reads the equation `D_J w = 0` in the charts of the atlas `twistCoreAtlas 1`, for an
almost complex structure `J` on the sphere `OnePoint ℂ` and the Cauchy–Riemann operator
`D_J = twistOneDelBarSobolev J 0 : W^{1,2}(𝒪(1)) → W^{0,2}(Λ^{0,1} ⊗ 𝒪(1))` of
`SymplecticGeometry.Geometry.Manifold.Instances.OnePoint.CauchyRiemann.Sobolev`.

In chart `i`, let `u` be the chart data of `w`, `Du` a weak derivative of `u` on the chart image,
`Γ` the zeroth-order term `chartZeroOrder` of the connection `twistOneConnection`, and
`K = J.inChart (twistCoreAtlas 1).center i` the reading of `J`. The chart data of `∇w` are the
one-forms `L y = Du y + Γ y (u y)` (`IsCovariantDerivativeOn.chartValueL_sobolevL_ae`). When a
two-form tames both `J` and the standard structure `i` of the sphere, `D_J w = 0` holds exactly
when, in every chart, `L y` is complex linear for `K y` at almost every point of the chart image:
`L y (K y v) = i L y v` (`SymplecticGeometry.twistOneDelBarSobolev_eq_zero_iff`).

The proof reads each factor of `D_J = π^{0,1}_i ∘ Φ_J ∘ ∇` in the chart. The chart data of
`Φ_J ∇w` are the chart reading of the field `zeroOnePartL J` applied to `L`
(`TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae`), so the `(0,1)`-part for `i` of
those data is the complex-antilinear part of `½ (L + i L ∘ K)`
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart_zeroOnePart`). Tau Ceti's
`TauCeti.zeroOnePartSobolevL_eq_zero_iff` says that `D_J w = 0` exactly when these parts vanish
almost everywhere in every chart. Taming gives `K 1 ≠ -i`
(`TauCeti.SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames`), and then that
complex-antilinear part vanishes exactly when `L ∘ K = i L`
(`ContinuousLinearMap.complexAntilinearPartL_half_smul_add_I_smul_comp_eq_zero_iff`).

## Main results

* `SymplecticGeometry.twistOneDelBarSobolev_eq_zero_iff`: for `J` tamed together with `i` by a
  two-form, a `W^{1,2}` section `w` of `𝒪(1)` satisfies `D_J w = 0` exactly when, in every chart
  of `twistCoreAtlas 1`, the chart data of `∇w` are complex linear for `J` almost everywhere.

## References

* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1 and C.2.
-/

public section

open Bundle MeasureTheory TauCeti
open OnePoint (twistCore)
open scoped Manifold ContDiff ENNReal TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

namespace SymplecticGeometry

/-- The standard complex structure of the Riemann sphere. -/
local notation "𝒊" => SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)

variable {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)}

/-- At a point `y` of the image of chart `i` of `twistCoreAtlas 1`, the chart reading of the
field `zeroOnePartL J` of `(0,1)`-projections sends a one-form `L` to a complex-linear one exactly
when `L` is complex linear for the reading of `J` at `y`, if a two-form tames `J` and `i`. -/
private theorem coord_hom_zeroOnePartL_apply_I_smul_iff {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) (i : Fin (twistCoreAtlas 1).n) {y : ℂ}
    (hy : y ∈ (twistCoreAtlas 1).image i) (L : ℂ →L[ℝ] ℂ) :
    (∀ v : ℂ, ((twistCoreAtlas 1).tangentHom.hom (𝕜 := ℝ)
        (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet).coord i J.zeroOnePartL y L
          (Complex.I • v) =
        Complex.I • ((twistCoreAtlas 1).tangentHom.hom (𝕜 := ℝ)
          (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet).coord i J.zeroOnePartL y L v) ↔
      ∀ v : ℂ, L (J.inChart ((twistCoreAtlas 1).center i) y v) = Complex.I • L v := by
  have hyT : y ∈ (twistCoreAtlas 1).tangentHom.image i := by
    rwa [FiniteBundleAtlas.image_tangentHom]
  have hyt : y ∈ (extChartAt 𝓘(ℝ, ℂ) ((twistCoreAtlas 1).center i)).target := by
    simpa using ((twistCoreAtlas 1).chart_image_closure_dom_subset i
      ((twistCoreAtlas 1).image_subset_chart_image_closure_dom i hy)).1
  -- A one-form whose reading at `y` is `L`.
  set η : Π x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x :=
    fun x ↦ ((twistCoreAtlas 1).tangentHom.triv i).symm x L
  have hη : (twistCoreAtlas 1).tangentHom.coord i η y = L :=
    FiniteBundleAtlas.coord_triv_symm _ L hyT
  have hc := FiniteBundleAtlas.coord_hom_apply (twistCoreAtlas 1).tangentHom
    (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet i (fun x ↦ J.zeroOnePartL x) η hyT
  simp only [hη, SmoothAlmostComplexStructure.zeroOnePartL_apply] at hc
  -- The atlas `A.tangentHom.ofBaseSet _` on the right of `hc` is `A.tangentHom` itself, by the
  -- eta rule for structures, so `hc` rewrites the reading of `J.zeroOnePart η`.
  rw [hc, ← ContinuousLinearMap.complexAntilinearPartL_eq_zero_iff]
  change ContinuousLinearMap.complexAntilinearPartL
      ((twistCoreAtlas 1).tangentHom.coord i (fun x ↦ J.zeroOnePart (η x)) y) = 0 ↔ _
  rw [← FiniteBundleAtlas.coord_tangentHom_zeroOnePart,
    (twistCoreAtlas 1).coord_tangentHom_zeroOnePart_zeroOnePart J hy, hη]
  refine ContinuousLinearMap.complexAntilinearPartL_half_smul_add_I_smul_comp_eq_zero_iff
    (J.inChart_inChart _ hyt) (fun h ↦ ?_) L
  have := SmoothAlmostComplexStructure.im_inChart_apply_one_pos_of_tames hJ hi _ hyt
  rw [h] at this
  norm_num at this

/-- **The kernel equation of `D_J` in the charts.** Let a two-form `σ` tame both `J` and the
standard structure `i` of the sphere, and let `w` be a `W^{1,2}` section of `𝒪(1)`. Then
`D_J w = 0` exactly when, for every chart `i` of `twistCoreAtlas 1` and every weak derivative
`Du` of the chart data `u` of `w` on the chart image, the one-form `L y = Du y + Γ y (u y)`, for
the zeroth-order term `Γ` of the connection in chart `i`, is complex linear for the reading
`K = J.inChart (twistCoreAtlas 1).center i` of `J` at almost every point `y` of the chart image:
`L y (K y v) = i L y v` for all `v`. -/
theorem twistOneDelBarSobolev_eq_zero_iff {σ : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ)}
    (hJ : σ.Tames J) (hi : σ.Tames 𝒊) {w : SobolevSection (twistCoreAtlas 1) volume 2 1} :
    twistOneDelBarSobolev J 0 w = 0 ↔
      ∀ (i : Fin (twistCoreAtlas 1).n) {Du : ℂ → ℂ →L[ℝ] ℂ},
        HasWeakFDerivOn volume ((twistCoreAtlas 1).image i)
          ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w) Du →
        ∀ᵐ y ∂volume.restrict ((twistCoreAtlas 1).image i), ∀ v : ℂ,
          (Du y + (twistCoreAtlas 1).chartZeroOrder twistOneConnection i y
              ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w y))
              (J.inChart ((twistCoreAtlas 1).center i) y v) =
            Complex.I • (Du y + (twistCoreAtlas 1).chartZeroOrder twistOneConnection i y
              ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w y)) v := by
  -- The chart data of `Φ_J ∇w` are the reading of `Φ_J` applied to those of `∇w`, which are
  -- `Du + Γ u` for any weak derivative `Du`.
  have hΦ (i : Fin (twistCoreAtlas 1).n) := by
    have := SobolevSection.chartValueL_contMDiffHomMulL_ae
      (h := (twistCoreAtlas 1).tangentHom.closure_dom_subset_baseSet)
      (J.contMDiff_zeroOnePartL le_rfl)
      (isCovariantDerivativeOn_twistOneConnection.sobolevL (twistCoreAtlas 1)
        (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 0 w) i
    rwa [FiniteBundleAtlas.image_tangentHom] at this
  have hcov (i : Fin (twistCoreAtlas 1).n) {Du : ℂ → ℂ →L[ℝ] ℂ}
      (hDu : HasWeakFDerivOn volume ((twistCoreAtlas 1).image i)
        ((twistCoreAtlas 1).sectionChartData.chartValueL volume 2 1 i w) Du) :=
    isCovariantDerivativeOn_twistOneConnection.chartValueL_sobolevL_ae (twistCoreAtlas 1)
      (contMDiffCovariantDerivativeOn_twistOneConnection ⊤) volume 2 0 w hDu
  rw [twistOneDelBarSobolev_apply]
  refine zeroOnePartSobolevL_eq_zero_iff.trans ⟨fun h i Du hDu ↦ ?_, fun h i ↦ ?_⟩
  · filter_upwards [(FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).1 (h i),
      hΦ i, hcov i hDu, ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet]
      with y hy1 hy2 hy3 hy
    refine (coord_hom_zeroOnePartL_apply_I_smul_iff hJ hi i hy _).1 fun v ↦ ?_
    have := hy1 v
    -- `hy2` is about the atlas `A.tangentHom.ofBaseSet _`, which is `A.tangentHom` itself.
    erw [hy2, hy3] at this
    exact this
  · have hDu := (twistCoreAtlas 1).sectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL
      volume 2 0 i w
    refine (FiniteBundleAtlas.ae_image_tangentHom_iff (twistCoreAtlas 1) volume i).2 ?_
    filter_upwards [h i hDu, hΦ i, hcov i hDu,
      ae_restrict_mem ((twistCoreAtlas 1).image i).isOpen.measurableSet] with y hy1 hy2 hy3 hy
    intro v
    -- `hy2` is about the atlas `A.tangentHom.ofBaseSet _`, which is `A.tangentHom` itself.
    erw [hy2, hy3]
    exact (coord_hom_zeroOnePartL_apply_I_smul_iff hJ hi i hy _).2 hy1 v

end SymplecticGeometry

end
