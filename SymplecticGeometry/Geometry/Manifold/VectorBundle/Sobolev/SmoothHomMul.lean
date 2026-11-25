/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import SymplecticGeometry.Analysis.Sobolev.Wkp.SmoothMultiplicationBound
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.FrameTopology
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# A smooth hom section acting on Sobolev sections

Let `M` be a smooth boundaryless manifold whose model `E` is a finite-dimensional inner product
space over `ℝ`, and let `V₁`, `V₂` be smooth real vector bundles over `M` with
finite-dimensional model fibres `F₁`, `F₂`. Let `A` be a finite bundle atlas of `V₁` whose chart
domains also serve as an atlas `A.ofBaseSet h` of `V₂`. A smooth section `Φ` of the hom bundle
`x ↦ V₁ x →L[ℝ] V₂ x` acts on the Sobolev spaces of sections:
`TauCeti.SobolevSection.contMDiffHomMulL` is a continuous linear map
`W^{k,p}(V₁) → W^{k,p}(V₂)` for every order `k` and every `1 ≤ p ≤ ∞`. In chart `i` it applies
the chart reading `(A.hom h).coord i Φ` of `Φ` to the chart data, and on actual sections it is
`s ↦ (x ↦ Φ x (s x))`
(`TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord`).

The operator norm of the action is at most a constant times a bound `M` on the derivatives of
order at most `k` of the chart readings of `Φ` on the chart images
(`TauCeti.SobolevSection.exists_norm_contMDiffHomMulL_le`). This is the local estimate
`TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le` of
`SymplecticGeometry.Analysis.Sobolev.Wkp.SmoothMultiplicationBound` in each chart, glued along the
norm of the Sobolev sections, which is the largest norm of their components
(`TauCeti.SectionChartData.norm_contDiffOnCLMApplyL_le`). With the linearity in `Φ`, the action
is then continuous in `Φ` for the `C^k` convergence of the chart readings on the chart images
(`TauCeti.SobolevSection.tendsto_contMDiffHomMulL`). In particular it is continuous in `Φ` for
the frame topology `ContMDiffSection.frameTopology` of a covering frame system on smooth sections
of the hom bundle (`TauCeti.SobolevSection.tendsto_contMDiffHomMulL_of_tendsto`), whose
convergence gives that of the chart readings by
`TauCeti.FiniteBundleAtlas.tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto`.

The construction is first carried out for general chart data
(`TauCeti.SectionChartData.contDiffOnCLMApplyL`): from the chart data `C` of one bundle to the
chart data `D` of another, whose chart `i` image lies in the image of chart `σ i` of `C`, the
chart-`σ i` components are restricted to the image of chart `i` of `D` and multiplied there by a
smooth operator-valued coefficient `g i` with `TauCeti.Wkp.contDiffOnCLMApplyL`. The result is a
tuple of components of a section as soon as applying `g` to the readings of every section gives
the readings of a section.

The construction follows Tau Ceti's `TauCeti.SectionChartData.contDiffOnSMulL` and
`TauCeti.SobolevSection.contMDiffSMulL` (`Geometry/Manifold/VectorBundle/Sobolev/SMul.lean`),
which are built in the same way from scalar multiplication `TauCeti.Wkp.contDiffOnSMulL`, with the
operator coefficient `TauCeti.Wkp.contDiffOnCLMApplyL` in place of the scalar one, as in Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.zeroOrderL` (`Sobolev/CauchyRiemann/Basic.lean` on Tau Ceti's
main branch). The proof of `TauCeti.SobolevSection.contMDiffHomMulL_ofContMDiffSection` is that of
Tau Ceti's `TauCeti.SobolevSection.contMDiffSMulL_ofContMDiffSection`. Tau Ceti's
`TauCeti.SobolevSection.homMulL` is a different operator: its coefficient is a rough Sobolev
section, and it lowers the order.

## Main definitions

* `TauCeti.SectionChartData.contDiffOnCLMApplyL`: chartwise multiplication by smooth operator
  coefficients, from the Sobolev sections of one chart data to those of another.
* `TauCeti.SobolevSection.contMDiffHomMulL`: a smooth hom section acting as an element of
  `W^{k,p}(V₁) →L[ℝ] W^{k,p}(V₂)`.

## Main results

* `TauCeti.SectionChartData.value_contDiffOnCLMApplyL_ae`,
  `TauCeti.SectionChartData.eq_contDiffOnCLMApplyL_iff`,
  `TauCeti.SectionChartData.chartValueL_contDiffOnCLMApplyL_ae`: the components and chart data of
  the product, and its characterization by its components.
* `TauCeti.SectionChartData.contDiffOnCLMApplyL_congr`: coefficients that agree on the chart images
  give the same map.
* `TauCeti.SectionChartData.contDiffOnCLMApplyL_zero`,
  `TauCeti.SectionChartData.contDiffOnCLMApplyL_add`,
  `TauCeti.SectionChartData.contDiffOnCLMApplyL_smul`,
  `TauCeti.SectionChartData.lowerOrderL_contDiffOnCLMApplyL`: linearity in the coefficient and
  compatibility with lowering the order.
* `TauCeti.SobolevSection.value_contMDiffHomMulL_ae`,
  `TauCeti.SobolevSection.eq_contMDiffHomMulL_iff`,
  `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae`: in chart `i`, the chart data of
  `Φ w` are `(A.hom h).coord i Φ y` applied to those of `w`.
* `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_self`: the same for `V₂ = V₁` and
  `h = A.closure_dom_subset_baseSet`, with the chart data of `Φ w` read in `A` itself.
* `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord`: if `w` consists of the
  components of a section `s`, then `Φ w` consists of those of `x ↦ Φ x (s x)`.
* `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord_self`: the same for `V₂ = V₁`
  and `h = A.closure_dom_subset_baseSet`, with the components of `Φ w` read in `A` itself.
* `TauCeti.SobolevSection.contMDiffHomMulL_zero`, `TauCeti.SobolevSection.contMDiffHomMulL_add`,
  `TauCeti.SobolevSection.contMDiffHomMulL_sub`, `TauCeti.SobolevSection.contMDiffHomMulL_smul`,
  `TauCeti.SobolevSection.contMDiffHomMulL_congr`,
  `TauCeti.SobolevSection.lowerOrderL_contMDiffHomMulL`: linearity in `Φ` and compatibility with
  the inclusion `W^{k+1,p} → W^{k,p}`.
* `TauCeti.SobolevSection.contMDiffHomMulL_ofContMDiffSection`: applied to the Sobolev section of a
  `Cᵏ` section `s`, the map gives the Sobolev section of `x ↦ Φ x (s x)`.
* `TauCeti.SectionChartData.norm_contDiffOnCLMApplyL_le`: a bound on the chartwise products
  bounds the product between the Sobolev sections.
* `TauCeti.SobolevSection.exists_norm_contMDiffHomMulL_le`,
  `TauCeti.SobolevSection.exists_norm_contMDiffHomMulL_sub_le`: the operator norm, and the distance
  between the actions of two hom sections, are bounded by a constant times the `C^k` size of the
  chart readings on the chart images.
* `TauCeti.SobolevSection.tendsto_contMDiffHomMulL`: continuity in the hom section.
* `TauCeti.SobolevSection.tendsto_contMDiffHomMulL_of_tendsto`: continuity in the hom section for
  the frame topology on smooth sections of the hom bundle.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* [D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SectionChartData

section HomMul

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [FiniteDimensional ℝ F'] {S : Type*} [AddCommGroup S] [Module ℝ S] {S' : Type*}
  [AddCommGroup S'] [Module ℝ S'] (C : SectionChartData E F S) (D : SectionChartData E F' S')
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) {σ : Fin D.n → Fin C.n}
  (hσ : ∀ i, D.image i ≤ C.image (σ i)) {U : Fin D.n → Set E} (hU : ∀ i, UniqueDiffOn ℝ (U i))
  (hK : ∀ i, IsCompact (closure (D.image i : Set E))) (hKU : ∀ i, closure (D.image i : Set E) ⊆ U i)
  {g g' : Fin D.n → E → F →L[ℝ] F'} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) (U i))
  (hsec : ∀ s, ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = g i y (C.coord (σ i) s y))

/-- The chartwise product on tuples: the chart-`σ i` components restricted to the image of chart
`i` of `D` and multiplied there by `g i`. -/
private def homMulData : C.SobolevData μ p k →L[ℝ] D.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦
    (Wkp.contDiffOnCLMApplyL (hU i) (hK i) (hKU i) k (finBasis ℝ F) (finBasis ℝ F') (hg i)).comp
      ((ContinuousLinearMap.piMap fun _ ↦ Wkp.restrictL (hσ i) k).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p k) (σ i)))

private theorem homMulData_apply (w : C.SobolevData μ p k) (i : Fin D.n) :
    homMulData C D μ p k hσ hU hK hKU hg w i =
      Wkp.contDiffOnCLMApplyL (hU i) (hK i) (hKU i) k (finBasis ℝ F) (finBasis ℝ F') (hg i)
        fun l ↦ Wkp.restrictL (hσ i) k (w (σ i) l) :=
  (rfl)

private theorem value_homMulData_ae (w : C.SobolevData μ p k) (i : Fin D.n)
    (m : Fin (finrank ℝ F')) :
    (Wkp.value k (homMulData C D μ p k hσ hU hK hKU hg w i m) : E → ℝ)
      =ᵐ[μ.restrict (D.image i)]
        fun y ↦ (finBasis ℝ F').repr (g i y (C.chartValueL μ p k (σ i) w y)) m := by
  rw [homMulData_apply]
  filter_upwards [Wkp.value_contDiffOnCLMApplyL_ae (hU i) (hK i) (hKU i) k (finBasis ℝ F)
      (finBasis ℝ F') (hg i) (fun l ↦ Wkp.restrictL (hσ i) k (w (σ i) l)) m,
    ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae (hσ i) k (w (σ i) l),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hσ i))
      (C.chartValueL_apply_ae μ p k (σ i) w)] with y hy hl hv
  rw [hy, hv]
  simp only [hl]

private theorem chartValueL_homMulData_ae (w : C.SobolevData μ p k) (i : Fin D.n) :
    D.chartValueL μ p k i (homMulData C D μ p k hσ hU hK hKU hg w)
      =ᵐ[μ.restrict (D.image i)] fun y ↦ g i y (C.chartValueL μ p k (σ i) w y) := by
  filter_upwards [D.chartValueL_apply_ae μ p k i (homMulData C D μ p k hσ hU hK hKU hg w),
    ae_all_iff.2 (value_homMulData_ae C D μ p k hσ hU hK hKU hg w i)] with y hy hm
  rw [hy]
  simp_rw [hm]
  exact (finBasis ℝ F').sum_repr _

include hsec in
/-- **Chartwise smooth operator coefficients on the Sobolev sections.** Let the image of chart
`i` of `D` lie in the image of chart `σ i` of `C`, and let its closure be compact and contained in
a set `U i` of unique differentiability on which `g i : E → F →L[ℝ] F'` is smooth. If applying `g`
to the readings of every section of `C` gives the readings of a section of `D`, then restricting
the chart-`σ i` components to the image of chart `i` of `D` and multiplying them there by `g i`
with `TauCeti.Wkp.contDiffOnCLMApplyL` is a continuous linear map between the Sobolev sections. -/
def contDiffOnCLMApplyL : C.sobolevSections μ p k →L[ℝ] D.sobolevSections μ p k :=
  ((homMulData C D μ p k hσ hU hK hKU hg).comp (C.sobolevSections μ p k).subtypeL).codRestrict
    (D.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (C.mem_sobolevSections_iff μ p k).1 w.property
      obtain ⟨t, ht⟩ := hsec s
      refine (D.mem_sobolevSections_iff μ p k).2 ⟨t, fun i ↦ ?_⟩
      filter_upwards [chartValueL_homMulData_ae C D μ p k hσ hU hK hKU hg w i,
        ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hσ i)) (hs (σ i)),
        ae_restrict_mem (D.image i).isOpen.measurableSet] with y hy hsy hyD
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hy, hsy, ht i y hyD]

/-- Each chart-`i` component of the product is obtained by restricting the chart-`σ i`
components of `w` to the image of chart `i` and multiplying them by `g i` with
`TauCeti.Wkp.contDiffOnCLMApplyL`. -/
@[simp]
theorem contDiffOnCLMApplyL_apply (w : C.sobolevSections μ p k) (i : Fin D.n)
    (m : Fin (finrank ℝ F')) :
    (C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w : D.SobolevData μ p k) i m =
      Wkp.contDiffOnCLMApplyL (hU i) (hK i) (hKU i) k (finBasis ℝ F) (finBasis ℝ F') (hg i)
        (fun l ↦ Wkp.restrictL (hσ i) k ((w : C.SobolevData μ p k) (σ i) l)) m := by
  rw [contDiffOnCLMApplyL, ContinuousLinearMap.coe_codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, homMulData_apply]

/-- The chart-`i` components of the product are, almost everywhere on the image of chart `i` of
`D`, the components of `g i y` applied to the chart-`σ i` data of `w`. -/
theorem value_contDiffOnCLMApplyL_ae (w : C.sobolevSections μ p k) (i : Fin D.n)
    (m : Fin (finrank ℝ F')) :
    (Wkp.value k ((C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w : D.SobolevData μ p k)
      i m) : E → ℝ) =ᵐ[μ.restrict (D.image i)]
        fun y ↦ (finBasis ℝ F').repr (g i y (C.chartValueL μ p k (σ i) w y)) m :=
  value_homMulData_ae C D μ p k hσ hU hK hKU hg w i m

/-- **Characterization.** An element of the Sobolev sections of `D` is the product of `w` exactly
when each of its chart-`i` components is, almost everywhere on the image of chart `i`, the
corresponding component of `g i y` applied to the chart-`σ i` data of `w`. -/
theorem eq_contDiffOnCLMApplyL_iff {w : C.sobolevSections μ p k} {w' : D.sobolevSections μ p k} :
    w' = C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w ↔ ∀ i m,
      (Wkp.value k ((w' : D.SobolevData μ p k) i m) : E → ℝ) =ᵐ[μ.restrict (D.image i)]
        fun y ↦ (finBasis ℝ F').repr (g i y (C.chartValueL μ p k (σ i) w y)) m :=
  ⟨fun h ↦ h ▸ C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg hsec w, fun h ↦
    Subtype.ext <| funext fun i ↦ funext fun m ↦ Wkp.ext k (Lp.ext ((h i m).trans
      (C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg hsec w i m).symm))⟩

/-- The chart data in chart `i` of the product are, almost everywhere on the image of chart `i`
of `D`, the coefficient `g i y` applied to the chart-`σ i` data of `w`. -/
theorem chartValueL_contDiffOnCLMApplyL_ae (w : C.sobolevSections μ p k) (i : Fin D.n) :
    D.chartValueL μ p k i (C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w)
      =ᵐ[μ.restrict (D.image i)] fun y ↦ g i y (C.chartValueL μ p k (σ i) w y) :=
  chartValueL_homMulData_ae C D μ p k hσ hU hK hKU hg w i

/-- Coefficients that agree on the image of each chart of `D` give the same map. -/
theorem contDiffOnCLMApplyL_congr (hg' : ∀ i, ContDiffOn ℝ ∞ (g' i) (U i))
    (hsec' : ∀ s, ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = g' i y (C.coord (σ i) s y))
    (hgg' : ∀ i, ∀ y ∈ D.image i, g i y = g' i y) :
    C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec =
      C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg' hsec' := by
  ext1 w
  refine (eq_contDiffOnCLMApplyL_iff C D μ p k hσ hU hK hKU hg' hsec').2 fun i m ↦ ?_
  filter_upwards [C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg hsec w i m,
    ae_restrict_mem (D.image i).isOpen.measurableSet] with y hy hyD
  rw [hy, hgg' i y hyD]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- Applying the zero coefficient to the readings of sections gives the readings of a section. -/
theorem exists_coord_eq_zero_apply (s : S) :
    ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = (0 : F →L[ℝ] F') (C.coord (σ i) s y) :=
  ⟨0, fun i y hy ↦ by rw [D.coord_zero i hy, zero_apply]⟩

include hsec in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- If applying `g` and `g'` to the readings of sections gives the readings of sections, then so
does applying `g + g'`. -/
theorem exists_coord_eq_add_apply
    (hsec' : ∀ s, ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = g' i y (C.coord (σ i) s y))
    (s : S) :
    ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = (g i y + g' i y) (C.coord (σ i) s y) := by
  obtain ⟨t₁, ht₁⟩ := hsec s
  obtain ⟨t₂, ht₂⟩ := hsec' s
  exact ⟨t₁ + t₂, fun i y hy ↦ by
    rw [D.coord_add i t₁ t₂ y hy, ht₁ i y hy, ht₂ i y hy, add_apply]⟩

include hsec in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- If applying `g` to the readings of sections gives the readings of sections, then so does
applying `c • g`. -/
theorem exists_coord_eq_smul_apply (c : ℝ) (s : S) :
    ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = (c • g i y) (C.coord (σ i) s y) := by
  obtain ⟨t, ht⟩ := hsec s
  exact ⟨c • t, fun i y hy ↦ by
    rw [D.coord_smul i c t y hy, ht i y hy, smul_apply]⟩

/-- The zero coefficient gives the zero map. -/
@[simp]
theorem contDiffOnCLMApplyL_zero :
    C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU (g := fun _ _ ↦ 0) (fun _ ↦ contDiffOn_const)
      (C.exists_coord_eq_zero_apply D) = 0 := by
  ext1 w
  refine ((eq_contDiffOnCLMApplyL_iff C D μ p k hσ hU hK hKU _ _).2 fun i m ↦ ?_).symm
  filter_upwards [Wkp.value_zero_ae (mu := μ) (Omega := D.image i) (p := p) k] with y hy
  rw [zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply, Pi.zero_apply, hy,
    Pi.zero_apply, zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- Chartwise multiplication is additive in the coefficient. -/
theorem contDiffOnCLMApplyL_add (hg' : ∀ i, ContDiffOn ℝ ∞ (g' i) (U i))
    (hsec' : ∀ s, ∃ t, ∀ i, ∀ y ∈ D.image i, D.coord i t y = g' i y (C.coord (σ i) s y)) :
    C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU (g := fun i ↦ g i + g' i)
      (fun i ↦ (hg i).add (hg' i)) (C.exists_coord_eq_add_apply D hsec hsec') =
      C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec +
        C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg' hsec' := by
  ext1 w
  refine ((eq_contDiffOnCLMApplyL_iff C D μ p k hσ hU hK hKU _ _).2 fun i m ↦ ?_).symm
  filter_upwards [Wkp.value_add_ae k
      ((C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w : D.SobolevData μ p k) i m)
      ((C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg' hsec' w : D.SobolevData μ p k) i m),
    C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg hsec w i m,
    C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg' hsec' w i m] with y hy h₁ h₂
  rw [add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, hy,
    Pi.add_apply, h₁, h₂, Pi.add_apply, add_apply, map_add,
    Finsupp.coe_add, Pi.add_apply]

/-- Chartwise multiplication is homogeneous in the coefficient. -/
theorem contDiffOnCLMApplyL_smul (c : ℝ) :
    C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU (g := fun i ↦ c • g i)
      (fun i ↦ (hg i).const_smul c) (C.exists_coord_eq_smul_apply D hsec c) =
      c • C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec := by
  ext1 w
  refine ((eq_contDiffOnCLMApplyL_iff C D μ p k hσ hU hK hKU _ _).2 fun i m ↦ ?_).symm
  filter_upwards [Wkp.value_smul_ae k c
      ((C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec w : D.SobolevData μ p k) i m),
    C.value_contDiffOnCLMApplyL_ae D μ p k hσ hU hK hKU hg hsec w i m] with y hy h₁
  rw [smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hy,
    Pi.smul_apply, h₁, Pi.smul_apply, smul_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply]

/-- Chartwise multiplication commutes with the inclusion of the Sobolev sections of order `k + 1`
into those of order `k`. -/
theorem lowerOrderL_contDiffOnCLMApplyL (w : C.sobolevSections μ p (k + 1)) :
    D.lowerOrderL μ p k (C.contDiffOnCLMApplyL D μ p (k + 1) hσ hU hK hKU hg hsec w) =
      C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec (C.lowerOrderL μ p k w) := by
  refine Subtype.ext <| funext fun i ↦ funext fun m ↦ ?_
  rw [lowerOrderL_apply, contDiffOnCLMApplyL_apply, contDiffOnCLMApplyL_apply,
    Wkp.lowerOrder_contDiffOnCLMApplyL]
  exact congrArg (fun u ↦ Wkp.contDiffOnCLMApplyL (hU i) (hK i) (hKU i) k (finBasis ℝ F)
    (finBasis ℝ F') (hg i) u m) (funext fun l ↦ by rw [Wkp.lowerOrder_restrictL, lowerOrderL_apply])

/-- **The norm from the charts.** If, on the image of each chart `i` of `D`, multiplication by
`g i` with `TauCeti.Wkp.contDiffOnCLMApplyL` has norm at most `c`, then so has the chartwise
product between the Sobolev sections. -/
theorem norm_contDiffOnCLMApplyL_le {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ i (u : Fin (finrank ℝ F) → Wkp μ (D.image i) p k),
      ‖Wkp.contDiffOnCLMApplyL (hU i) (hK i) (hKU i) k (finBasis ℝ F) (finBasis ℝ F') (hg i) u‖ ≤
        c * ‖u‖) :
    ‖C.contDiffOnCLMApplyL D μ p k hσ hU hK hKU hg hsec‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun w ↦ ?_
  rw [← Submodule.norm_coe, ← Submodule.norm_coe]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [funext (C.contDiffOnCLMApplyL_apply D μ p k hσ hU hK hKU hg hsec w i)]
  refine (hc i _).trans (mul_le_mul_of_nonneg_left ?_ hc0)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l ↦
    (Wkp.norm_restrictL_le (hσ i) k _).trans ?_
  exact C.norm_component_le w (σ i) l

end HomMul

end SectionChartData

open FiniteBundleAtlas

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ 𝓘(ℝ, E)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)]
  {A : FiniteBundleAtlas E M F₁ V₁}
  {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet}
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
  {Φ Ψ : ∀ x, V₁ x →L[ℝ] V₂ x}

variable (A h) in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ 𝓘(ℝ, E)] [FiniteDimensional ℝ F₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] [μ.IsAddHaarMeasure] in
/-- An almost-everywhere statement on the image of chart `i` of `A.ofBaseSet h` holds on the
image of chart `i` of `A`, which is the same set. -/
private theorem ae_image_of_ae_image_ofBaseSet (i : Fin A.n) {P : E → Prop}
    (hP : ∀ᵐ y ∂μ.restrict ((A.ofBaseSet h).sectionChartData.image i), P y) :
    ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rwa [(A.ofBaseSet h).sectionChartData_image i, image_ofBaseSet] at hP

variable (A h μ p k) in
/-- **A smooth hom section acting on `W^{k,p}`.** A smooth section `Φ` of the hom bundle
`x ↦ V₁ x →L[ℝ] V₂ x` gives a continuous linear map `W^{k,p}(V₁) → W^{k,p}(V₂)`: in chart `i` the
chart reading `(A.hom h).coord i Φ` of `Φ` is applied to the components with
`TauCeti.Wkp.contDiffOnCLMApplyL`. If `w` consists of the components of a section `s`, then its
image consists of the components of `x ↦ Φ x (s x)`
(`TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord`). The construction is that of
Tau Ceti's `TauCeti.SobolevSection.contMDiffSMulL` from `TauCeti.Wkp.contDiffOnSMulL`, with an
operator coefficient in place of a scalar one. For `V₂ = V₁` and
`h = A.closure_dom_subset_baseSet`, the atlas `A.ofBaseSet h` is `A` itself. -/
def contMDiffHomMulL
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x)) :
    SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  A.sectionChartData.contDiffOnCLMApplyL (A.ofBaseSet h).sectionChartData μ p k (σ := fun i ↦ i)
    (fun i ↦ (image_ofBaseSet (A := A) (h := h) i).le)
    (fun i ↦ (((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
      ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet).uniqueDiffOn)
    (A.ofBaseSet h).isCompact_closure_image
    (fun i ↦ (closure_mono fun _ hy ↦
      (image_hom (𝕜 := ℝ) (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy)).trans
      (((A.hom (𝕜 := ℝ) h).closure_image_subset_chart_image_closure_dom i).trans
        ((A.hom (𝕜 := ℝ) h).chart_image_closure_dom_subset i)))
    (fun i ↦ contDiffOn_infty.2 fun _ ↦
      (A.hom (𝕜 := ℝ) h).contDiffOn_coord (hΦ.of_le (by exact_mod_cast le_top)) i) fun s ↦
      ⟨fun x ↦ Φ x (s x), fun i y hy ↦ by
        have hy' : y ∈ A.image i := (image_ofBaseSet (A := A) (h := h) i).le hy
        rw [(A.ofBaseSet h).sectionChartData_coord_of_mem _ hy,
          A.sectionChartData_coord_of_mem _ hy', A.coord_hom_apply h i Φ s hy']⟩

variable
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x))
    (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Ψ x))

/-- The components in chart `i` of `Φ w` are those of `w`, restricted to the image of chart `i`
in the atlas of `V₂`, multiplied by the chart reading of `Φ` using
`TauCeti.Wkp.contDiffOnCLMApplyL`. -/
@[simp]
theorem contMDiffHomMulL_apply (w : SobolevSection A μ p k) (i : Fin A.n)
    (m : Fin (finrank ℝ F₂)) :
    (contMDiffHomMulL A h μ p k hΦ w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m =
      Wkp.contDiffOnCLMApplyL
        (((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
          ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet).uniqueDiffOn
        ((A.ofBaseSet h).isCompact_closure_image i)
        ((closure_mono fun _ hy ↦
          (image_hom (𝕜 := ℝ) (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy)).trans
          (((A.hom (𝕜 := ℝ) h).closure_image_subset_chart_image_closure_dom i).trans
            ((A.hom (𝕜 := ℝ) h).chart_image_closure_dom_subset i))) k
        (finBasis ℝ F₁) (finBasis ℝ F₂)
        (contDiffOn_infty.2 fun _ ↦
          (A.hom (𝕜 := ℝ) h).contDiffOn_coord (hΦ.of_le (by exact_mod_cast le_top)) i)
        (fun l ↦ Wkp.restrictL (image_ofBaseSet (A := A) (h := h) i).le k
          ((w : A.sectionChartData.SobolevData μ p k) i l)) m :=
  A.sectionChartData.contDiffOnCLMApplyL_apply (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ w i m

/-- The components in chart `i` of `Φ w` are, almost everywhere on the image of chart `i`, the
components of the chart reading of `Φ` applied to the chart data of `w`. -/
theorem value_contMDiffHomMulL_ae (w : SobolevSection A μ p k) (i : Fin A.n)
    (m : Fin (finrank ℝ F₂)) :
    (Wkp.value k ((contMDiffHomMulL A h μ p k hΦ w :
      (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F₂).repr
        ((A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y)) m :=
  ae_image_of_ae_image_ofBaseSet A h i
    (A.sectionChartData.value_contDiffOnCLMApplyL_ae (A.ofBaseSet h).sectionChartData μ p k
      _ _ _ _ _ _ w i m)

/-- **Characterization.** An element of `W^{k,p}(V₂)` equals `Φ w` exactly when each of its
components in chart `i` is, almost everywhere on the image of chart `i`, the corresponding
component of the chart reading of `Φ` applied to the chart data of `w`. -/
theorem eq_contMDiffHomMulL_iff {w : SobolevSection A μ p k}
    {w' : SobolevSection (A.ofBaseSet h) μ p k} :
    w' = contMDiffHomMulL A h μ p k hΦ w ↔ ∀ i m,
      (Wkp.value k ((w' : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F₂).repr
          ((A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y)) m :=
  (A.sectionChartData.eq_contDiffOnCLMApplyL_iff (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _).trans <| forall_congr' fun i ↦ forall_congr' fun m ↦ by
      rw [← image_ofBaseSet (A := A) (h := h) i]
      rfl

/-- The chart data in chart `i` of `Φ w` are, almost everywhere on the image of chart `i`, the
chart reading of `Φ` applied to the chart data of `w`. -/
theorem chartValueL_contMDiffHomMulL_ae (w : SobolevSection A μ p k) (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (contMDiffHomMulL A h μ p k hΦ w)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y) :=
  ae_image_of_ae_image_ofBaseSet A h i
    (A.sectionChartData.chartValueL_contDiffOnCLMApplyL_ae (A.ofBaseSet h).sectionChartData μ p k
      _ _ _ _ _ _ w i)

/-- **Sections.** If `w` consists of the chartwise components of a section `s` of `V₁`, then
`Φ w` consists of the chartwise components of the section `x ↦ Φ x (s x)` of `V₂`. -/
theorem chartValueL_contMDiffHomMulL_ae_coord {w : SobolevSection A μ p k} {s : ∀ x, V₁ x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (contMDiffHomMulL A h μ p k hΦ w)
      =ᵐ[μ.restrict (A.image i)] (A.ofBaseSet h).coord i fun x ↦ Φ x (s x) := by
  filter_upwards [chartValueL_contMDiffHomMulL_ae hΦ w i, hs i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hsy hyi
  rw [hy, hsy, A.coord_hom_apply h i Φ s hyi]

/-- `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae` for a smooth section `Φ` of the
endomorphism bundle of `V₁`, read in `A` itself: the chart data in chart `i` of `Φ w` are, almost
everywhere on the image of chart `i`, the chart reading of `Φ` applied to the chart data of `w`. -/
theorem chartValueL_contMDiffHomMulL_ae_self [∀ x, IsTopologicalAddGroup (V₁ x)]
    [∀ x, ContinuousSMul ℝ (V₁ x)] {Φ : ∀ x, V₁ x →L[ℝ] V₁ x}
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₁)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₁) x (Φ x))
    (w : SobolevSection A μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i
        (contMDiffHomMulL A A.closure_dom_subset_baseSet μ p k hΦ w :
          (A.ofBaseSet A.closure_dom_subset_baseSet).sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet).coord i Φ y
          (A.sectionChartData.chartValueL μ p k i w y) :=
  -- `A.ofBaseSet A.closure_dom_subset_baseSet`, the atlas of the image, is `A` by the eta rule
  -- for structures; the statement cannot be rewritten into this form, since the type of the
  -- chart data depends on the atlas.
  chartValueL_contMDiffHomMulL_ae hΦ w i

/-- `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord` for a smooth section `Φ` of
the endomorphism bundle of `V₁`, read in `A` itself: if `w` consists of the chartwise components
of a section `s` of `V₁`, then `Φ w` consists of the chartwise components in `A` of the section
`x ↦ Φ x (s x)`. -/
theorem chartValueL_contMDiffHomMulL_ae_coord_self [∀ x, IsTopologicalAddGroup (V₁ x)]
    [∀ x, ContinuousSMul ℝ (V₁ x)] {Φ : ∀ x, V₁ x →L[ℝ] V₁ x}
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₁)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₁) x (Φ x))
    {w : SobolevSection A μ p k} {s : ∀ x, V₁ x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i
        (contMDiffHomMulL A A.closure_dom_subset_baseSet μ p k hΦ w :
          (A.ofBaseSet A.closure_dom_subset_baseSet).sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] A.coord i fun x ↦ Φ x (s x) := by
  filter_upwards [chartValueL_contMDiffHomMulL_ae_self hΦ w i, hs i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hsy hyi
  rw [hy, hsy, A.coord_hom_apply_self i Φ s hyi]

/-- The map depends only on the hom section, not on the proof of its smoothness. -/
theorem contMDiffHomMulL_congr (hΦΨ : Φ = Ψ) :
    contMDiffHomMulL A h μ p k hΦ = contMDiffHomMulL A h μ p k hΨ := by
  subst hΦΨ
  rfl

/-- The zero hom section gives the zero map. -/
@[simp]
theorem contMDiffHomMulL_zero
    (h0 : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((0 : ∀ x, V₁ x →L[ℝ] V₂ x) x)) :
    contMDiffHomMulL A h μ p k h0 = 0 :=
  (A.sectionChartData.contDiffOnCLMApplyL_congr (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ _ (A.sectionChartData.exists_coord_eq_zero_apply _) fun i _ hy ↦
      (A.hom (𝕜 := ℝ) h).coord_zero i
        ((image_hom (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy))).trans
    (A.sectionChartData.contDiffOnCLMApplyL_zero (A.ofBaseSet h).sectionChartData μ p k _ _ _ _)

/-- The map is additive in the hom section. -/
theorem contMDiffHomMulL_add
    (hΦΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((Φ + Ψ) x)) :
    contMDiffHomMulL A h μ p k hΦΨ =
      contMDiffHomMulL A h μ p k hΦ + contMDiffHomMulL A h μ p k hΨ := by
  refine Eq.trans ?_ (A.sectionChartData.contDiffOnCLMApplyL_add (A.ofBaseSet h).sectionChartData
    μ p k _ _ _ _ _ _ _ _)
  exact A.sectionChartData.contDiffOnCLMApplyL_congr (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ _ _ fun i _ hy ↦ (A.hom (𝕜 := ℝ) h).coord_add i Φ Ψ
      ((image_hom (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy))

/-- The map takes differences of hom sections to differences. -/
theorem contMDiffHomMulL_sub
    (hΦΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((Φ - Ψ) x)) :
    contMDiffHomMulL A h μ p k hΦΨ =
      contMDiffHomMulL A h μ p k hΦ - contMDiffHomMulL A h μ p k hΨ := by
  rw [contMDiffHomMulL_congr hΦ (hΦΨ.add_section hΨ) (sub_add_cancel Φ Ψ).symm,
    contMDiffHomMulL_add hΦΨ hΨ (hΦΨ.add_section hΨ)]
  exact (add_sub_cancel_right (contMDiffHomMulL A h μ p k hΦΨ) (contMDiffHomMulL A h μ p k hΨ)).symm

/-- The map is homogeneous in the hom section. -/
theorem contMDiffHomMulL_smul (c : ℝ)
    (hcΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((c • Φ) x)) :
    contMDiffHomMulL A h μ p k hcΦ = c • contMDiffHomMulL A h μ p k hΦ := by
  refine Eq.trans ?_ (A.sectionChartData.contDiffOnCLMApplyL_smul (A.ofBaseSet h).sectionChartData
    μ p k _ _ _ _ _ _ c)
  exact A.sectionChartData.contDiffOnCLMApplyL_congr (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ _ _ fun i _ hy ↦ (A.hom (𝕜 := ℝ) h).coord_smul i c Φ
      ((image_hom (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy))

/-- The action of a smooth hom section commutes with the inclusion `W^{k+1,p} → W^{k,p}`. -/
theorem lowerOrderL_contMDiffHomMulL (w : SobolevSection A μ p (k + 1)) :
    (A.ofBaseSet h).sectionChartData.lowerOrderL μ p k (contMDiffHomMulL A h μ p (k + 1) hΦ w) =
      contMDiffHomMulL A h μ p k hΦ (A.sectionChartData.lowerOrderL μ p k w) :=
  A.sectionChartData.lowerOrderL_contDiffOnCLMApplyL (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ w

/-- Applying a smooth hom section `Φ` to the Sobolev section of a `Cᵏ` section `s` of `V₁` gives
the Sobolev section of the `Cᵏ` section `x ↦ Φ x (s x)` of `V₂`. -/
@[simp]
theorem contMDiffHomMulL_ofContMDiffSection (s : Cₛ^k⟮𝓘(ℝ, E); F₁, V₁⟯) :
    contMDiffHomMulL A h μ p k hΦ (ofContMDiffSection A μ p k s) =
      ofContMDiffSection (A.ofBaseSet h) μ p k
        ⟨fun x ↦ Φ x (s x), (hΦ.of_le (by exact_mod_cast le_top)).clm_bundle_apply s.contMDiff⟩ :=
  eq_of_ae_eq_coord
    (fun i ↦ by
      have := chartValueL_contMDiffHomMulL_ae_coord (h := h) hΦ
        (chartValueL_ofContMDiffSection_ae A μ p k s) i
      rwa [← image_ofBaseSet (A := A) (h := h) i, ← (A.ofBaseSet h).sectionChartData_image i]
        at this)
    fun i ↦ chartValueL_ofContMDiffSection_ae (A.ofBaseSet h) μ p k _ i

variable (A h k) in
/-- **A `C^k` bound for a smooth hom section acting on `W^{k,p}`.** There is a constant `c`,
depending only on the atlas, `h` and `k`, such that for every Haar measure, every exponent
`1 ≤ p ≤ ∞` and every smooth hom section `Φ` whose chart readings have, on the image of every
chart, derivatives of order at most `k` bounded by `M ≥ 0`, the operator norm of `Φ` acting on
`W^{k,p}` is at most `c M`. -/
theorem exists_norm_contMDiffHomMulL_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
      {Φ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x)) {M : ℝ}, 0 ≤ M →
      (∀ i, ∀ j ≤ k, ∀ y ∈ A.image i, ‖iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ) y‖ ≤ M) →
      ‖contMDiffHomMulL A h μ p k hΦ‖ ≤ c * M := by
  obtain ⟨c, hc0, hc⟩ := Wkp.exists_norm_contDiffOnCLMApplyL_le E k (finBasis ℝ F₁) (finBasis ℝ F₂)
  refine ⟨c, hc0, fun {μ} _ {p} _ {Φ} hΦ {M} hM0 hM ↦
    A.sectionChartData.norm_contDiffOnCLMApplyL_le (A.ofBaseSet h).sectionChartData μ p k _ _ _ _ _
      _ (mul_nonneg hc0 hM0) fun i u ↦ hc _ _ _ _ (fun j hj y hy ↦ ?_) u⟩
  have hy' : y ∈ A.image i := (image_ofBaseSet (A := A) (h := h) i).le hy
  rw [iteratedFDerivWithin_of_isOpen j (((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
    ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet)
    ((A.hom (𝕜 := ℝ) h).image_subset_target_inter_preimage_symm i ((image_hom (h := h) i).ge hy'))]
  exact hM i j hj y hy'

variable (A h k) in
/-- **A `C^k` bound for the difference of two hom sections.** There is a constant `c`, depending
only on the atlas, `h` and `k`, such that for every Haar measure and every exponent `1 ≤ p ≤ ∞`,
two smooth hom sections whose chart readings have, on the image of every chart, derivatives of
order at most `k` that differ by at most `M ≥ 0` act on `W^{k,p}` by operators at distance at
most `c M`. -/
theorem exists_norm_contMDiffHomMulL_sub_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
      {Φ Ψ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x))
      (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Ψ x)) {M : ℝ}, 0 ≤ M →
      (∀ i, ∀ j ≤ k, ∀ y ∈ A.image i,
        ‖iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ) y -
          iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Ψ) y‖ ≤ M) →
      ‖contMDiffHomMulL A h μ p k hΦ - contMDiffHomMulL A h μ p k hΨ‖ ≤ c * M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_contMDiffHomMulL_le A h k
  refine ⟨c, hc0, fun {μ} _ {p} _ {Φ Ψ} hΦ hΨ {M} hM0 hM ↦ ?_⟩
  have hΦΨ := hΦ.sub_section hΨ
  rw [← contMDiffHomMulL_sub hΦ hΨ hΦΨ]
  refine hc hΦΨ hM0 fun i j hj y hy ↦ ?_
  have hU := ((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
    ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet
  have hyU :=
    (A.hom (𝕜 := ℝ) h).image_subset_target_inter_preimage_symm i ((image_hom (h := h) i).ge hy)
  have hcd {Θ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΘ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Θ x)) :
      ContDiffAt ℝ j ((A.hom (𝕜 := ℝ) h).coord i Θ) y :=
    ((A.hom (𝕜 := ℝ) h).contDiffOn_coord (hΘ.of_le (by exact_mod_cast le_top)) i).contDiffAt
      (hU.mem_nhds hyU)
  have hsub : (A.hom (𝕜 := ℝ) h).coord i (Φ - Ψ) =ᶠ[nhds y]
      (A.hom (𝕜 := ℝ) h).coord i Φ - (A.hom (𝕜 := ℝ) h).coord i Ψ := by
    filter_upwards [(A.image i).isOpen.mem_nhds hy] with z hz
    rw [Pi.sub_apply]
    exact (A.hom (𝕜 := ℝ) h).coord_sub i Φ Ψ ((image_hom (h := h) i).ge hz)
  rw [(hsub.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_sub_apply (hcd hΦ) (hcd hΨ)]
  exact hM i j hj y hy

/-- **Continuity in the hom section.** If the derivatives of order at most `k` of the chart
readings of smooth hom sections `Φ t` converge uniformly on the image of every chart to those of
`Φ₀`, then the action of `Φ t` on `W^{k,p}` converges in operator norm to that of `Φ₀`. -/
theorem tendsto_contMDiffHomMulL {ι : Type*} {l : Filter ι} {Φ : ι → ∀ x, V₁ x →L[ℝ] V₂ x}
    (hΦ : ∀ t, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ t x)) {Φ₀ : ∀ x, V₁ x →L[ℝ] V₂ x}
    (hΦ₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ₀ x))
    (hlim : ∀ i, ∀ j ≤ k, TendstoUniformlyOn
      (fun t ↦ iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i (Φ t)))
      (iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ₀)) l (A.image i)) :
    Filter.Tendsto (fun t ↦ contMDiffHomMulL A h μ p k (hΦ t)) l
      (nhds (contMDiffHomMulL A h μ p k hΦ₀)) := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_contMDiffHomMulL_sub_le A h k
  refine (Metric.tendsto_nhds
    (α := SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k)).2
    fun ε hε ↦ ?_
  have hδ : 0 < ε / (c + 1) := div_pos hε (by positivity)
  have hev : ∀ᶠ t in l, ∀ i, ∀ j ∈ Finset.range (k + 1), ∀ y ∈ A.image i,
      dist (iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ₀) y)
        (iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i (Φ t)) y) < ε / (c + 1) :=
    Filter.eventually_all.2 fun i ↦ (Filter.eventually_all_finset _).2 fun j hj ↦
      Metric.tendstoUniformlyOn_iff.1
        (hlim i j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) _ hδ
  filter_upwards [hev] with t ht
  refine (dist_eq_norm (contMDiffHomMulL A h μ p k (hΦ t))
    (contMDiffHomMulL A h μ p k hΦ₀)).trans_lt
    ((hc (hΦ t) hΦ₀ hδ.le fun i j hj y hy ↦ ?_).trans_lt ?_)
  · rw [← dist_eq_norm, dist_comm]
    exact (ht i j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) y hy).le
  · rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith

/-- **Continuity in the hom section for the frame topology.** If smooth sections `s t` of the hom
bundle tend to `s₀` along `l` in the frame topology of a frame system covering `M`, then the action
of `s t` on `W^{k,p}` converges in operator norm to that of `s₀`. -/
theorem tendsto_contMDiffHomMulL_of_tendsto {κ : Type*}
    {e : κ → Trivialization (F₁ →L[ℝ] F₂) (π (F₁ →L[ℝ] F₂) fun x ↦ V₁ x →L[ℝ] V₂ x)}
    [∀ i, MemTrivializationAtlas (e i)] {U : κ → TopologicalSpace.Opens M}
    {hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet} (hcover : ∀ x, ∃ i, x ∈ U i) {ι : Type*}
    {l : Filter ι} {s : ι → Cₛ^∞⟮𝓘(ℝ, E); F₁ →L[ℝ] F₂, fun x ↦ V₁ x →L[ℝ] V₂ x⟯}
    {s₀ : Cₛ^∞⟮𝓘(ℝ, E); F₁ →L[ℝ] F₂, fun x ↦ V₁ x →L[ℝ] V₂ x⟯}
    (hs : letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, E)) (n := ∞) e U hU
      Filter.Tendsto s l (nhds s₀)) :
    Filter.Tendsto (fun t ↦ contMDiffHomMulL A h μ p k (s t).contMDiff) l
      (nhds (contMDiffHomMulL A h μ p k s₀.contMDiff)) :=
  tendsto_contMDiffHomMulL (fun t ↦ (s t).contMDiff) s₀.contMDiff fun i _ _ ↦
    (tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto hcover hs (A.hom (𝕜 := ℝ) h) i
      (by exact_mod_cast le_top)).mono (image_hom (h := h) i).ge

end SobolevSection

end TauCeti

end
