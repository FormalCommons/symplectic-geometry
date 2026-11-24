/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
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
main branch). Tau Ceti's `TauCeti.SobolevSection.homMulL` is a different operator: its
coefficient is a rough Sobolev section, and it lowers the order.

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
* `TauCeti.SectionChartData.contDiffOnCLMApplyL_zero`,
  `TauCeti.SectionChartData.contDiffOnCLMApplyL_add`,
  `TauCeti.SectionChartData.contDiffOnCLMApplyL_smul`,
  `TauCeti.SectionChartData.lowerOrderL_contDiffOnCLMApplyL`: linearity in the coefficient and
  compatibility with lowering the order.
* `TauCeti.SobolevSection.value_contMDiffHomMulL_ae`,
  `TauCeti.SobolevSection.eq_contMDiffHomMulL_iff`,
  `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae`: in chart `i`, the chart data of
  `Φ w` are `(A.hom h).coord i Φ y` applied to those of `w`.
* `TauCeti.SobolevSection.chartValueL_contMDiffHomMulL_ae_coord`: if `w` consists of the
  components of a section `s`, then `Φ w` consists of those of `x ↦ Φ x (s x)`.
* `TauCeti.SobolevSection.contMDiffHomMulL_zero`, `TauCeti.SobolevSection.contMDiffHomMulL_add`,
  `TauCeti.SobolevSection.contMDiffHomMulL_smul`, `TauCeti.SobolevSection.contMDiffHomMulL_congr`,
  `TauCeti.SobolevSection.lowerOrderL_contMDiffHomMulL`: linearity in `Φ` and compatibility with
  the inclusion `W^{k+1,p} → W^{k,p}`.

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

variable (A) in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ F₁] [ContMDiffVectorBundle ∞ F₁ V₁ 𝓘(ℝ, E)]
  [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, E)] in
/-- The closure of the image of chart `i` lies in the open set of chart-`i` coordinates over the
base set of the hom bundle chart, where the chart reading of a smooth hom section is smooth
(`TauCeti.FiniteBundleAtlas.contDiffOn_coord_of_contMDiff`). -/
theorem _root_.TauCeti.FiniteBundleAtlas.closure_image_ofBaseSet_subset_hom (i : Fin A.n) :
    closure ((A.ofBaseSet h).image i : Set E) ⊆
      ((A.hom (𝕜 := ℝ) h).chart i).target ∩
        ((A.hom (𝕜 := ℝ) h).chart i).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv i).baseSet := by
  rw [image_ofBaseSet, ← image_hom (𝕜 := ℝ) (h := h)]
  exact ((A.hom (𝕜 := ℝ) h).closure_image_subset_chart_image_closure_dom i).trans
    ((A.hom (𝕜 := ℝ) h).chart_image_closure_dom_subset i)

variable (A) in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F₁]
  [FiniteDimensional ℝ F₂] in
/-- **The chart readings of a smooth hom section are smooth** on the open set of points of the
chart target over the base set of the hom bundle chart. -/
theorem _root_.TauCeti.FiniteBundleAtlas.contDiffOn_coord_hom
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x)) (i : Fin A.n) :
    ContDiffOn ℝ ∞ ((A.hom (𝕜 := ℝ) h).coord i Φ)
      (((A.hom (𝕜 := ℝ) h).chart i).target ∩
        ((A.hom (𝕜 := ℝ) h).chart i).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv i).baseSet) :=
  (contDiffOn_trivialization_comp_chart_symm_of_contMDiff hΦ
    (IsManifold.chart_mem_maximalAtlas _) ((A.hom (𝕜 := ℝ) h).triv i)).congr
      fun y _ ↦ (A.hom (𝕜 := ℝ) h).coord_def i Φ y

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
  rwa [← image_ofBaseSet (A := A) (h := h) i]

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
    (A.ofBaseSet h).isCompact_closure_image A.closure_image_ofBaseSet_subset_hom
    (A.contDiffOn_coord_hom hΦ) fun s ↦
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
        ((A.ofBaseSet h).isCompact_closure_image i) (A.closure_image_ofBaseSet_subset_hom i) k
        (finBasis ℝ F₁) (finBasis ℝ F₂) (A.contDiffOn_coord_hom hΦ i)
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
    contMDiffHomMulL A h μ p k h0 = 0 := by
  ext1 w
  refine ((eq_contMDiffHomMulL_iff h0).2 fun i m ↦ ?_).symm
  filter_upwards [ae_image_of_ae_image_ofBaseSet A h i
      (Wkp.value_zero_ae (mu := μ) (Omega := (A.ofBaseSet h).sectionChartData.image i) (p := p) k),
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hyi
  have hc : (A.hom (𝕜 := ℝ) h).coord i (0 : ∀ x, V₁ x →L[ℝ] V₂ x) y = 0 :=
    (A.hom (𝕜 := ℝ) h).coord_zero i ((image_hom (𝕜 := ℝ) (h := h) i).ge hyi)
  rw [zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply, Pi.zero_apply, hy, Pi.zero_apply, hc,
    zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- The map is additive in the hom section. -/
theorem contMDiffHomMulL_add
    (hΦΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((Φ + Ψ) x)) :
    contMDiffHomMulL A h μ p k hΦΨ =
      contMDiffHomMulL A h μ p k hΦ + contMDiffHomMulL A h μ p k hΨ := by
  ext1 w
  refine ((eq_contMDiffHomMulL_iff hΦΨ).2 fun i m ↦ ?_).symm
  filter_upwards [ae_image_of_ae_image_ofBaseSet A h i (Wkp.value_add_ae k
      ((contMDiffHomMulL A h μ p k hΦ w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m)
      ((contMDiffHomMulL A h μ p k hΨ w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m)),
    value_contMDiffHomMulL_ae hΦ w i m, value_contMDiffHomMulL_ae hΨ w i m,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy h₁ h₂ hyi
  have hc : (A.hom (𝕜 := ℝ) h).coord i (Φ + Ψ) y =
      (A.hom (𝕜 := ℝ) h).coord i Φ y + (A.hom (𝕜 := ℝ) h).coord i Ψ y :=
    (A.hom (𝕜 := ℝ) h).coord_add i Φ Ψ ((image_hom (𝕜 := ℝ) (h := h) i).ge hyi)
  rw [add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, hy, Pi.add_apply, h₁, h₂, hc,
    add_apply, map_add, Finsupp.coe_add, Pi.add_apply]

/-- The map is homogeneous in the hom section. -/
theorem contMDiffHomMulL_smul (c : ℝ)
    (hcΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((c • Φ) x)) :
    contMDiffHomMulL A h μ p k hcΦ = c • contMDiffHomMulL A h μ p k hΦ := by
  ext1 w
  refine ((eq_contMDiffHomMulL_iff hcΦ).2 fun i m ↦ ?_).symm
  filter_upwards [ae_image_of_ae_image_ofBaseSet A h i (Wkp.value_smul_ae k c
      ((contMDiffHomMulL A h μ p k hΦ w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m)),
    value_contMDiffHomMulL_ae hΦ w i m,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy h₁ hyi
  have hc : (A.hom (𝕜 := ℝ) h).coord i (c • Φ) y = c • (A.hom (𝕜 := ℝ) h).coord i Φ y :=
    (A.hom (𝕜 := ℝ) h).coord_smul i c Φ ((image_hom (𝕜 := ℝ) (h := h) i).ge hyi)
  rw [smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hy, Pi.smul_apply, h₁, hc,
    smul_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply]

/-- The action of a smooth hom section commutes with the inclusion `W^{k+1,p} → W^{k,p}`. -/
theorem lowerOrderL_contMDiffHomMulL (w : SobolevSection A μ p (k + 1)) :
    (A.ofBaseSet h).sectionChartData.lowerOrderL μ p k (contMDiffHomMulL A h μ p (k + 1) hΦ w) =
      contMDiffHomMulL A h μ p k hΦ (A.sectionChartData.lowerOrderL μ p k w) :=
  A.sectionChartData.lowerOrderL_contDiffOnCLMApplyL (A.ofBaseSet h).sectionChartData μ p k
    _ _ _ _ _ _ w

end SobolevSection

end TauCeti

end
