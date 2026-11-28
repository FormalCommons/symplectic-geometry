/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BundleMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
import SymplecticGeometry.Analysis.Sobolev.Wkp.SmoothMultiplicationBound
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import SymplecticGeometry.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.FrameTopology

/-!
# Bounds and continuity for a smooth hom section acting on Sobolev sections

Let `M` be a smooth boundaryless manifold whose model `E` is a finite-dimensional inner product
space over `ℝ`, and let `V₁`, `V₂` be smooth real vector bundles over `M` with
finite-dimensional model fibres `F₁`, `F₂`. Let `A` be a finite bundle atlas of `V₁` whose chart
domains also serve as an atlas `A.ofBaseSet h` of `V₂`. A smooth section `Φ` of the hom bundle
`x ↦ V₁ x →L[ℝ] V₂ x` acts on the Sobolev spaces of sections by Tau Ceti's continuous linear map
`TauCeti.SobolevSection.bundleMapL : W^{k,p}(V₁) → W^{k,p}(V₂)`, which sends the class of a
section `s` to that of `x ↦ Φ x (s x)` (`TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`).
This file adds what Tau Ceti's file does not say: the components of `Φ w` in each chart, as the
chart reading `(A.hom h).coord i Φ` of `Φ` applied to those of `w`; linearity in `Φ`;
compatibility with lowering the order; and bounds on the operator norm and continuity in `Φ`.

The operator norm of the action is at most a constant times a bound `M` on the derivatives of
order at most `k` of the chart readings of `Φ` on the chart images
(`TauCeti.SobolevSection.exists_norm_bundleMapL_le`). In each chart the components of `Φ w`
are the product of those of `w` by the chart reading of `Φ` with `TauCeti.Wkp.contDiffOnCLMApplyL`
(`TauCeti.SobolevSection.bundleMapL_apply`), so the local estimate
`TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le` of
`SymplecticGeometry.Analysis.Sobolev.Wkp.SmoothMultiplicationBound` bounds each of them, and the
norm of the Sobolev sections is the largest norm of their components. With the linearity in `Φ`,
the action is then continuous in `Φ` for the `C^k` convergence of the chart readings on the
chart images (`TauCeti.SobolevSection.tendsto_bundleMapL`). In particular it is continuous in `Φ`
for the frame topology `ContMDiffSection.frameTopology` of a covering frame system on smooth
sections of the hom bundle (`TauCeti.SobolevSection.tendsto_bundleMapL_of_tendsto`), whose
convergence gives that of the chart readings by
`TauCeti.FiniteBundleAtlas.tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto`.

Everything is proved from Tau Ceti's description of `bundleMapL` through a section
representative (`TauCeti.SobolevSection.exists_section_ae_eq_coord`,
`TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`): two elements with the same section
are equal (`TauCeti.SobolevSection.eq_of_ae_eq_coord`), and the reading of `Φ s` in chart `i`
is the chart reading of `Φ` applied to that of `s`
(`TauCeti.FiniteBundleAtlas.coord_hom_apply`). Tau Ceti's
`TauCeti.SobolevSection.homMulL` is a different operator: its coefficient is a rough Sobolev
section, and it lowers the order.

## Main results

* `TauCeti.SobolevSection.value_bundleMapL_ae`,
  `TauCeti.SobolevSection.eq_bundleMapL_iff`,
  `TauCeti.SobolevSection.chartValueL_bundleMapL_ae`: in chart `i`, the chart data of
  `Φ w` are `(A.hom h).coord i Φ y` applied to those of `w`.
* `TauCeti.SobolevSection.bundleMapL_apply`: the components of `Φ w` in chart `i` as a
  product with `TauCeti.Wkp.contDiffOnCLMApplyL`.
* `TauCeti.SobolevSection.chartValueL_bundleMapL_ae_self`: the same for `V₂ = V₁` and
  `h = A.closure_dom_subset_baseSet`, with the chart data of `Φ w` read in `A` itself.
* `TauCeti.SobolevSection.bundleMapL_zero`, `TauCeti.SobolevSection.bundleMapL_add`,
  `TauCeti.SobolevSection.bundleMapL_sub`, `TauCeti.SobolevSection.bundleMapL_smul`,
  `TauCeti.SobolevSection.bundleMapL_congr`,
  `TauCeti.SobolevSection.lowerOrderL_bundleMapL`: linearity in `Φ` and compatibility with
  the inclusion `W^{k+1,p} → W^{k,p}`.
* `TauCeti.SobolevSection.exists_norm_bundleMapL_le`,
  `TauCeti.SobolevSection.exists_norm_bundleMapL_sub_le`: the operator norm, and the distance
  between the actions of two hom sections, are bounded by a constant times the `C^k` size of the
  chart readings on the chart images.
* `TauCeti.SobolevSection.tendsto_bundleMapL`: continuity in the hom section.
* `TauCeti.SobolevSection.tendsto_bundleMapL_of_tendsto`: continuity in the hom section for
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

variable
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x))
    (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Ψ x))

/-- The chart data in chart `i` of `Φ w` are, almost everywhere on the image of chart `i`, the
chart reading of `Φ` applied to the chart data of `w`. -/
theorem chartValueL_bundleMapL_ae (w : SobolevSection A μ p k) (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (bundleMapL A h hΦ μ p k w)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y) := by
  obtain ⟨s, hs⟩ := exists_section_ae_eq_coord _ _ _ _ w
  filter_upwards [(A.ae_image_ofBaseSet_iff μ h i).1
      (chartValueL_bundleMapL_ae_coord (h := h) (hΦ := hΦ) hs i), hs i,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy hsy hyi
  rw [hy, hsy, A.coord_hom_apply h i Φ s hyi]

/-- The components in chart `i` of `Φ w` are, almost everywhere on the image of chart `i`, the
components of the chart reading of `Φ` applied to the chart data of `w`. -/
theorem value_bundleMapL_ae (w : SobolevSection A μ p k) (i : Fin A.n)
    (m : Fin (finrank ℝ F₂)) :
    (Wkp.value k ((bundleMapL A h hΦ μ p k w :
      (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F₂).repr
        ((A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y)) m := by
  filter_upwards [(A.ae_image_ofBaseSet_iff μ h i).1
      ((A.ofBaseSet h).sectionChartData.chartValueL_apply_ae μ p k i
        (bundleMapL A h hΦ μ p k w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k)),
    chartValueL_bundleMapL_ae hΦ w i] with y h₁ h₂
  rw [← h₂, h₁, (finBasis ℝ F₂).repr_sum_self]

/-- **Characterization.** An element of `W^{k,p}(V₂)` equals `Φ w` exactly when each of its
components in chart `i` is, almost everywhere on the image of chart `i`, the corresponding
component of the chart reading of `Φ` applied to the chart data of `w`. -/
theorem eq_bundleMapL_iff {w : SobolevSection A μ p k}
    {w' : SobolevSection (A.ofBaseSet h) μ p k} :
    w' = bundleMapL A h hΦ μ p k w ↔ ∀ i m,
      (Wkp.value k ((w' : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m) : E → ℝ)
        =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F₂).repr
          ((A.hom (𝕜 := ℝ) h).coord i Φ y (A.sectionChartData.chartValueL μ p k i w y)) m :=
  ⟨fun hw' ↦ hw' ▸ value_bundleMapL_ae hΦ w, fun hw' ↦
    (A.ofBaseSet h).sectionChartData.sobolevSections_ext μ p k fun i m ↦ Lp.ext <|
      (A.ae_image_ofBaseSet_iff μ h i).2 ((hw' i m).trans (value_bundleMapL_ae hΦ w i m).symm)⟩

/-- The components in chart `i` of `Φ w` are those of `w`, restricted to the image of chart `i`
in the atlas of `V₂`, multiplied by the chart reading of `Φ` using
`TauCeti.Wkp.contDiffOnCLMApplyL`. -/
@[simp]
theorem bundleMapL_apply (w : SobolevSection A μ p k) (i : Fin A.n)
    (m : Fin (finrank ℝ F₂)) :
    (bundleMapL A h hΦ μ p k w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i m =
      Wkp.contDiffOnCLMApplyL
        (((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
          ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet).uniqueDiffOn
        ((A.ofBaseSet h).isCompact_closure_image i)
        ((closure_mono fun _ hy ↦
          (image_hom (𝕜 := ℝ) (h := h) i).ge ((image_ofBaseSet (A := A) (h := h) i).le hy)).trans
          ((A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet i)) k
        (finBasis ℝ F₁) (finBasis ℝ F₂)
        (contDiffOn_infty.2 fun _ ↦
          (A.hom (𝕜 := ℝ) h).contDiffOn_coord (hΦ.of_le (by exact_mod_cast le_top)) i)
        (fun l ↦ Wkp.restrictL (image_ofBaseSet (A := A) (h := h) i).le k
          ((w : A.sectionChartData.SobolevData μ p k) i l)) m := by
  refine Wkp.ext k (Lp.ext ((A.ae_image_ofBaseSet_iff μ h i).2
    ((value_bundleMapL_ae hΦ w i m).trans (Filter.EventuallyEq.symm ?_))))
  refine Filter.EventuallyEq.trans ((A.ae_image_ofBaseSet_iff μ h i).1
    (Wkp.value_contDiffOnCLMApplyL_ae (mu := μ) (p := p) _ _ _ k (finBasis ℝ F₁) (finBasis ℝ F₂)
      _ _ m)) ?_
  filter_upwards [(A.ae_image_ofBaseSet_iff μ h i).1 (ae_all_iff.2 fun l ↦
      Wkp.value_restrictL_ae (image_ofBaseSet (A := A) (h := h) i).le k
        ((w : A.sectionChartData.SobolevData μ p k) i l)),
    A.sectionChartData.chartValueL_apply_ae μ p k i w] with y h₁ h₂
  rw [h₂]
  exact congrArg (fun v ↦ (finBasis ℝ F₂).repr ((A.hom (𝕜 := ℝ) h).coord i Φ y v) m)
    (Finset.sum_congr rfl fun l _ ↦ congrArg (· • finBasis ℝ F₁ l) (h₁ l))

/-- `TauCeti.SobolevSection.chartValueL_bundleMapL_ae` for a smooth section `Φ` of the
endomorphism bundle of `V₁`, read in `A` itself: the chart data in chart `i` of `Φ w` are, almost
everywhere on the image of chart `i`, the chart reading of `Φ` applied to the chart data of `w`. -/
theorem chartValueL_bundleMapL_ae_self [∀ x, IsTopologicalAddGroup (V₁ x)]
    [∀ x, ContinuousSMul ℝ (V₁ x)] {Φ : ∀ x, V₁ x →L[ℝ] V₁ x}
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₁)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₁) x (Φ x))
    (w : SobolevSection A μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i
        (bundleMapL A A.closure_dom_subset_baseSet hΦ μ p k w :
          (A.ofBaseSet A.closure_dom_subset_baseSet).sectionChartData.SobolevData μ p k)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.hom (𝕜 := ℝ) A.closure_dom_subset_baseSet).coord i Φ y
          (A.sectionChartData.chartValueL μ p k i w y) :=
  -- `A.ofBaseSet A.closure_dom_subset_baseSet`, the atlas of the image, is `A` by the eta rule
  -- for structures; the statement cannot be rewritten into this form, since the type of the
  -- chart data depends on the atlas.
  chartValueL_bundleMapL_ae hΦ w i

/-- The map depends only on the hom section, not on the proof of its smoothness. -/
theorem bundleMapL_congr (hΦΨ : Φ = Ψ) :
    bundleMapL A h hΦ μ p k = bundleMapL A h hΨ μ p k := by
  subst hΦΨ
  rfl

/-- The map is additive in the hom section. -/
theorem bundleMapL_add
    (hΦΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((Φ + Ψ) x)) :
    bundleMapL A h hΦΨ μ p k = bundleMapL A h hΦ μ p k + bundleMapL A h hΨ μ p k := by
  ext1 w
  obtain ⟨s, hs⟩ := exists_section_ae_eq_coord _ _ _ _ w
  have hsec : (fun x ↦ (Φ + Ψ) x (s x)) = (fun x ↦ Φ x (s x)) + fun x ↦ Ψ x (s x) :=
    funext fun x ↦ by simp
  refine eq_of_ae_eq_coord (fun i ↦ chartValueL_bundleMapL_ae_coord hs i) fun i ↦ ?_
  rw [hsec, add_apply]
  exact chartValueL_add_ae_coord (chartValueL_bundleMapL_ae_coord hs i)
    (chartValueL_bundleMapL_ae_coord hs i)

/-- The map takes differences of hom sections to differences. -/
theorem bundleMapL_sub
    (hΦΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((Φ - Ψ) x)) :
    bundleMapL A h hΦΨ μ p k = bundleMapL A h hΦ μ p k - bundleMapL A h hΨ μ p k := by
  rw [bundleMapL_congr hΦ (hΦΨ.add_section hΨ) (sub_add_cancel Φ Ψ).symm,
    bundleMapL_add hΦΨ hΨ (hΦΨ.add_section hΨ)]
  exact (add_sub_cancel_right (bundleMapL A h hΦΨ μ p k) (bundleMapL A h hΨ μ p k)).symm

/-- The map is homogeneous in the hom section. -/
theorem bundleMapL_smul (c : ℝ)
    (hcΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((c • Φ) x)) :
    bundleMapL A h hcΦ μ p k = c • bundleMapL A h hΦ μ p k := by
  ext1 w
  obtain ⟨s, hs⟩ := exists_section_ae_eq_coord _ _ _ _ w
  have hsec : (fun x ↦ (c • Φ) x (s x)) = c • fun x ↦ Φ x (s x) := funext fun x ↦ by simp
  refine eq_of_ae_eq_coord (fun i ↦ chartValueL_bundleMapL_ae_coord hs i) fun i ↦ ?_
  rw [hsec, smul_apply]
  exact chartValueL_smul_ae_coord c (chartValueL_bundleMapL_ae_coord hs i)

/-- The zero hom section gives the zero map. -/
@[simp]
theorem bundleMapL_zero
    (h0 : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x ((0 : ∀ x, V₁ x →L[ℝ] V₂ x) x)) :
    bundleMapL A h h0 μ p k = 0 := by
  have hc : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞ fun x ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂) x (((0 : ℝ) • (0 : ∀ x, V₁ x →L[ℝ] V₂ x)) x) := by
    rw [zero_smul]
    exact h0
  rw [bundleMapL_congr h0 hc (zero_smul ℝ (0 : ∀ x, V₁ x →L[ℝ] V₂ x)).symm,
    bundleMapL_smul h0 0 hc]
  ext1 w
  rw [smul_apply, zero_apply]
  exact zero_smul ℝ (bundleMapL A h h0 μ p k w)

/-- The action of a smooth hom section commutes with the inclusion `W^{k+1,p} → W^{k,p}`. -/
theorem lowerOrderL_bundleMapL (w : SobolevSection A μ p (k + 1)) :
    (A.ofBaseSet h).sectionChartData.lowerOrderL μ p k (bundleMapL A h hΦ μ p (k + 1) w) =
      bundleMapL A h hΦ μ p k (A.sectionChartData.lowerOrderL μ p k w) := by
  obtain ⟨s, hs⟩ := exists_section_ae_eq_coord _ _ _ _ w
  have hs' (i : Fin A.n) : A.sectionChartData.chartValueL μ p k i
      (A.sectionChartData.lowerOrderL μ p k w) =ᵐ[μ.restrict (A.image i)] A.coord i s := by
    exact A.sectionChartData.chartValueL_coe_lowerOrderL μ p k w i ▸ hs i
  refine eq_of_ae_eq_coord (s := fun x ↦ Φ x (s x)) (fun i ↦ ?_)
    (chartValueL_bundleMapL_ae_coord hs')
  exact (A.ofBaseSet h).sectionChartData.chartValueL_coe_lowerOrderL μ p k
    (bundleMapL A h hΦ μ p (k + 1) w) i ▸ chartValueL_bundleMapL_ae_coord hs i

variable (A h k) in
/-- **A `C^k` bound for a smooth hom section acting on `W^{k,p}`.** There is a constant `c`,
depending only on the atlas, `h` and `k`, such that for every Haar measure, every exponent
`1 ≤ p ≤ ∞` and every smooth hom section `Φ` whose chart readings have, on the image of every
chart, derivatives of order at most `k` bounded by `M ≥ 0`, the operator norm of `Φ` acting on
`W^{k,p}` is at most `c M`. -/
theorem exists_norm_bundleMapL_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
      {Φ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x)) {M : ℝ}, 0 ≤ M →
      (∀ i, ∀ j ≤ k, ∀ y ∈ A.image i, ‖iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ) y‖ ≤ M) →
      ‖bundleMapL A h hΦ μ p k‖ ≤ c * M := by
  obtain ⟨c, hc0, hc⟩ := Wkp.exists_norm_contDiffOnCLMApplyL_le E k (finBasis ℝ F₁) (finBasis ℝ F₂)
  refine ⟨c, hc0, fun {μ} _ {p} _ {Φ} hΦ {M} hM0 hM ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc0 hM0) fun w ↦ ?_
  rw [← Submodule.norm_coe, ← Submodule.norm_coe]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
  rw [funext (bundleMapL_apply hΦ w i)]
  refine (hc _ _ _ _ (fun j hj y hy ↦ ?_) _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  swap
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l ↦
      (Wkp.norm_restrictL_le (image_ofBaseSet (A := A) (h := h) i).le k _).trans ?_
    exact A.sectionChartData.norm_component_le w i l
  have hy' : y ∈ A.image i := (image_ofBaseSet (A := A) (h := h) i).le hy
  rw [iteratedFDerivWithin_of_isOpen j (((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm
    ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet)
    ((A.hom (𝕜 := ℝ) h).image_subset_target_inter_preimage_baseSet i
      ((image_hom (h := h) i).ge hy'))]
  exact hM i j hj y hy'

variable (A h k) in
/-- **A `C^k` bound for the difference of two hom sections.** There is a constant `c`, depending
only on the atlas, `h` and `k`, such that for every Haar measure and every exponent `1 ≤ p ≤ ∞`,
two smooth hom sections whose chart readings have, on the image of every chart, derivatives of
order at most `k` that differ by at most `M ≥ 0` act on `W^{k,p}` by operators at distance at
most `c M`. -/
theorem exists_norm_bundleMapL_sub_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
      {Φ Ψ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ x))
      (hΨ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Ψ x)) {M : ℝ}, 0 ≤ M →
      (∀ i, ∀ j ≤ k, ∀ y ∈ A.image i,
        ‖iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ) y -
          iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Ψ) y‖ ≤ M) →
      ‖bundleMapL A h hΦ μ p k - bundleMapL A h hΨ μ p k‖ ≤ c * M := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_bundleMapL_le A h k
  refine ⟨c, hc0, fun {μ} _ {p} _ {Φ Ψ} hΦ hΨ {M} hM0 hM ↦ ?_⟩
  have hΦΨ := hΦ.sub_section hΨ
  rw [← bundleMapL_sub hΦ hΨ hΦΨ]
  refine hc hΦΨ hM0 fun i j hj y hy ↦ ?_
  have hcd {Θ : ∀ x, V₁ x →L[ℝ] V₂ x}
      (hΘ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
        fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Θ x)) :
      ContDiffOn ℝ j ((A.hom (𝕜 := ℝ) h).coord i Θ) ((A.hom (𝕜 := ℝ) h).image i) :=
    (A.hom (𝕜 := ℝ) h).contDiffOn_coord_image (hΘ.of_le (by exact_mod_cast le_top)) i
  rw [(A.hom (𝕜 := ℝ) h).iteratedFDeriv_coord_sub i (hcd hΦ) (hcd hΨ)
    ((image_hom (h := h) i).ge hy)]
  exact hM i j hj y hy

/-- **Continuity in the hom section.** If the derivatives of order at most `k` of the chart
readings of smooth hom sections `Φ t` converge uniformly on the image of every chart to those of
`Φ₀`, then the action of `Φ t` on `W^{k,p}` converges in operator norm to that of `Φ₀`. -/
theorem tendsto_bundleMapL {ι : Type*} {l : Filter ι} {Φ : ι → ∀ x, V₁ x →L[ℝ] V₂ x}
    (hΦ : ∀ t, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ t x)) {Φ₀ : ∀ x, V₁ x →L[ℝ] V₂ x}
    (hΦ₀ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂) x (Φ₀ x))
    (hlim : ∀ i, ∀ j ≤ k, TendstoUniformlyOn
      (fun t ↦ iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i (Φ t)))
      (iteratedFDeriv ℝ j ((A.hom (𝕜 := ℝ) h).coord i Φ₀)) l (A.image i)) :
    Filter.Tendsto (fun t ↦ bundleMapL A h (hΦ t) μ p k) l
      (nhds (bundleMapL A h hΦ₀ μ p k)) := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_bundleMapL_sub_le A h k
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
  refine (dist_eq_norm (bundleMapL A h (hΦ t) μ p k)
    (bundleMapL A h hΦ₀ μ p k)).trans_lt
    ((hc (hΦ t) hΦ₀ hδ.le fun i j hj y hy ↦ ?_).trans_lt ?_)
  · rw [← dist_eq_norm, dist_comm]
    exact (ht i j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) y hy).le
  · rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith

/-- **Continuity in the hom section for the frame topology.** If smooth sections `s t` of the hom
bundle tend to `s₀` along `l` in the frame topology of a frame system covering `M`, then the action
of `s t` on `W^{k,p}` converges in operator norm to that of `s₀`. -/
theorem tendsto_bundleMapL_of_tendsto {κ : Type*}
    {e : κ → Trivialization (F₁ →L[ℝ] F₂) (π (F₁ →L[ℝ] F₂) fun x ↦ V₁ x →L[ℝ] V₂ x)}
    [∀ i, MemTrivializationAtlas (e i)] {U : κ → TopologicalSpace.Opens M}
    {hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet} (hcover : ∀ x, ∃ i, x ∈ U i) {ι : Type*}
    {l : Filter ι} {s : ι → Cₛ^∞⟮𝓘(ℝ, E); F₁ →L[ℝ] F₂, fun x ↦ V₁ x →L[ℝ] V₂ x⟯}
    {s₀ : Cₛ^∞⟮𝓘(ℝ, E); F₁ →L[ℝ] F₂, fun x ↦ V₁ x →L[ℝ] V₂ x⟯}
    (hs : letI := ContMDiffSection.frameTopology (I := 𝓘(ℝ, E)) (n := ∞) e U hU
      Filter.Tendsto s l (nhds s₀)) :
    Filter.Tendsto (fun t ↦ bundleMapL A h (s t).contMDiff μ p k) l
      (nhds (bundleMapL A h s₀.contMDiff μ p k)) :=
  tendsto_bundleMapL (fun t ↦ (s t).contMDiff) s₀.contMDiff fun i _ _ ↦
    (tendstoUniformlyOn_iteratedFDeriv_coord_of_tendsto hcover hs (A.hom (𝕜 := ℝ) h) i
      (by exact_mod_cast le_top)).mono (image_hom (h := h) i).ge

end SobolevSection

end TauCeti

end
