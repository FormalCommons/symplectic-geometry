/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import SymplecticGeometry.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The formal transpose of a second-order operator

Let `U` be an open subset of a finite-dimensional real space `E`, `v : ι → E` a finite family of
vectors, and `P` the second-order operator on maps `a : E → F`
`P a = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} a + ∑ᵢ Bᵢ ∂_{v_i} a + C a`,
with scalar coefficients `Aᵢⱼ` and coefficients `Bᵢ`, `C` with values in `F →L[ℝ] F`. Its formal
transpose for an additive Haar measure `μ`, acting on maps `w : E → F →L[ℝ] ℝ` with the pairing
`⟨w, a⟩ = ∫ w a dμ`, is the operator
`P' w = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} w + ∑ᵢ (∂_{v_i} w) ∘ B'ᵢ + w ∘ C'`, with the same second-order
coefficients `Aᵢⱼ` and
`B'ᵢ = (∑ⱼ ∂_{v_j} Aᵢⱼ + ∑ⱼ ∂_{v_j} Aⱼᵢ) • id - Bᵢ`,
`C' = (∑ᵢⱼ ∂_{v_i} ∂_{v_j} Aᵢⱼ) • id - ∑ᵢ ∂_{v_i} Bᵢ + C`:
`∫ w (P a) dμ = ∫ (P' w) a dμ` whenever `w` is `C²` on `U` and `a` is `C²` with compact support in
`U`. The second-order coefficients carry over because they are scalars.

The proof integrates by parts once for each first-order term and twice for each second-order
term, with Tau Ceti's `TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport`,
and expands the derivatives of the products `Aᵢⱼ w` by Tau Ceti's Leibniz rule
`TauCeti.fderiv_fderiv_fun_smul_apply`.

## Main results

* `SymplecticGeometry.integral_apply_apply_fderiv_eq_integral_neg_apply` and
  `SymplecticGeometry.integral_apply_smul_fderiv_fderiv_eq_integral_fderiv_fderiv_apply`: the
  transpose of a single first-order and second-order term.
* `SymplecticGeometry.integral_apply_eq_integral_transpose_apply`: the formal transpose of `P`,
  with explicit coefficients, for `Aᵢⱼ` of class `C²`, `Bᵢ` of class `C¹` and `C` continuous
  on `U`.
* `SymplecticGeometry.exists_integral_apply_eq_integral_transpose_apply`: for smooth
  coefficients, the transpose has smooth coefficients.
* `SymplecticGeometry.exists_abs_integral_sum_mul_apply_le`: an energy bound. For `C¹` maps
  `φ q : E → F →L[ℝ] ℝ` and functionals `ℓ q` on `F`, the integral of
  `∑_q ℓ q (a y) * φ q y (P a y)` over `a` of class `C²` supported in a compact `K ⊆ U` is at
  most a constant times `(‖a‖_{L²} + ∑ᵢ ‖∂_{v_i} a‖_{L²}) ^ 2`, with `Aᵢⱼ` of class `C¹` and
  `Bᵢ`, `C` continuous on `U`. One integration by parts in each second-order term
  (`SymplecticGeometry.integral_apply_apply_fderiv_eq_integral_neg_apply`) leaves an integrand
  bounded by a multiple of `(‖a‖ + ∑ᵢ ‖∂_{v_i} a‖) ^ 2`, whose integral
  `MeasureTheory.integral_sum_norm_sq_le` bounds. Read in a chart, this bounds the
  Dirichlet pairing `⟪Δφ, φ⟫` of a form `φ` supported in the chart.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983,
  Chapter III (the transpose of a differential operator).
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology ENNReal

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The integral of `∑ᵢⱼ f₂ᵢⱼ + ∑ᵢ f₁ᵢ + f₀` is the sum of the integrals of its terms, when all of
them are integrable. -/
private theorem integral_sum_sum_add_sum_add {α ι G : Type*} [MeasurableSpace α]
    {μ : Measure α} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f₂ : ι → ι → α → G) (f₁ : ι → α → G) (f₀ : α → G)
    (h₂ : ∀ i j, Integrable (f₂ i j) μ) (h₁ : ∀ i, Integrable (f₁ i) μ) (h₀ : Integrable f₀ μ) :
    ∫ y, (∑ i, ∑ j, f₂ i j y + ∑ i, f₁ i y + f₀ y) ∂μ =
      ∑ i, ∑ j, ∫ y, f₂ i j y ∂μ + ∑ i, ∫ y, f₁ i y ∂μ + ∫ y, f₀ y ∂μ := by
  have hs₂ : Integrable (fun y ↦ ∑ i, ∑ j, f₂ i j y) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h₂ i j
  have hs₁ : Integrable (fun y ↦ ∑ i, f₁ i y) μ := integrable_finsetSum _ fun i _ ↦ h₁ i
  rw [integral_add (f := fun y ↦ ∑ i, ∑ j, f₂ i j y + ∑ i, f₁ i y) (hs₂.add hs₁) h₀,
    integral_add hs₂ hs₁, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ h₂ i j,
    integral_finsetSum _ fun i _ ↦ h₁ i]
  simp_rw [integral_finsetSum _ fun j _ ↦ h₂ _ j]

/-- The pointwise identity behind `integral_apply_eq_integral_transpose_apply`: the terms that
integration by parts produces add up to `P' w`, at a point where `w` and the `Aᵢⱼ` are `C²`. -/
private theorem sum_fderiv_fderiv_smul_add_eq_transpose_apply {ι : Type*} [Fintype ι] (v : ι → E)
    {A : ι → ι → E → ℝ} (B : ι → E → F →L[ℝ] F) (C : E → F →L[ℝ] F) {w : E → F →L[ℝ] ℝ}
    {y : E} (hA : ∀ i j, ContDiffAt ℝ 2 (A i j) y) (hw : ContDiffAt ℝ 2 w y) (x : F) :
    ∑ i, ∑ j, fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ A i j z • w z) z (v j)) y (v i) x +
        ∑ i, (-((fderiv ℝ w y (v i)).comp (B i y) + (w y).comp (fderiv ℝ (B i) y (v i)))) x +
        w y (C y x) =
      (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ w z (v i)) y (v j) +
        ∑ i, (fderiv ℝ w y (v i)).comp
          ((∑ j, fderiv ℝ (A i j) y (v j) + ∑ j, fderiv ℝ (A j i) y (v j)) •
            ContinuousLinearMap.id ℝ F - B i y) +
        (w y).comp ((∑ i, ∑ j, fderiv ℝ (fun z ↦ fderiv ℝ (A i j) z (v j)) y (v i)) •
            ContinuousLinearMap.id ℝ F - ∑ i, fderiv ℝ (B i) y (v i) + C y)) x := by
  have hAw (i j : ι) (u u' : E) :
      fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ A i j z • w z) z u) y u' =
        A i j y • fderiv ℝ (fun z ↦ fderiv ℝ w z u) y u' +
          fderiv ℝ (fun z ↦ fderiv ℝ (A i j) z u) y u' • w y +
          fderiv ℝ (A i j) y u' • fderiv ℝ w y u + fderiv ℝ (A i j) y u • fderiv ℝ w y u' := by
    have hAw : ContDiffAt ℝ 2 (fun z ↦ A i j z • w z) y := (hA i j).smul hw
    rw [TauCeti.fderiv_clm_apply_const_apply (hAw.hasFDerivAt_fderiv le_rfl).differentiableAt,
      TauCeti.fderiv_fderiv_fun_smul_apply (hA i j) hw,
      TauCeti.fderiv_clm_apply_const_apply ((hA i j).hasFDerivAt_fderiv le_rfl).differentiableAt,
      TauCeti.fderiv_clm_apply_const_apply (hw.hasFDerivAt_fderiv le_rfl).differentiableAt]
  have hc (u u' : E) := TauCeti.fderiv_fderiv_apply_comm hw (n := 2) (by simp) u u'
  simp only [hAw, add_apply, sum_apply,
    neg_apply, smul_apply, sub_apply,
    map_add, map_sum, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub,
    map_smul, Finset.sum_add_distrib, Finset.sum_smul, smul_eq_mul]
  rw [Finset.sum_comm (f := fun i j ↦ fderiv ℝ (A i j) y (v i) * fderiv ℝ w y (v j) x)]
  simp only [hc, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    add_mul, Finset.sum_mul]
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {U : Set E}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] in
/-- A function continuous on `U` that vanishes off the support of `a`, compact and contained in
`U`, is integrable. This is the integrability of the terms that the integrations by parts of
this file split an integral into. -/
private theorem integrable_of_continuousOn_of_eq_zero {G : Type*} [NormedAddCommGroup G]
    {a : E → F} (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) {h : E → G}
    (hh : ContinuousOn h U) (hz : ∀ y ∉ tsupport a, h y = 0) : Integrable h μ :=
  ((hh.mono haU).integrableOn_compact hac).integrable_of_forall_notMem_eq_zero hz

/-- **Transposing a first-order term.** For `B`, `C¹` on an open set `U`, `w`, `C¹` on `U`, and `a`,
`C¹` with compact support in `U`, `∫ w (B ∂_u a) = ∫ (-(∂_u w) ∘ B - w ∘ ∂_u B) a`. -/
theorem integral_apply_apply_fderiv_eq_integral_neg_apply (hU : IsOpen U) {B : E → F →L[ℝ] F}
    (hB : ContDiffOn ℝ 1 B U) {w : E → F →L[ℝ] ℝ} (hw : ContDiffOn ℝ 1 w U) {a : E → F}
    (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) (u : E) :
    ∫ y, w y (B y (fderiv ℝ a y u)) ∂μ =
      ∫ y, (-((fderiv ℝ w y u).comp (B y) + (w y).comp (fderiv ℝ B y u))) (a y) ∂μ := by
  have h := TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport (μ := μ)
    (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)) (f := fun y ↦ (w y).comp (B y))
    (fun y hy ↦ ((hw.contDiffAt (hU.mem_nhds (haU hy))).clm_comp
      (hB.contDiffAt (hU.mem_nhds (haU hy))))) ha hac u
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h
  rw [h, ← integral_neg]
  congr 1 with y
  by_cases hy : y ∈ tsupport a
  · have hyU := hU.mem_nhds (haU hy)
    rw [fderiv_clm_comp ((hw.contDiffAt hyU).differentiableAt one_ne_zero)
      ((hB.contDiffAt hyU).differentiableAt one_ne_zero)]
    simp [add_comm]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Transposing a second-order term.** For a scalar `φ` and a map `w`, both `C²` on an open set
`U`, and `a`, `C²` with compact support in `U`, `∫ w (φ ∂_{u'} ∂_u a) = ∫ (∂_u ∂_{u'} (φ w)) a`. -/
theorem integral_apply_smul_fderiv_fderiv_eq_integral_fderiv_fderiv_apply (hU : IsOpen U)
    {φ : E → ℝ} (hφ : ContDiffOn ℝ 2 φ U) {w : E → F →L[ℝ] ℝ} (hw : ContDiffOn ℝ 2 w U)
    {a : E → F} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U)
    (u u' : E) :
    ∫ y, w y (φ y • fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u') ∂μ =
      ∫ y, fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ φ z • w z) z u') y u (a y) ∂μ := by
  have hφw (y : E) (hy : y ∈ tsupport a) : ContDiffAt ℝ 2 (fun z ↦ φ z • w z) y :=
    (hφ.contDiffAt (hU.mem_nhds (haU hy))).smul (hw.contDiffAt (hU.mem_nhds (haU hy)))
  have hda : ContDiff ℝ 1 fun z ↦ fderiv ℝ a z u :=
    (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  -- The first integration by parts, in the direction `u'`.
  have h₁ := TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport (μ := μ)
    (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)) (f := fun y ↦ φ y • w y)
    (fun y hy ↦ (hφw y (tsupport_fderiv_apply_subset ℝ u hy)).of_le (by norm_num)) hda
    (hac.fderiv_apply (𝕜 := ℝ) u) u'
  -- The second one, in the direction `u`.
  have h₂ := TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport (μ := μ)
    (ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)) (f := fun y ↦ fderiv ℝ (fun z ↦ φ z • w z) y u')
    (fun y hy ↦ ((hφw y hy).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
    (ha.of_le (by norm_num)) hac u
  simp only [ContinuousLinearMap.id_apply] at h₁ h₂
  calc ∫ y, w y (φ y • fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u') ∂μ
      = ∫ y, (φ y • w y) (fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u') ∂μ := by simp
    _ = _ := by rw [h₁, h₂, neg_neg]

/-- **The formal transpose of a second-order operator.** Let `U` be an open subset of `E`,
`v : ι → E` a finite family, and `P a = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} a + ∑ᵢ Bᵢ ∂_{v_i} a + C a` an
operator on maps `E → F`, with scalar coefficients `Aᵢⱼ` of class `C²` on `U`, coefficients
`Bᵢ : E → F →L[ℝ] F` of class `C¹` on `U` and `C : E → F →L[ℝ] F` continuous on `U`. Then
`∫ w (P a) dμ = ∫ (P' w) a dμ` for every `w : E → F →L[ℝ] ℝ` that is `C²` on `U` and every `a`
that is `C²` with compact support in `U`, where
`P' w = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} w + ∑ᵢ (∂_{v_i} w) ∘ B'ᵢ + w ∘ C'` with
`B'ᵢ = (∑ⱼ ∂_{v_j} Aᵢⱼ + ∑ⱼ ∂_{v_j} Aⱼᵢ) • id - Bᵢ` and
`C' = (∑ᵢⱼ ∂_{v_i} ∂_{v_j} Aᵢⱼ) • id - ∑ᵢ ∂_{v_i} Bᵢ + C`. -/
theorem integral_apply_eq_integral_transpose_apply {ι : Type*} [Fintype ι] (hU : IsOpen U)
    (v : ι → E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ 2 (A i j) U) (hB : ∀ i, ContDiffOn ℝ 1 (B i) U)
    (hC : ContinuousOn C U) {w : E → F →L[ℝ] ℝ} {a : E → F} (hw : ContDiffOn ℝ 2 w U)
    (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    ∫ y, w y (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
        ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) ∂μ =
      ∫ y, (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ w z (v i)) y (v j) +
        ∑ i, (fderiv ℝ w y (v i)).comp
          ((∑ j, fderiv ℝ (A i j) y (v j) + ∑ j, fderiv ℝ (A j i) y (v j)) •
            ContinuousLinearMap.id ℝ F - B i y) +
        (w y).comp ((∑ i, ∑ j, fderiv ℝ (fun z ↦ fderiv ℝ (A i j) z (v j)) y (v i)) •
            ContinuousLinearMap.id ℝ F - ∑ i, fderiv ℝ (B i) y (v i) + C y)) (a y) ∂μ := by
  have int (h : E → ℝ) (hh : ContinuousOn h U) (hz : ∀ y ∉ tsupport a, h y = 0) :
      Integrable h μ :=
    integrable_of_continuousOn_of_eq_zero hac haU hh hz
  -- Outside the support of `a`, `a` and its first two derivatives vanish.
  have h0 (y : E) (hy : y ∉ tsupport a) : a y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h1 (y : E) (hy : y ∉ tsupport a) (u : E) : fderiv ℝ a y u = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ hy]
  have h2 (y : E) (hy : y ∉ tsupport a) (u u' : E) :
      fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u' = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ fun h ↦ hy (tsupport_fderiv_apply_subset ℝ u h)]
  have hdda (u u' : E) : Continuous fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u' :=
    (((ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hAw (i j : ι) : ContDiffOn ℝ 2 (fun y ↦ A i j y • w y) U := (hA i j).smul hw
  -- Split `w (P a)` into its terms, and transpose each of them.
  rw [integral_congr_ae (g := fun y ↦ ∑ i, ∑ j, w y (A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z
      (v i)) y (v j)) + ∑ i, w y (B i y (fderiv ℝ a y (v i))) + w y (C y (a y)))
      (Filter.Eventually.of_forall fun y ↦ by simp only [map_add, map_sum])]
  rw [integral_sum_sum_add_sum_add
    (fun i j y ↦ w y (A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j)))
    (fun i y ↦ w y (B i y (fderiv ℝ a y (v i)))) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ int _ (hw.continuousOn.clm_apply ((hA i j).continuousOn.smul
      (hdda _ _).continuousOn)) fun y hy ↦ by simp [h2 y hy])
    (fun i ↦ int _ (hw.continuousOn.clm_apply ((hB i).continuousOn.clm_apply
      ((ha.continuous_fderiv two_ne_zero).clm_apply continuous_const).continuousOn))
      fun y hy ↦ by simp [h1 y hy])
    (int _ (hw.continuousOn.clm_apply (hC.clm_apply ha.continuous.continuousOn))
      fun y hy ↦ by simp [h0 y hy])]
  simp only [integral_apply_smul_fderiv_fderiv_eq_integral_fderiv_fderiv_apply (μ := μ) hU
      (hA _ _) hw ha hac haU,
    integral_apply_apply_fderiv_eq_integral_neg_apply (μ := μ) hU (hB _) (hw.of_le (by norm_num))
      (ha.of_le (by norm_num)) hac haU]
  rw [← integral_sum_sum_add_sum_add
    (fun i j y ↦ fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ A i j z • w z) z (v j)) y (v i) (a y))
    (fun i y ↦ (-((fderiv ℝ w y (v i)).comp (B i y) + (w y).comp (fderiv ℝ (B i) y (v i))))
      (a y)) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ int _ ((((hAw i j).fderiv_apply_of_isOpen hU (m := 1) (by norm_num)
      (v j)).fderiv_apply_of_isOpen hU (m := 0) (by norm_num) (v i)).continuousOn.clm_apply
      ha.continuous.continuousOn) fun y hy ↦ by simp [h0 y hy])
    (fun i ↦ int _ ((((hw.fderiv_apply_of_isOpen hU (m := 1) (by norm_num)
      (v i)).continuousOn.clm_comp (hB i).continuousOn).add
      (hw.continuousOn.clm_comp ((hB i).fderiv_apply_of_isOpen hU (m := 0) (by simp)
        (v i)).continuousOn)).neg.clm_apply ha.continuous.continuousOn)
      fun y hy ↦ by simp [h0 y hy])
    (int _ (hw.continuousOn.clm_apply (hC.clm_apply ha.continuous.continuousOn))
      fun y hy ↦ by simp [h0 y hy])]
  -- The integrands agree: off the support of `a` both vanish, and on it by the Leibniz rule.
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ tsupport a
  · have hyU := hU.mem_nhds (haU hy)
    exact sum_fderiv_fderiv_smul_add_eq_transpose_apply v B C
      (fun i j ↦ (hA i j).contDiffAt hyU) (hw.contDiffAt hyU) (a y)
  · simp [h0 y hy]

/-- **The formal transpose of a second-order operator with smooth coefficients.** Let `U` be an
open subset of `E`, `v : ι → E` a finite family, and
`P a = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} a + ∑ᵢ Bᵢ ∂_{v_i} a + C a` an operator on maps `E → F` with scalar
coefficients `Aᵢⱼ` and coefficients `Bᵢ`, `C` in `F →L[ℝ] F`, all smooth on `U`. Then there are
`B'ᵢ` and `C'` in `F →L[ℝ] F`, smooth on `U`, such that the operator
`P' w = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} w + ∑ᵢ (∂_{v_i} w) ∘ B'ᵢ + w ∘ C'` on maps `E → F →L[ℝ] ℝ`
satisfies `∫ w (P a) dμ = ∫ (P' w) a dμ` for every `w` that is `C²` on `U` and every `a` that is
`C²` with compact support in `U`. The coefficients are those of
`integral_apply_eq_integral_transpose_apply`. -/
theorem exists_integral_apply_eq_integral_transpose_apply {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (v : ι → E) (A : ι → ι → E → ℝ) (B : ι → E → F →L[ℝ] F)
    (C : E → F →L[ℝ] F) (hA : ∀ i j, ContDiffOn ℝ ∞ (A i j) U)
    (hB : ∀ i, ContDiffOn ℝ ∞ (B i) U) (hC : ContDiffOn ℝ ∞ C U) :
    ∃ (B' : ι → E → F →L[ℝ] F) (C' : E → F →L[ℝ] F),
      (∀ i, ContDiffOn ℝ ∞ (B' i) U) ∧ ContDiffOn ℝ ∞ C' U ∧
      ∀ (w : E → F →L[ℝ] ℝ) (a : E → F), ContDiffOn ℝ 2 w U → ContDiff ℝ 2 a →
        HasCompactSupport a → tsupport a ⊆ U →
        ∫ y, w y (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
            ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) ∂μ =
          ∫ y, (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ w z (v i)) y (v j) +
            ∑ i, (fderiv ℝ w y (v i)).comp (B' i y) + (w y).comp (C' y)) (a y) ∂μ := by
  have hdA (i j : ι) : ContDiffOn ℝ ∞ (fun y ↦ fderiv ℝ (A i j) y (v j)) U :=
    (hA i j).fderiv_apply_of_isOpen hU (by simp) (v j)
  refine ⟨fun i y ↦ ((∑ j, fderiv ℝ (A i j) y (v j) + ∑ j, fderiv ℝ (A j i) y (v j)) •
      ContinuousLinearMap.id ℝ F - B i y : F →L[ℝ] F),
    fun y ↦ ((∑ i, ∑ j, fderiv ℝ (fun z ↦ fderiv ℝ (A i j) z (v j)) y (v i)) •
      ContinuousLinearMap.id ℝ F - ∑ i, fderiv ℝ (B i) y (v i) + C y : F →L[ℝ] F), fun i ↦ ?_, ?_,
    fun w a hw ha hac haU ↦ ?_⟩
  · exact (((ContDiffOn.sum fun j _ ↦ hdA i j).add (ContDiffOn.sum fun j _ ↦
      (hA j i).fderiv_apply_of_isOpen hU (by simp) (v j))).smul
      contDiffOn_const).sub (hB i)
  · exact (((ContDiffOn.sum fun i _ ↦ ContDiffOn.sum fun j _ ↦
      (hdA i j).fderiv_apply_of_isOpen hU (by simp) (v i)).smul contDiffOn_const).sub
      (ContDiffOn.sum fun i _ ↦ (hB i).fderiv_apply_of_isOpen hU (by simp) (v i))).add hC
  exact integral_apply_eq_integral_transpose_apply (A := A) (B := B) (C := C) hU v
    (fun i j ↦ (hA i j).of_le (by simp)) (fun i ↦ (hB i).of_le (by simp)) hC.continuousOn hw ha
    hac haU

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise bound behind `exists_abs_integral_sum_mul_apply_le`. Write `w = (ℓ ∘ a) • φ`
and `N = ‖a‖ + ∑ᵢ ‖∂_{v_i} a‖`. At a point where `a` and `φ` are differentiable, the integrand
left by one integration by parts in each second-order term, with coefficients `Bt i j`, is at most
`‖ℓ‖ * Q * N ^ 2`, where `Q` collects the norms of `φ`, of its derivatives and of the
coefficients. -/
private theorem norm_sum_sum_neg_comp_add_le {ι : Type*} [Fintype ι] (v : ι → E)
    (Bt : ι → ι → E → F →L[ℝ] F) (B : ι → E → F →L[ℝ] F) (C : E → F →L[ℝ] F)
    (φ : E → F →L[ℝ] ℝ) (ℓ : F →L[ℝ] ℝ) {a : E → F} {y : E} (ha : DifferentiableAt ℝ a y)
    (hφ : DifferentiableAt ℝ φ y) :
    ‖∑ i, ∑ j, (-((fderiv ℝ (fun z ↦ ℓ (a z) • φ z) y (v j)).comp (Bt i j y) +
          (ℓ (a y) • φ y).comp (fderiv ℝ (Bt i j) y (v j)))) (fderiv ℝ a y (v i)) +
        ∑ i, (ℓ (a y) • φ y) (B i y (fderiv ℝ a y (v i))) + (ℓ (a y) • φ y) (C y (a y))‖ ≤
      ‖ℓ‖ * (∑ i, ∑ j, ((‖φ y‖ + ‖fderiv ℝ φ y (v j)‖) * ‖Bt i j y‖ +
          ‖φ y‖ * ‖fderiv ℝ (Bt i j) y (v j)‖) + ∑ i, ‖φ y‖ * ‖B i y‖ + ‖φ y‖ * ‖C y‖) *
        (‖a y‖ + ∑ i, ‖fderiv ℝ a y (v i)‖) ^ 2 := by
  set N := ‖a y‖ + ∑ i, ‖fderiv ℝ a y (v i)‖
  have haN : ‖a y‖ ≤ N := le_add_of_nonneg_right (by positivity)
  have hgN (i : ι) : ‖fderiv ℝ a y (v i)‖ ≤ N :=
    (Finset.single_le_sum (f := fun i ↦ ‖fderiv ℝ a y (v i)‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left (norm_nonneg _))
  have hℓ (x : F) (hx : ‖x‖ ≤ N) : ‖ℓ x‖ ≤ ‖ℓ‖ * N :=
    (ℓ.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hw : ‖ℓ (a y) • φ y‖ ≤ ‖ℓ‖ * N * ‖φ y‖ := by
    rw [norm_smul]
    gcongr
    exact hℓ _ haN
  -- The Leibniz rule for `w = (ℓ ∘ a) • φ`.
  have hdw (j : ι) : ‖fderiv ℝ (fun z ↦ ℓ (a z) • φ z) y (v j)‖ ≤
      ‖ℓ‖ * N * (‖φ y‖ + ‖fderiv ℝ φ y (v j)‖) := by
    have hda : HasFDerivAt (fun z ↦ ℓ (a z)) (ℓ.comp (fderiv ℝ a y)) y :=
      ℓ.hasFDerivAt.comp y ha.hasFDerivAt
    rw [fderiv_fun_smul hda.differentiableAt hφ, hda.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smulRight_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, mul_add, add_comm (‖ℓ‖ * N * ‖φ y‖)]
    gcongr <;> first | exact hℓ _ (hgN j) | exact hℓ _ haN
  calc _ ≤ ∑ i, ∑ j, ‖ℓ‖ * ((‖φ y‖ + ‖fderiv ℝ φ y (v j)‖) * ‖Bt i j y‖ +
          ‖φ y‖ * ‖fderiv ℝ (Bt i j) y (v j)‖) * N ^ 2 +
        ∑ i, ‖ℓ‖ * (‖φ y‖ * ‖B i y‖) * N ^ 2 + ‖ℓ‖ * (‖φ y‖ * ‖C y‖) * N ^ 2 := by
        refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) ?_)
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ ↦ ?_))
          refine (le_opNorm _ _).trans ?_
          rw [norm_neg]
          calc _ ≤ (‖fderiv ℝ (fun z ↦ ℓ (a z) • φ z) y (v j)‖ * ‖Bt i j y‖ +
                ‖ℓ (a y) • φ y‖ * ‖fderiv ℝ (Bt i j) y (v j)‖) * ‖fderiv ℝ a y (v i)‖ := by
                gcongr
                exact (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))
            _ ≤ (‖ℓ‖ * N * (‖φ y‖ + ‖fderiv ℝ φ y (v j)‖) * ‖Bt i j y‖ +
                ‖ℓ‖ * N * ‖φ y‖ * ‖fderiv ℝ (Bt i j) y (v j)‖) * N := by
                gcongr
                all_goals first | exact hdw j | exact hgN i
            _ = _ := by ring
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
          calc _ ≤ ‖ℓ (a y) • φ y‖ * (‖B i y‖ * ‖fderiv ℝ a y (v i)‖) :=
                (le_opNorm _ _).trans (by gcongr; exact le_opNorm _ _)
            _ ≤ ‖ℓ‖ * N * ‖φ y‖ * (‖B i y‖ * N) := by gcongr; exact hgN i
            _ = _ := by ring
        · calc _ ≤ ‖ℓ (a y) • φ y‖ * (‖C y‖ * ‖a y‖) :=
                (le_opNorm _ _).trans (by gcongr; exact le_opNorm _ _)
            _ ≤ ‖ℓ‖ * N * ‖φ y‖ * (‖C y‖ * N) := by gcongr
            _ = _ := by ring
    _ = _ := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum]
        ring

/-- One integration by parts in each second-order term of `∫ ℓ (a y) * φ y (P a y) dμ`, for `a` of
class `C²` with compact support in `U`. With `w = (ℓ ∘ a) • φ`, the term
`w (Aᵢⱼ ∂_{v_j} ∂_{v_i} a)` becomes
`-((∂_{v_j} w) ∘ (Aᵢⱼ • id) + w ∘ ∂_{v_j} (Aᵢⱼ • id)) (∂_{v_i} a)`,
and the other terms stay. -/
private theorem integral_mul_apply_eq_integral_sum_sum_neg_comp_add {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (v : ι → E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ 1 (A i j) U) (hB : ∀ i, ContinuousOn (B i) U)
    (hC : ContinuousOn C U) {φ : E → F →L[ℝ] ℝ} (hφ : ContDiffOn ℝ 1 φ U) (ℓ : F →L[ℝ] ℝ)
    {a : E → F} (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    ∫ y, ℓ (a y) * φ y (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
        ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) ∂μ =
      ∫ y, (∑ i, ∑ j, (-((fderiv ℝ (fun z ↦ ℓ (a z) • φ z) y (v j)).comp
          (A i j y • ContinuousLinearMap.id ℝ F) + (ℓ (a y) • φ y).comp
            (fderiv ℝ (fun z ↦ A i j z • ContinuousLinearMap.id ℝ F) y (v j))))
              (fderiv ℝ a y (v i)) +
        ∑ i, (ℓ (a y) • φ y) (B i y (fderiv ℝ a y (v i))) + (ℓ (a y) • φ y) (C y (a y))) ∂μ := by
  set Bt : ι → ι → E → F →L[ℝ] F := fun i j y ↦ A i j y • ContinuousLinearMap.id ℝ F
  have hBt (i j : ι) : ContDiffOn ℝ 1 (Bt i j) U := (hA i j).smul contDiffOn_const
  set g : ι → E → F := fun i y ↦ fderiv ℝ a y (v i)
  have hg (i : ι) : ContDiff ℝ 1 (g i) :=
    (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgU (i : ι) : tsupport (g i) ⊆ U := (tsupport_fderiv_apply_subset ℝ (v i)).trans haU
  have h0 (y : E) (hy : y ∉ tsupport a) : a y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h1 (y : E) (hy : y ∉ tsupport a) (i : ι) : g i y = 0 := by
    simp [g, fderiv_of_notMem_tsupport ℝ hy]
  -- The test function `w = (ℓ ∘ a) • φ` is `C¹` on `U`.
  set w : E → F →L[ℝ] ℝ := fun y ↦ ℓ (a y) • φ y
  have hw : ContDiffOn ℝ 1 w U :=
    (ℓ.contDiff.comp (ha.of_le (by norm_num))).contDiffOn.smul hφ
  have hdw (j : ι) : ContinuousOn (fun y ↦ fderiv ℝ w y (v j)) U :=
    (hw.fderiv_apply_of_isOpen hU (m := 0) (by simp) (v j)).continuousOn
  have hdBt (i j : ι) : ContinuousOn (fun y ↦ fderiv ℝ (Bt i j) y (v j)) U :=
    ((hBt i j).fderiv_apply_of_isOpen hU (m := 0) (by simp) (v j)).continuousOn
  -- Split the integral into its terms and integrate by parts in each second-order term.
  rw [integral_congr_ae (g := fun y ↦ ∑ i, ∑ j, w y (Bt i j y (fderiv ℝ (g i) y (v j))) +
      ∑ i, w y (B i y (g i y)) + w y (C y (a y)))
      (Filter.Eventually.of_forall fun y ↦ by
        simp [w, Bt, g, mul_add, Finset.mul_sum, mul_left_comm])]
  have hT₁ (i : ι) : Integrable (fun y ↦ w y (B i y (g i y))) μ :=
    integrable_of_continuousOn_of_eq_zero hac haU (hw.continuousOn.clm_apply ((hB i).clm_apply
      (hg i).continuous.continuousOn)) fun y hy ↦ by simp [w, h0 y hy]
  have hT₀ : Integrable (fun y ↦ w y (C y (a y))) μ :=
    integrable_of_continuousOn_of_eq_zero hac haU
      (hw.continuousOn.clm_apply (hC.clm_apply ha.continuous.continuousOn))
      fun y hy ↦ by simp [w, h0 y hy]
  rw [integral_sum_sum_add_sum_add (fun i j y ↦ w y (Bt i j y (fderiv ℝ (g i) y (v j))))
    (fun i y ↦ w y (B i y (g i y))) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ integrable_of_continuousOn_of_eq_zero hac haU (hw.continuousOn.clm_apply
      ((hBt i j).continuousOn.clm_apply
        (((hg i).continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn))
      fun y hy ↦ by simp [w, h0 y hy]) hT₁ hT₀]
  simp only [integral_apply_apply_fderiv_eq_integral_neg_apply (μ := μ) hU (hBt _ _) hw (hg _)
    (hac.fderiv_apply (𝕜 := ℝ) _) (hgU _)]
  rw [← integral_sum_sum_add_sum_add
    (fun i j y ↦ (-((fderiv ℝ w y (v j)).comp (Bt i j y) +
      (w y).comp (fderiv ℝ (Bt i j) y (v j)))) (g i y))
    (fun i y ↦ w y (B i y (g i y))) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ integrable_of_continuousOn_of_eq_zero hac haU
      ((((hdw j).clm_comp (hBt i j).continuousOn).add (hw.continuousOn.clm_comp (hdBt i j))).neg
        |>.clm_apply (hg i).continuous.continuousOn) fun y hy ↦ by simp [h1 y hy]) hT₁ hT₀]

/-- The step of `exists_abs_integral_sum_mul_apply_le` for one term `ℓ (a y) * φ y (P a y)`. -/
private theorem exists_abs_integral_mul_apply_le {ι : Type*} [Fintype ι] (hU : IsOpen U)
    (v : ι → E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F} {C : E → F →L[ℝ] F}
    (hA : ∀ i j, ContDiffOn ℝ 1 (A i j) U) (hB : ∀ i, ContinuousOn (B i) U)
    (hC : ContinuousOn C U) {φ : E → F →L[ℝ] ℝ} (hφ : ContDiffOn ℝ 1 φ U) (ℓ : F →L[ℝ] ℝ)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c, ∀ a : E → F, ContDiff ℝ 2 a → tsupport a ⊆ K →
      |∫ y, ℓ (a y) * φ y (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
        ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) ∂μ| ≤
        c * ((eLpNorm a 2 μ).toReal +
          ∑ i, (eLpNorm (fun y ↦ fderiv ℝ a y (v i)) 2 μ).toReal) ^ 2 := by
  -- With the coefficients `A i j • id` of the second-order terms, the factor `Q` of
  -- `norm_sum_sum_neg_comp_add_le` is continuous on `U`, so bounded on `K`.
  set Bt : ι → ι → E → F →L[ℝ] F := fun i j y ↦ A i j y • ContinuousLinearMap.id ℝ F
  have hBt (i j : ι) : ContDiffOn ℝ 1 (Bt i j) U := (hA i j).smul contDiffOn_const
  have hdφ (u : E) : ContinuousOn (fun y ↦ fderiv ℝ φ y u) U :=
    (hφ.fderiv_apply_of_isOpen hU (m := 0) (by simp) u).continuousOn
  have hdBt (i j : ι) (u : E) : ContinuousOn (fun y ↦ fderiv ℝ (Bt i j) y u) U :=
    ((hBt i j).fderiv_apply_of_isOpen hU (m := 0) (by simp) u).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun y ↦
    ∑ i, ∑ j, ((‖φ y‖ + ‖fderiv ℝ φ y (v j)‖) * ‖Bt i j y‖ +
      ‖φ y‖ * ‖fderiv ℝ (Bt i j) y (v j)‖) + ∑ i, ‖φ y‖ * ‖B i y‖ + ‖φ y‖ * ‖C y‖)
    ((((continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      ((hφ.continuousOn.norm.add (hdφ (v j)).norm).mul (hBt i j).continuousOn.norm).add
        (hφ.continuousOn.norm.mul (hdBt i j (v j)).norm)).add
      (continuousOn_finsetSum _ fun i _ ↦ hφ.continuousOn.norm.mul (hB i).norm)).add
      (hφ.continuousOn.norm.mul hC.norm)).mono hKU)
  refine ⟨‖ℓ‖ * max M 0, fun a ha haK ↦ ?_⟩
  have hac : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport a) haK
  have haU : tsupport a ⊆ U := haK.trans hKU
  rw [integral_mul_apply_eq_integral_sum_sum_neg_comp_add hU v hA hB hC hφ ℓ ha hac haU]
  set g : ι → E → F := fun i y ↦ fderiv ℝ a y (v i)
  have hg (i : ι) : ContDiff ℝ 1 (g i) :=
    (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h0 (y : E) (hy : y ∉ tsupport a) : a y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h1 (y : E) (hy : y ∉ tsupport a) (i : ι) : g i y = 0 := by
    simp [g, fderiv_of_notMem_tsupport ℝ hy]
  -- The integrand is at most `‖ℓ‖ * max M 0 * N ^ 2`, with `N = ‖a‖ + ∑ᵢ ‖∂_{v_i} a‖`, and the
  -- integral of `N ^ 2` is at most the square of the sum of the `L²` norms.
  set N : E → ℝ := fun y ↦ ‖a y‖ + ∑ i, ‖g i y‖
  have hNi : Integrable (fun y ↦ N y ^ 2) μ :=
    integrable_of_continuousOn_of_eq_zero hac haU ((ha.continuous.norm.add
      (continuous_finsetSum _ fun i _ ↦ (hg i).continuous.norm)).pow 2).continuousOn
      fun y hy ↦ by simp [N, h0 y hy, h1 y hy]
  have hpt (y : E) : ‖∑ i, ∑ j, (-((fderiv ℝ (fun z ↦ ℓ (a z) • φ z) y (v j)).comp (Bt i j y) +
      (ℓ (a y) • φ y).comp (fderiv ℝ (Bt i j) y (v j)))) (g i y) +
      ∑ i, (ℓ (a y) • φ y) (B i y (g i y)) + (ℓ (a y) • φ y) (C y (a y))‖ ≤
      ‖ℓ‖ * max M 0 * N y ^ 2 := by
    by_cases hy : y ∈ tsupport a
    · refine (norm_sum_sum_neg_comp_add_le v Bt B C φ ℓ (ha.differentiable (by norm_num) y)
        ((hφ.contDiffAt (hU.mem_nhds (haU hy))).differentiableAt one_ne_zero)).trans ?_
      gcongr
      exact (le_abs_self _).trans ((hM y (haK hy)).trans (le_max_left _ _))
    · simp only [h0 y hy, h1 y hy, map_zero, zero_smul, Finset.sum_const_zero, add_zero,
        norm_zero]
      positivity
  have hN2 : ∫ y, N y ^ 2 ∂μ ≤ ((eLpNorm a 2 μ).toReal + ∑ i, (eLpNorm (g i) 2 μ).toReal) ^ 2 := by
    have hm (o : Option ι) (_ : o ∈ Finset.univ) : MemLp (o.elim a g) 2 μ := by
      cases o with
      | none => exact ha.continuous.memLp_of_hasCompactSupport hac
      | some i =>
        exact (hg i).continuous.memLp_of_hasCompactSupport (hac.fderiv_apply (𝕜 := ℝ) (v i))
    simpa [Fintype.sum_option, N] using integral_sum_norm_sq_le Finset.univ hm
  calc |∫ y, _ ∂μ| = ‖∫ y, _ ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖ℓ‖ * max M 0 * N y ^ 2 ∂μ :=
        norm_integral_le_of_norm_le (hNi.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = ‖ℓ‖ * max M 0 * ∫ y, N y ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hN2 (by positivity)

/-- **A bound for the energy of a second-order operator.** Let `U` be an open subset of `E`,
`v : ι → E` a finite family, and `P a = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} a + ∑ᵢ Bᵢ ∂_{v_i} a + C a` an
operator on maps `E → F` with scalar coefficients `Aᵢⱼ` of class `C¹` on `U` and coefficients
`Bᵢ`, `C` in `F →L[ℝ] F` continuous on `U`. Let `ℓ q : F →L[ℝ] ℝ` and `φ q : E → F →L[ℝ] ℝ`, for
`q` in a finite type, with each `φ q` of class `C¹` on `U`. For every compact `K ⊆ U` there is
`c` such that, for every `a` of class `C²` supported in `K`,
`|∫ ∑_q ℓ q (a y) * φ q y (P a y) dμ| ≤ c * (‖a‖_{L²(μ)} + ∑ᵢ ‖∂_{v_i} a‖_{L²(μ)}) ^ 2`. -/
theorem exists_abs_integral_sum_mul_apply_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hU : IsOpen U) (v : ι → E) {A : ι → ι → E → ℝ} {B : ι → E → F →L[ℝ] F}
    {C : E → F →L[ℝ] F} (hA : ∀ i j, ContDiffOn ℝ 1 (A i j) U)
    (hB : ∀ i, ContinuousOn (B i) U) (hC : ContinuousOn C U) {φ : κ → E → F →L[ℝ] ℝ}
    (hφ : ∀ q, ContDiffOn ℝ 1 (φ q) U) (ℓ : κ → F →L[ℝ] ℝ) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ c, ∀ a : E → F, ContDiff ℝ 2 a → tsupport a ⊆ K →
      |∫ y, ∑ q, ℓ q (a y) * φ q y
          (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
            ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) ∂μ| ≤
        c * ((eLpNorm a 2 μ).toReal +
          ∑ i, (eLpNorm (fun y ↦ fderiv ℝ a y (v i)) 2 μ).toReal) ^ 2 := by
  choose c hc using fun q ↦
    exists_abs_integral_mul_apply_le (μ := μ) hU v hA hB hC (hφ q) (ℓ q) hK hKU
  refine ⟨∑ q, c q, fun a ha haK ↦ ?_⟩
  have hac : HasCompactSupport a := hK.of_isClosed_subset (isClosed_tsupport a) haK
  have haU : tsupport a ⊆ U := haK.trans hKU
  -- Each term is continuous on `U` and vanishes off the compact `tsupport a ⊆ U`.
  have hPa : ContinuousOn (fun y ↦ ∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y
      (v j) + ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y)) U :=
    ((continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      (hA i j).continuousOn.smul ((((ha.fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiff_const).continuous_fderiv one_ne_zero).clm_apply
          continuous_const).continuousOn).add
      (continuousOn_finsetSum _ fun i _ ↦ (hB i).clm_apply
        ((ha.continuous_fderiv two_ne_zero).clm_apply continuous_const).continuousOn)).add
      (hC.clm_apply ha.continuous.continuousOn)
  have hint (q : κ) : Integrable (fun y ↦ ℓ q (a y) * φ q y
      (∑ i, ∑ j, A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j) +
        ∑ i, B i y (fderiv ℝ a y (v i)) + C y (a y))) μ :=
    (((((ℓ q).continuous.comp ha.continuous).continuousOn.mul
      ((hφ q).continuousOn.clm_apply hPa)).mono haU).integrableOn_compact
        hac).integrable_of_forall_notMem_eq_zero fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_finsetSum _ fun q _ ↦ hint q, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ ↦ hc q a ha haK)

end SymplecticGeometry
