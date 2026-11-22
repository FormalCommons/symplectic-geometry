/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.LocallyIntegrable
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

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983,
  Chapter III (the transpose of a differential operator).
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace MeasureTheory

variable {α ι G : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The integral of `∑ᵢⱼ f₂ᵢⱼ + ∑ᵢ f₁ᵢ + f₀` is the sum of the integrals of its terms, when all of
them are integrable. -/
theorem integral_sum_sum_add_sum_add (f₂ : ι → ι → α → G) (f₁ : ι → α → G) (f₀ : α → G)
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

end MeasureTheory

namespace SymplecticGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

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
  -- A function continuous on `U` that vanishes off the compact `tsupport a ⊆ U` is integrable.
  have int (h : E → ℝ) (hh : ContinuousOn h U) (hz : ∀ y ∉ tsupport a, h y = 0) :
      Integrable h μ :=
    ((hh.mono haU).integrableOn_compact hac).integrable_of_forall_notMem_eq_zero hz
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

end SymplecticGeometry
