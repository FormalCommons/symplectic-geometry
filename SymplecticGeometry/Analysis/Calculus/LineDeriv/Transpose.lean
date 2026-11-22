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
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Calculus.ContDiff.FDerivApply

/-!
# The formal transpose of a second-order operator

Let `U` be an open subset of a finite-dimensional real space `E`, `v : ι → E` a finite family of
vectors, and `P` the second-order operator on maps `a : E → F`
`P a = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} a + ∑ᵢ Bᵢ ∂_{v_i} a + C a`,
with smooth coefficients on `U`: scalar `Aᵢⱼ`, and `Bᵢ`, `C` with values in `F →L[ℝ] F`. Its formal
transpose for an additive Haar measure `μ`, acting on maps `w : E → F →L[ℝ] ℝ` with the pairing
`⟨w, a⟩ = ∫ w a dμ`, is the operator
`P' w = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} w + ∑ᵢ (∂_{v_i} w) ∘ B'ᵢ + w ∘ C'`, with the same second-order
coefficients `Aᵢⱼ` and new smooth coefficients `B'ᵢ`, `C'` with values in `F →L[ℝ] F`:
`∫ w (P a) dμ = ∫ (P' w) a dμ` whenever `w` is `C²` on `U` and `a` is `C²` with compact support in
`U` (`SymplecticGeometry.exists_integral_apply_eq_integral_transpose_apply`). The second-order
coefficients carry over because they are scalars. The proof integrates by parts once for each
first-order term and twice for each second-order term, with Tau Ceti's
`TauCeti.integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport`, and expands the
derivatives of the products `Aᵢⱼ w` and `w ∘ Bᵢ` by the Leibniz rule
(`fderiv_fderiv_smul_apply`).

## Main results

* `fderiv_fderiv_smul_apply`: the Leibniz rule for a second directional derivative of `φ • w`.
* `SymplecticGeometry.exists_integral_apply_eq_integral_transpose_apply`: the formal transpose of
  `P`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Springer, 1983, §5.1
  (the transpose of a differential operator).
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **The Leibniz rule for a second directional derivative.** If a scalar function `φ` and a map
`w` are `C²` at `y`, then `∂_{u'} ∂_u (φ • w) = φ ∂_{u'} ∂_u w + ∂_{u'} φ ∂_u w + ∂_u φ ∂_{u'} w +
(∂_{u'} ∂_u φ) w` at `y`. -/
theorem fderiv_fderiv_smul_apply {φ : E → ℝ} {w : E → G} {y : E} (hφ : ContDiffAt ℝ 2 φ y)
    (hw : ContDiffAt ℝ 2 w y) (u u' : E) :
    fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ φ z • w z) z u) y u' =
      φ y • fderiv ℝ (fun z ↦ fderiv ℝ w z u) y u' + fderiv ℝ φ y u' • fderiv ℝ w y u +
        fderiv ℝ φ y u • fderiv ℝ w y u' + fderiv ℝ (fun z ↦ fderiv ℝ φ z u) y u' • w y := by
  -- Near `y`, the first derivative is given by the Leibniz rule.
  have hev : (fun z ↦ fderiv ℝ (fun z ↦ φ z • w z) z u) =ᶠ[𝓝 y]
      fun z ↦ φ z • fderiv ℝ w z u + fderiv ℝ φ z u • w z := by
    filter_upwards [hφ.eventually (by simp), hw.eventually (by simp)] with z hφz hwz
    rw [fderiv_fun_smul (hφz.differentiableAt (by simp)) (hwz.differentiableAt (by simp))]
    simp
  have hφ1 : DifferentiableAt ℝ φ y := hφ.differentiableAt (by simp)
  have hw1 : DifferentiableAt ℝ w y := hw.differentiableAt (by simp)
  have hφ2 : DifferentiableAt ℝ (fun z ↦ fderiv ℝ φ z u) y :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hw2 : DifferentiableAt ℝ (fun z ↦ fderiv ℝ w z u) y :=
    ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hD : HasFDerivAt (fun z ↦ φ z • fderiv ℝ w z u + fderiv ℝ φ z u • w z) _ y :=
    (hφ1.hasFDerivAt.smul hw2.hasFDerivAt).add (hφ2.hasFDerivAt.smul hw1.hasFDerivAt)
  rw [hev.fderiv_eq, hD.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  abel

namespace SymplecticGeometry

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {U : Set E}

/-- **Transposing a first-order term.** For `B`, `C¹` on an open set `U`, `w`, `C¹` on `U`, and `a`,
`C¹` with compact support in `U`, `∫ w (B ∂_u a) = ∫ (-(∂_u w) ∘ B - w ∘ ∂_u B) a`. -/
private theorem integral_apply_apply_fderiv (hU : IsOpen U) {B : E → F →L[ℝ] F}
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
private theorem integral_apply_smul_fderiv_fderiv (hU : IsOpen U) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) {w : E → F →L[ℝ] ℝ} (hw : ContDiffOn ℝ 2 w U) {a : E → F}
    (ha : ContDiff ℝ 2 a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) (u u' : E) :
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
operator on maps `E → F` with scalar coefficients `Aᵢⱼ` and coefficients `Bᵢ`, `C` in
`F →L[ℝ] F`, all smooth on `U`. Then there are `B'ᵢ` and `C'` in `F →L[ℝ] F`, smooth on
`U`, such that the operator `P' w = ∑ᵢⱼ Aᵢⱼ ∂_{v_j} ∂_{v_i} w + ∑ᵢ (∂_{v_i} w) ∘ B'ᵢ + w ∘ C'` on
maps `E → F →L[ℝ] ℝ` satisfies `∫ w (P a) dμ = ∫ (P' w) a dμ` for every `w` that is `C²` on `U`
and every `a` that is `C²` with compact support in `U`. -/
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
  -- Directional derivatives of the coefficients.
  set dA : ι → ι → E → ℝ := fun i j y ↦ fderiv ℝ (A i j) y (v j)
  set ddA : ι → ι → E → ℝ := fun i j y ↦ fderiv ℝ (fun z ↦ fderiv ℝ (A i j) z (v j)) y (v i)
  set dB : ι → E → F →L[ℝ] F := fun i y ↦ fderiv ℝ (B i) y (v i)
  have hdA (i j : ι) : ContDiffOn ℝ ∞ (dA i j) U :=
    (hA i j).fderiv_apply_of_isOpen hU (by simp) (v j)
  have hddA (i j : ι) : ContDiffOn ℝ ∞ (ddA i j) U :=
    ((hA i j).fderiv_apply_of_isOpen hU (m := ∞) (by simp) (v j)).fderiv_apply_of_isOpen hU
      (by simp) (v i)
  have hdB (i : ι) : ContDiffOn ℝ ∞ (dB i) U := (hB i).fderiv_apply_of_isOpen hU (by simp) (v i)
  -- `lsmul t` is multiplication by the scalar `t`.
  set lsm := ContinuousLinearMap.lsmul ℝ ℝ (E := F)
  refine ⟨fun i y ↦ lsm (∑ j, dA i j y + ∑ j, fderiv ℝ (A j i) y (v j)) - B i y,
    fun y ↦ lsm (∑ i, ∑ j, ddA i j y) - ∑ i, dB i y + C y, fun i ↦ ?_, ?_,
    fun w a hw ha hac haU ↦ ?_⟩
  · exact (contDiffOn_const.clm_apply ((ContDiffOn.sum fun j _ ↦ hdA i j).add
      (ContDiffOn.sum fun j _ ↦ (hA j i).fderiv_apply_of_isOpen hU (by simp) (v j)))).sub (hB i)
  · exact ((contDiffOn_const.clm_apply (ContDiffOn.sum fun i _ ↦ ContDiffOn.sum fun j _ ↦
      hddA i j)).sub (ContDiffOn.sum fun i _ ↦ hdB i)).add hC
  have hwU (y : E) (hy : y ∈ U) : ContDiffAt ℝ 2 w y := hw.contDiffAt (hU.mem_nhds hy)
  have hw1 (u : E) : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ w y u) U :=
    hw.fderiv_apply_of_isOpen hU (by norm_num) u
  have hda (u : E) : ContDiff ℝ 1 fun z ↦ fderiv ℝ a z u :=
    (ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdda (u u' : E) : Continuous fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u' :=
    ((hda u).continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- Outside the support of `a`, `a` and its first two derivatives vanish.
  have h0 (y : E) (hy : y ∉ tsupport a) : a y = 0 := image_eq_zero_of_notMem_tsupport hy
  have h1 (y : E) (hy : y ∉ tsupport a) (u : E) : fderiv ℝ a y u = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ hy]
  have h2 (y : E) (hy : y ∉ tsupport a) (u u' : E) :
      fderiv ℝ (fun z ↦ fderiv ℝ a z u) y u' = 0 := by
    simp [fderiv_of_notMem_tsupport ℝ fun h ↦ hy (tsupport_fderiv_apply_subset ℝ u h)]
  -- A function continuous on `U` and vanishing outside the support of `a` is integrable.
  have int (h : E → ℝ) (hh : ContinuousOn h U) (hz : ∀ y ∉ tsupport a, h y = 0) :
      Integrable h μ := by
    have hs : tsupport h ⊆ tsupport a :=
      closure_minimal (fun y hy ↦ by_contra fun hn ↦ hy (hz y hn)) (isClosed_tsupport a)
    exact (hh.continuous_of_tsupport_subset hU (hs.trans haU)).integrable_of_hasCompactSupport
      (hac.mono' (subset_closure.trans hs))
  -- The integral of a sum of the shape of `P` splits into the integrals of its terms.
  have split (f₂ : ι → ι → E → ℝ) (f₁ : ι → E → ℝ) (f₀ : E → ℝ)
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
  -- The pieces of `w (P a)`, and the pieces of `(P' w) a` that they integrate to.
  have hA2 (i j : ι) : ContDiffOn ℝ 2 (A i j) U := (hA i j).of_le (by simp)
  have hAw (i j : ι) : ContDiffOn ℝ 2 (fun y ↦ A i j y • w y) U := (hA2 i j).smul hw
  rw [integral_congr_ae (g := fun y ↦ ∑ i, ∑ j, w y (A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z
      (v i)) y (v j)) + ∑ i, w y (B i y (fderiv ℝ a y (v i))) + w y (C y (a y)))
      (Filter.Eventually.of_forall fun y ↦ by simp only [map_add, map_sum])]
  rw [split (fun i j y ↦ w y (A i j y • fderiv ℝ (fun z ↦ fderiv ℝ a z (v i)) y (v j)))
    (fun i y ↦ w y (B i y (fderiv ℝ a y (v i)))) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ int _ (hw.continuousOn.clm_apply ((hA i j).continuousOn.smul
      (hdda _ _).continuousOn)) fun y hy ↦ by simp [h2 y hy])
    (fun i ↦ int _ (hw.continuousOn.clm_apply ((hB i).continuousOn.clm_apply
      ((ha.continuous_fderiv two_ne_zero).clm_apply continuous_const).continuousOn))
      fun y hy ↦ by simp [h1 y hy])
    (int _ (hw.continuousOn.clm_apply (hC.continuousOn.clm_apply ha.continuous.continuousOn))
      fun y hy ↦ by simp [h0 y hy])]
  simp only [integral_apply_smul_fderiv_fderiv (μ := μ) hU (hA2 _ _) hw ha hac haU,
    integral_apply_apply_fderiv (μ := μ) hU ((hB _).of_le (by simp)) (hw.of_le (by norm_num))
      (ha.of_le (by norm_num)) hac haU]
  rw [← split
    (fun i j y ↦ fderiv ℝ (fun z ↦ fderiv ℝ (fun z ↦ A i j z • w z) z (v j)) y (v i) (a y))
    (fun i y ↦ (-((fderiv ℝ w y (v i)).comp (B i y) + (w y).comp (fderiv ℝ (B i) y (v i))))
      (a y)) (fun y ↦ w y (C y (a y)))
    (fun i j ↦ int _ ((((hAw i j).fderiv_apply_of_isOpen hU (m := 1) (by norm_num)
      (v j)).fderiv_apply_of_isOpen hU (m := 0) (by norm_num) (v i)).continuousOn.clm_apply
      ha.continuous.continuousOn) fun y hy ↦ by simp [h0 y hy])
    (fun i ↦ int _ ((((hw1 (v i)).continuousOn.clm_comp (hB i).continuousOn).add
      (hw.continuousOn.clm_comp ((hB i).fderiv_apply_of_isOpen hU (m := 0) (by simp)
        (v i)).continuousOn)).neg.clm_apply ha.continuous.continuousOn)
      fun y hy ↦ by simp [h0 y hy])
    (int _ (hw.continuousOn.clm_apply (hC.continuousOn.clm_apply ha.continuous.continuousOn))
      fun y hy ↦ by simp [h0 y hy])]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  by_cases hy : y ∈ tsupport a
  swap
  · simp [h0 y hy]
  have hyU := hU.mem_nhds (haU hy)
  have hc (u u' : E) := TauCeti.fderiv_fderiv_apply_comm (hwU y (haU hy)) (n := 2) (by simp) u u'
  beta_reduce
  simp only [fderiv_fderiv_smul_apply ((hA2 _ _).contDiffAt hyU) (hwU y (haU hy)),
    add_apply, sum_apply, neg_apply, smul_apply, sub_apply, map_add, map_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply, map_sub, map_smul, lsm, dA,
    ddA, dB,
    Finset.sum_add_distrib, smul_eq_mul]
  rw [Finset.sum_comm (f := fun i j ↦ fderiv ℝ (A i j) y (v i) * fderiv ℝ w y (v j) (a y))]
  simp only [hc, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end SymplecticGeometry
