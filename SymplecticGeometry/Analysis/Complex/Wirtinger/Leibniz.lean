/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weak
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Leibniz rule for the weak `∂̄` with a smooth factor

If `∂̄u = f` in the sense of distributions on an open set `Ω ⊆ ℂ` and `c` is smooth on `Ω`, then
`∂̄(c u) = c f + (∂̄c) u` in the sense of distributions on `Ω`. Only local integrability of `u` is
used; Tau Ceti's `TauCeti.HasWeakConjWirtingerDerivOn.clm_apply`
(`TauCeti/Analysis/Complex/Wirtinger/Leibniz.lean`) asks instead that both factors be continuous.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_smul`: the Leibniz rule
  `∂̄(c u) = c ∂̄u + (∂̄c) u` for a weak solution `u` and a complex factor `c` smooth on `Ω`.

The proof follows that of Tau Ceti's `TauCeti.HasWeakLineDerivOn.contDiffOn_smul`
(`TauCeti/Analysis/Sobolev/Leibniz.lean`): the product of a test function and a factor smooth on
`Ω` is a test function. Since the tests of `TauCeti.HasWeakConjWirtingerDerivOn` are real, the
rule is first proved for a real factor and then applied to the real and imaginary parts of `c`.
-/

public section

open Complex MeasureTheory TopologicalSpace Filter
open scoped ContDiff Distributions

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure ℂ} {Ω : Opens ℂ} {u f : ℂ → F}

/-- The Leibniz rule for a real factor `ψ` smooth on `Ω`, with `∂̄ψ` written through the real
derivative of `ψ`. -/
private theorem HasWeakConjWirtingerDerivOn.contDiffOn_real_smul
    (h : HasWeakConjWirtingerDerivOn μ Ω u f) {ψ : ℂ → ℝ} (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    HasWeakConjWirtingerDerivOn μ Ω (fun z ↦ ψ z • u z)
      (fun z ↦ ψ z • f z + (2 : ℂ)⁻¹ • (fderiv ℝ ψ z 1 • u z + I • fderiv ℝ ψ z I • u z)) := by
  have hdψ (w : ℂ) : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ ψ z w) Ω :=
    (hψ.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const
  have hu := h.locallyIntegrableOn
  have hf := h.locallyIntegrableOn_deriv
  refine hasWeakConjWirtingerDerivOn_iff.2 ⟨h.completeSpace,
    hu.continuousOn_smul_of_isOpen Ω.isOpen hψ.continuousOn,
    (hf.continuousOn_smul_of_isOpen Ω.isOpen hψ.continuousOn).add
      (((hu.continuousOn_smul_of_isOpen Ω.isOpen (hdψ 1).continuousOn).add
        ((hu.continuousOn_smul_of_isOpen Ω.isOpen (hdψ I).continuousOn).smul I)).smul _),
    fun φ ↦ ?_⟩
  -- `ψ φ` and `(∂_w ψ) φ` are test functions on `Ω`.
  obtain ⟨Φ, hΦ⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hψ φ
  obtain ⟨Ψ₁, hΨ₁⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn (hdψ 1) φ
  obtain ⟨Ψ₂, hΨ₂⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn (hdψ I) φ
  have hline (w : ℂ) (x : ℂ) : lineDeriv ℝ (Φ : ℂ → ℝ) x w =
      ψ x * lineDeriv ℝ (φ : ℂ → ℝ) x w + fderiv ℝ ψ x w * φ x := by
    rw [hΦ, TestFunction.lineDeriv_fun_smul_of_differentiableOn
      (hψ.differentiableOn (by simp)) φ x w]
    simp only [smul_eq_mul]
  have hside (w : ℂ) (Ψ : 𝓓(Ω, ℝ)) (hΨ : ⇑Ψ = fun x ↦ fderiv ℝ ψ x w • φ x) :
      ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z w • (ψ z • u z) ∂μ =
        ∫ z, lineDeriv ℝ (Φ : ℂ → ℝ) z w • u z ∂μ - ∫ z, (Ψ : ℂ → ℝ) z • u z ∂μ := by
    rw [← integral_sub (integrable_lineDeriv_smul_of_locallyIntegrableOn hu Φ w)
      (Ψ.integrable_smul hu)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hline, hΨ, smul_eq_mul, add_smul, smul_smul, add_sub_cancel_right, mul_comm]
  have hint₁ := Φ.integrable_smul hf
  have hint₂ := Ψ₁.integrable_smul hu
  have hint₃ := Ψ₂.integrable_smul hu
  have hrhs : ∫ z, (φ : ℂ → ℝ) z • (ψ z • f z +
        (2 : ℂ)⁻¹ • (fderiv ℝ ψ z 1 • u z + I • fderiv ℝ ψ z I • u z)) ∂μ =
      ∫ z, (Φ : ℂ → ℝ) z • f z ∂μ + (2 : ℂ)⁻¹ •
        ((∫ z, (Ψ₁ : ℂ → ℝ) z • u z ∂μ) + I • ∫ z, (Ψ₂ : ℂ → ℝ) z • u z ∂μ) := by
    calc _ = ∫ z, ((Φ : ℂ → ℝ) z • f z + (2 : ℂ)⁻¹ •
          ((Ψ₁ : ℂ → ℝ) z • u z + I • (Ψ₂ : ℂ → ℝ) z • u z)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only [hΦ, hΨ₁, hΨ₂, smul_eq_mul, mul_smul]
          module
      _ = _ := by
          have hint₄ : Integrable (fun z ↦ I • (Ψ₂ : ℂ → ℝ) z • u z) μ := hint₃.smul I
          have hint₅ : Integrable (fun z ↦ (2 : ℂ)⁻¹ •
              ((Ψ₁ : ℂ → ℝ) z • u z + I • (Ψ₂ : ℂ → ℝ) z • u z)) μ :=
            (hint₂.add hint₄).smul _
          rw [integral_add hint₁ hint₅, integral_smul, integral_add hint₂ hint₄, integral_smul]
  rw [hside 1 Ψ₁ hΨ₁, hside I Ψ₂ hΨ₂, hrhs]
  linear_combination (norm := module)
    h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul Φ

/-- **The Leibniz rule for the weak `∂̄`.** If `∂̄u = f` weakly on `Ω` and `c` is smooth on `Ω`,
then `∂̄(c u) = c f + (∂̄c) u` weakly on `Ω`. No regularity of `u` beyond local integrability is
needed. -/
theorem HasWeakConjWirtingerDerivOn.contDiffOn_smul (h : HasWeakConjWirtingerDerivOn μ Ω u f)
    {c : ℂ → ℂ} (hc : ContDiffOn ℝ ∞ c Ω) :
    HasWeakConjWirtingerDerivOn μ Ω (fun z ↦ c z • u z)
      (fun z ↦ c z • f z + conjWirtingerDeriv c z 1 • u z) := by
  have hre : ContDiffOn ℝ ∞ (fun z ↦ (c z).re) Ω := reCLM.contDiff.comp_contDiffOn hc
  have him : ContDiffOn ℝ ∞ (fun z ↦ (c z).im) Ω := imCLM.contDiff.comp_contDiffOn hc
  have hsum := (h.contDiffOn_real_smul hre).add ((h.contDiffOn_real_smul him).const_smul I)
  refine (hsum.congr_ae (Eventually.of_forall fun z ↦ ?_)).congr_ae_deriv ?_
  · simp only [Pi.add_apply, Pi.smul_apply]
    conv_rhs => rw [← re_add_im (c z)]
    rw [add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul, smul_comm I]
  · rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    refine Eventually.of_forall fun z hz ↦ ?_
    have hcz : DifferentiableAt ℝ c z :=
      (hc.differentiableOn (by simp)).differentiableAt (Ω.isOpen.mem_nhds hz)
    have hD (w : ℂ) : fderiv ℝ c z w =
        ((fderiv ℝ (fun z ↦ (c z).re) z w : ℝ) : ℂ) +
          ((fderiv ℝ (fun z ↦ (c z).im) z w : ℝ) : ℂ) * I := by
      have hre' : HasFDerivAt (fun z ↦ (c z).re) (reCLM.comp (fderiv ℝ c z)) z :=
        reCLM.hasFDerivAt.comp z hcz.hasFDerivAt
      have him' : HasFDerivAt (fun z ↦ (c z).im) (imCLM.comp (fderiv ℝ c z)) z :=
        imCLM.hasFDerivAt.comp z hcz.hasFDerivAt
      rw [hre'.fderiv, him'.fderiv]
      simp
    simp only [Pi.add_apply, Pi.smul_apply, conjWirtingerDeriv_apply, smul_eq_mul, mul_one,
      hD 1, hD I]
    conv_rhs => rw [← re_add_im (c z)]
    simp only [← Complex.coe_smul]
    module

end TauCeti

end
