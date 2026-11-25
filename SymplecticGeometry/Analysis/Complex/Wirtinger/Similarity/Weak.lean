/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weak
import TauCeti.Analysis.Complex.Wirtinger.Potential
import TauCeti.Analysis.Complex.Wirtinger.Weyl
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The weak similarity principle in the plane

A locally integrable function `u` solving `∂̄u = a u` in the sense of distributions, with a
coefficient `a` smooth on an open set `Ω`, is near each point of `Ω` almost everywhere equal to
`exp (-g) h`, with `g` smooth on the plane and `h` holomorphic. In particular it agrees almost
everywhere near each point with a smooth function. This is the distributional counterpart of
`TauCeti.exists_contDiff_analyticAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul`, which
asks `u` to be real differentiable.

## Main results

* `TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_smul`: the Leibniz rule
  `∂̄(c u) = c ∂̄u + (∂̄c) u` for a weak solution `u` and a complex factor `c` smooth on `Ω`.
* `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiff_differentiableOn_ae_eq_exp_neg_mul`:
  the weak similarity principle.
* `TauCeti.HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_eq_mul`: a weak solution of
  `∂̄u = a u` is almost everywhere smooth near each point.

The Leibniz rule follows the proof of Tau Ceti's `TauCeti.HasWeakLineDerivOn.contDiffOn_smul`
(`TauCeti/Analysis/Sobolev/Leibniz.lean`): the product of a test function and a factor smooth on
`Ω` is a test function. Since the tests of `TauCeti.HasWeakConjWirtingerDerivOn` are real, the
rule is first proved for a real factor and then applied to the real and imaginary parts of `c`.
The similarity principle takes `g` with `∂̄g = -a` near the point from
`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq`; then `∂̄(exp g u) = 0`
weakly, and Weyl's lemma `TauCeti.HasWeakConjWirtingerDerivOn.exists_differentiableOn_ae_eq`
gives `h`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix B.
* I. N. Vekua, *Generalized Analytic Functions*, Chapter I.
-/

public section

open Complex MeasureTheory TopologicalSpace Filter Topology
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
section Similarity

variable [μ.IsAddHaarMeasure] {a u : ℂ → ℂ}

/-- **The weak similarity principle.** Let `u` solve `∂̄u = a u` weakly on `Ω`, with `a` smooth
on `Ω`. Near each point `z` of `Ω` there are a smooth `g` on the plane and an open neighbourhood
`V` of `z` in `Ω` with `∂̄g = -a` on `V`, and a function `h` holomorphic on `V` such that
`u = exp (-g) h` almost everywhere on `V`. -/
theorem HasWeakConjWirtingerDerivOn.exists_contDiff_differentiableOn_ae_eq_exp_neg_mul
    (hu : HasWeakConjWirtingerDerivOn μ Ω u (fun z ↦ a z * u z)) (ha : ContDiffOn ℝ ∞ a Ω)
    {z : ℂ} (hz : z ∈ Ω) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ ∃ V : Opens ℂ, z ∈ V ∧ V ≤ Ω ∧
      (∀ w ∈ V, conjWirtingerDeriv g w 1 = -a w) ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h V ∧ u =ᵐ[μ.restrict V] fun w ↦ exp (-g w) * h w := by
  obtain ⟨g, hg, hga⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq (n := ⊤) le_top Ω.isOpen ha.neg hz
  obtain ⟨t, hgt, ht, hzt⟩ := eventually_nhds_iff.1 hga
  let V : Opens ℂ := ⟨t, ht⟩ ⊓ Ω
  have hVΩ : V ≤ Ω := inf_le_right
  have hexp : ContDiff ℝ ∞ (fun w ↦ exp (g w)) := hg.cexp
  -- `exp g • u` solves `∂̄ = 0` weakly on `V`.
  have h0 : HasWeakConjWirtingerDerivOn μ V (fun w ↦ exp (g w) • u w) 0 := by
    refine ((hu.mono hVΩ).contDiffOn_smul hexp.contDiffOn).congr_ae_deriv ?_
    rw [EventuallyEq, ae_restrict_iff' V.isOpen.measurableSet]
    refine Eventually.of_forall fun w hw ↦ ?_
    have hgw : DifferentiableAt ℝ g w := hg.differentiable (by simp) w
    have hd : conjWirtingerDeriv (fun w ↦ exp (g w)) w 1 = exp (g w) * -a w := by
      rw [← Function.comp_def exp g,
        conjWirtingerDeriv_comp differentiableAt_exp hgw,
        ContinuousLinearMap.comp_apply, hgt w hw.1, (hasDerivAt_exp (g w)).hasFDerivAt.fderiv]
      simp [mul_comm]
    simp only [hd, smul_eq_mul, Pi.zero_apply]
    ring
  obtain ⟨h, hh, hae⟩ := h0.exists_differentiableOn_ae_eq
  refine ⟨g, hg, V, ⟨hzt, hz⟩, hVΩ, fun w hw ↦ hgt w hw.1, h, hh, hae.mono fun w hw ↦ ?_⟩
  simp only [← hw, smul_eq_mul, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/-- A weak solution of `∂̄u = a u` on `Ω`, with `a` smooth on `Ω`, agrees almost everywhere near
each point of `Ω` with a smooth function: there are an open neighbourhood `V` of the point in `Ω`
and a function smooth on `V` equal to `u` almost everywhere on `V`. -/
theorem HasWeakConjWirtingerDerivOn.exists_contDiffOn_ae_eq_of_mul_self
    (hu : HasWeakConjWirtingerDerivOn μ Ω u (fun z ↦ a z * u z)) (ha : ContDiffOn ℝ ∞ a Ω)
    {z : ℂ} (hz : z ∈ Ω) :
    ∃ V : Opens ℂ, z ∈ V ∧ V ≤ Ω ∧ ∃ v : ℂ → ℂ, ContDiffOn ℝ ∞ v V ∧ u =ᵐ[μ.restrict V] v := by
  obtain ⟨g, hg, V, hzV, hVΩ, -, h, hh, hae⟩ :=
    hu.exists_contDiff_differentiableOn_ae_eq_exp_neg_mul ha hz
  exact ⟨V, hzV, hVΩ, _,
    hg.neg.cexp.contDiffOn.mul ((hh.contDiffOn V.isOpen).restrict_scalars ℝ), hae⟩

end Similarity

end TauCeti
