/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Localization.Real
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import SymplecticGeometry.Probability.Moments.ComplexMGF
import SymplecticGeometry.Topology.Algebra.ConstMulAction

/-!
# Duistermaat–Heckman localization

Let the circle act on a compact boundaryless symplectic manifold `(M, σ)` of dimension `2 n`,
preserving `σ`, with a moment map `μ` and isolated fixed points, and let `H = ⟨μ, ξ₁⟩` for the
period-one generator `ξ₁ = circlePeriodOneGenerator`. With weights `k p` of the tangent action
at each fixed point `p` (`SymplecticGeometry.IsTangentWeights`), this file proves, for every
complex `ħ ≠ 0`,
`∫ e^{-ħ H} dλ_σ = ∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħⁿ ∏ⱼ k p j)`, where `λ_σ` is the Liouville
measure, the measure of `σⁿ / n!`.

* `SymplecticGeometry.integral_exp_neg_mul_eq_finsum_of_pos`: the formula for real `ħ > 0`.
  It is `SymplecticGeometry.integralTopForm_exp_neg_mul_eq_finsum_of_pos`, whose left side is the
  integral of the top component `e^{-ħ H} σⁿ / n!` of `e^{σ - ħH}` against the symplectic
  orientation, turned into a Liouville integral by
  `TauCeti.SmoothTwoForm.IsNondegenerate.integralTopForm_smul_volumeForm`.
* `SymplecticGeometry.integral_cexp_neg_mul_eq_finsum_fixedPoints`: the formula for complex
  `ħ ≠ 0`. The left side is `complexMGF H λ_σ (-ħ)`, an entire function of `ħ`, since `H` is
  continuous, hence bounded, and `λ_σ` is finite on the compact space `M`
  (`ProbabilityTheory.analyticOnNhd_complexMGF_of_mem_Icc`); the right side is a finite sum of
  functions analytic on `ℂ ∖ {0}`, which is connected. The two agree on the positive reals, so on
  `ℂ ∖ {0}` (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`).
* `SymplecticGeometry.tendsto_finsum_fixedPoints_liouvilleMeasure`: as `ħ → 0`, `ħ ≠ 0`, the right
  side tends to the total Liouville measure of `M`, the value of the left side at `ħ = 0`; so
  `ħ = 0` is a removable singularity of the sum.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6,
  Theorem 5.6.1 and Remark 5.6.2(i)
* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268
-/

public section

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Manifold ContDiff Topology Real

namespace SymplecticGeometry

open TauCeti

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M]
  [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {n : ℕ} [Fact (Module.finrank ℝ E = 2 * n)] {σ : SmoothTwoForm I M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}

/-- **The Duistermaat–Heckman formula for real `ħ > 0`, against the Liouville measure.** Let the
circle act smoothly on a compact boundaryless manifold `M` of dimension `2 n`, preserving a
symplectic form `σ`, with a moment map `μ` in the sign `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` and isolated fixed
points, and let `H = ⟨μ, ξ₁⟩` for the period-one generator `ξ₁ = circlePeriodOneGenerator`. Let
`k p` be weights of the action at each fixed point `p`, as in
`SymplecticGeometry.IsTangentWeights`. Then for real `ħ > 0`,
`∫ e^{-ħ H} dλ_σ = ∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħ ^ n * ∏ j, k p j)` for the Liouville
measure `λ_σ`. -/
theorem integral_exp_neg_mul_eq_finsum_of_pos (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hiso : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints Circle M)
    (k : M → Fin n → ℤ)
    (hk : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ), IsTangentWeights σ p (k p) L)
    {ħ : ℝ} (hħ : 0 < ħ) :
    ∫ x, Real.exp (-ħ * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n =
      ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
        Real.exp (-ħ * μ p circlePeriodOneGenerator) / (ħ ^ n * ∏ j, (k p j : ℝ)) := by
  have hc : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ μ x circlePeriodOneGenerator := by
    simpa using (hμ.contMDiff circlePeriodOneGenerator).neg
  obtain ⟨H, hH⟩ : ∃ H : C^∞⟮I, M; ℝ⟯, ∀ x, H x = μ x circlePeriodOneGenerator :=
    ⟨⟨_, hc⟩, fun x ↦ by rw [ContMDiffMap.coeFn_mk]⟩
  have h := integralTopForm_exp_neg_mul_eq_finsum_of_pos hσ hinv hμ hiso k hk hH hħ
  simp only [hH] at h
  have hf : Continuous fun x ↦ Real.exp (-ħ * μ x circlePeriodOneGenerator) :=
    Real.continuous_exp.comp (continuous_const.mul hc.continuous)
  rw [← h, ← hσ.isNondegenerate.integralTopForm_smul_volumeForm hf
    (HasCompactSupport.of_compactSpace _)]
  congr 1
  funext x
  rw [formCalculus_apply_val, SmoothTwoForm.volumeForm_apply, smul_smul, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, hH,
    mul_comm ((n.factorial : ℝ)⁻¹)]

/-- **Duistermaat–Heckman localization.** Let the circle act smoothly on a compact boundaryless
manifold `M` of dimension `2 n`, preserving a symplectic form `σ`, with a moment map `μ` in the
sign `d⟨μ, ξ⟩ = -ι_{ξ_M} σ` and isolated fixed points, and let `H = ⟨μ, ξ₁⟩` for the period-one
generator `ξ₁ = circlePeriodOneGenerator`. At each fixed point `p`, let `k p j` be the weights of
the tangent action: a real-linear isomorphism `L : T_p M ≃ ℂⁿ` carries `σ_p` to the standard
symplectic form of `ℂⁿ` and the derivative at `p` of the action of `exp(2π i t)` to
`z ↦ (e^{2π i k p j t} zⱼ)ⱼ`. Then for every complex `ħ ≠ 0`,
`∫ e^{-ħ H} dλ_σ = ∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħ ^ n * ∏ j, k p j)`, where `λ_σ` is the
Liouville measure, the measure of `σⁿ / n!`.

Milestone: *Duistermaat–Heckman localization*. -/
theorem integral_cexp_neg_mul_eq_finsum_fixedPoints (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hiso : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints Circle M)
    (k : M → Fin n → ℤ)
    (hk : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ), IsTangentWeights σ p (k p) L)
    {ħ : ℂ} (hħ : ħ ≠ 0) :
    ∫ x, Complex.exp (-ħ * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n =
      ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
        Complex.exp (-ħ * μ p circlePeriodOneGenerator) / (ħ ^ n * ∏ j, (k p j : ℂ)) := by
  classical
  have hc : Continuous fun x ↦ μ x circlePeriodOneGenerator := by
    simpa using (hμ.contMDiff circlePeriodOneGenerator).continuous.neg
  have : ContinuousConstSMul Circle M :=
    ⟨fun g ↦ (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) (n := ∞) g).continuous⟩
  have hS := finite_fixedPoints hiso
  -- The left side is `complexMGF H λ_σ (-ħ)`, an entire function of `ħ`.
  obtain ⟨a, ha⟩ := (isCompact_range hc).bddBelow
  obtain ⟨b, hb⟩ := (isCompact_range hc).bddAbove
  have hA := analyticOnNhd_complexMGF_of_mem_Icc (μ := σ.liouvilleMeasure n) hc.aemeasurable
    (ae_of_all _ fun x ↦ ⟨ha ⟨x, rfl⟩, hb ⟨x, rfl⟩⟩)
  have hL : AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ x, Complex.exp (-z * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n) {0}ᶜ :=
    fun z _ ↦ by
      simpa only [complexMGF, Function.comp_def, neg_mul] using
        (hA (-z) trivial).comp analyticAt_id.neg
  -- The right side is a finite sum of functions analytic away from `0`.
  have hR : AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
      Complex.exp (-z * μ p circlePeriodOneGenerator) / (z ^ n * ∏ j, (k p j : ℂ))) {0}ᶜ := by
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hS]
    convert Finset.analyticOnNhd_sum hS.toFinset (fun p _ z hz ↦ ?_) using 1
    · ext z
      rw [Finset.sum_apply]
    by_cases hp : ∏ j, (k p j : ℂ) = 0
    · simp only [hp, mul_zero, div_zero]
      exact analyticAt_const
    · exact (analyticAt_id.neg.mul analyticAt_const).cexp'.div
        ((analyticAt_id.pow n).mul analyticAt_const) (mul_ne_zero (pow_ne_zero _ hz) hp)
  -- The two sides agree on the positive reals, by the formula for real `ħ > 0`.
  have hpos (t : ℝ) (ht : 0 < t) :
      ∫ x, Complex.exp (-(t : ℂ) * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n =
        ∑ᶠ p ∈ MulAction.fixedPoints Circle M, Complex.exp (-(t : ℂ) *
          μ p circlePeriodOneGenerator) / ((t : ℂ) ^ n * ∏ j, (k p j : ℂ)) := by
    have h := integral_exp_neg_mul_eq_finsum_of_pos hσ hinv hμ hiso k hk ht
    rw [finsum_mem_eq_finite_toFinset_sum _ hS] at h ⊢
    have h' := congrArg (fun r : ℝ ↦ (r : ℂ)) h
    rw [← integral_complex_ofReal] at h'
    push_cast at h'
    exact h'
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      ∫ x, Complex.exp (-z * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n =
        ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
          Complex.exp (-z * μ p circlePeriodOneGenerator) / (z ^ n * ∏ j, (k p j : ℂ)) := by
    have hmap : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 1) (𝓝[≠] 1) :=
      Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun t ht h ↦
        ht (by simpa using h)
    refine hmap.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds one_pos)] with t ht
    exact hpos t ht
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hL hR
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) 0).isPreconnected (by simp) hfreq hħ

/-- **The value of Duistermaat–Heckman localization at `ħ = 0`.** Under the hypotheses of
`SymplecticGeometry.integral_cexp_neg_mul_eq_finsum_fixedPoints`, the sum
`∑ᶠ p ∈ fixedPoints, e^{-ħ H(p)} / (ħ ^ n * ∏ j, k p j)` tends, as `ħ → 0` with `ħ ≠ 0`, to the
symplectic volume of `M`, its total Liouville measure: the singularity at `ħ = 0` is removable.

Milestone: *Duistermaat–Heckman localization*. -/
theorem tendsto_finsum_fixedPoints_liouvilleMeasure (hσ : σ.IsSymplectic)
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) g) σ = σ)
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) fun x ↦ -μ x)
    (hiso : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∀ᶠ x in 𝓝[≠] p, x ∉ MulAction.fixedPoints Circle M)
    (k : M → Fin n → ℤ)
    (hk : ∀ p ∈ MulAction.fixedPoints Circle M,
      ∃ L : TangentSpace I p ≃L[ℝ] (Fin n → ℂ), IsTangentWeights σ p (k p) L) :
    Tendsto (fun ħ : ℂ ↦ ∑ᶠ p ∈ MulAction.fixedPoints Circle M,
        Complex.exp (-ħ * μ p circlePeriodOneGenerator) / (ħ ^ n * ∏ j, (k p j : ℂ)))
      (𝓝[≠] 0) (𝓝 ((σ.liouvilleMeasure n univ).toReal : ℂ)) := by
  have hc : Continuous fun x ↦ μ x circlePeriodOneGenerator := by
    simpa using (hμ.contMDiff circlePeriodOneGenerator).continuous.neg
  -- The left side `complexMGF H λ_σ (-ħ)` is continuous at `0`, with value the total measure.
  obtain ⟨a, ha⟩ := (isCompact_range hc).bddBelow
  obtain ⟨b, hb⟩ := (isCompact_range hc).bddAbove
  have hA := analyticOnNhd_complexMGF_of_mem_Icc (μ := σ.liouvilleMeasure n) hc.aemeasurable
    (ae_of_all _ fun x ↦ ⟨ha ⟨x, rfl⟩, hb ⟨x, rfl⟩⟩)
  have hL : ContinuousAt (fun z : ℂ ↦
      ∫ x, Complex.exp (-z * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n) 0 := by
    simpa only [complexMGF, Function.comp_def, neg_mul] using
      ((hA (-0) trivial).comp analyticAt_id.neg).continuousAt
  have h0 : ∫ x, Complex.exp (-0 * μ x circlePeriodOneGenerator) ∂σ.liouvilleMeasure n =
      ((σ.liouvilleMeasure n univ).toReal : ℂ) := by
    simp [measureReal_def]
  have hL' := hL.tendsto
  rw [h0] at hL'
  refine (hL'.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact integral_cexp_neg_mul_eq_finsum_fixedPoints hσ hinv hμ hiso k hk hz

end SymplecticGeometry

end
