/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import SymplecticGeometry.Analysis.SpecialFunctions.Pow.Asymptotics
import SymplecticGeometry.Geometry.Manifold.Morse.ComplexIndex
import SymplecticGeometry.Geometry.Manifold.Morse.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Metric
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartHessian
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Critical points of `log |s_k|²` for uniformly transverse sequences

Let `s` be an asymptotically holomorphic sequence of sections of the powers `PowerBundle P k`
which is uniformly transverse with constant `η` (`SymplecticGeometry.IsUniformlyTransverse`).
Then, for `k` large, at every point `x` where `s k` is differentiable, does not vanish, and is a
critical point of `y ↦ log ‖s k y‖ ^ 2` (Tau Ceti's `TauCeti.criticalPoints`), the norm of
`s k x` is at least `η`
(`SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`).

At such a point the `(1,0)`-part and the `(0,1)`-part of `powerConnection α k (s k) x` have equal
operator norms, since the connection is metric and the fibres are complex lines
(`CovariantDerivative.IsMetricCompatible.norm_oneZeroPart_eq_norm_zeroOnePart_of_log`). The
rescaled `(0,1)`-part is `O(k ^ (-1/2))` uniformly
(`SymplecticGeometry.RescaledUnitaryCharts.exists_rpow_mul_norm_zeroOnePart_powerConnection_le`),
so for `k` large the derivative term of `IsUniformlyTransverse` is below `η`, and the maximum
there is attained by `‖s k x‖`.

On a boundaryless manifold and for `η > 0`, this gives the second step: for `k` large, at such
a point the critical Hessian of `f = log ‖s k‖²` satisfies `Hess f (v, v) + Hess f (J v, J v) < 0`
for every nonzero tangent vector `v`
(`SymplecticGeometry.IsUniformlyTransverse.criticalHessian_add_criticalHessian_neg`). In the chart
centred at `x`, the reading `F` of `s k` has `|F 0| ≥ η` and a bounded first derivative, while its
`∂̄` reading, with its first derivative, and the derivative of the pushed-forward almost complex
structure are `O(k ^ (-1/2))`. So the chart estimate
`SymplecticGeometry.fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le` bounds the sum by a
negative multiple of the square norm. The critical Hessian is carried to the chart by
`PartialDiffeomorph.criticalHessian_apply_eq_fderiv_fderiv`, and the derivative of the chart
carries `J` at `x` to the standard structure. The Morse index of `f` at `x` is then at least
half the dimension of `M`
(`SymplecticGeometry.IsUniformlyTransverse.finrank_div_two_le_manifoldMorseIndex`), by
`TauCeti.SmoothAlmostComplexStructure.finrank_div_two_le_manifoldMorseIndex`.

These are the first steps of the Morse theory of `log |s_k|²` away from the zero set.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  Proposition 2 and §5.1
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
-/

public section

open scoped Manifold ContDiff
open TauCeti Bundle

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, Nonempty (P x)] [∀ x, MulAction Circleᵐᵒᵖ (P x)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}


/-- **Uniformly transverse sequences have norm at least `η` at the critical points of
`log |s_k|²`.** Let `M` be compact, with a continuous Riemannian metric, `σ` compatible with `J`,
`α` a connection form, and `D` rescaled unitary charts of radius `ρ₀ > 0`. If `s` is
asymptotically holomorphic for `D` and uniformly transverse with constant `η`, then for `k`
large, at every point `x` where `s k` is differentiable and does not vanish and which is a
critical point of `y ↦ log (‖s k y‖ ^ 2)`, we have `η ≤ ‖s k x‖`. -/
theorem IsUniformlyTransverse.le_norm_of_mem_criticalPoints
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ}
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, PowerModel k))
        (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y)) x → s k x ≠ 0 →
      x ∈ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2)) → η ≤ ‖s k x‖ := by
  rcases le_or_gt η 0 with hη | hη
  · exact Filter.Eventually.of_forall fun k x _ _ _ ↦ hη.trans (norm_nonneg _)
  obtain ⟨C, hC⟩ := D.exists_rpow_mul_norm_zeroOnePart_powerConnection_le hJ hα hρ₀ hs
  have hsmall := Real.eventually_mul_rpow_neg_half_lt C hη
  filter_upwards [isUniformlyTransverse_def.1 ht, hC, hsmall] with k hk hCk hsk x hdiff hx hcrit
  have heq := (isMetricCompatible_powerConnection α k).norm_oneZeroPart_eq_norm_zeroOnePart_of_log
    J (PowerBundle.finrank_eq_one P k x) hdiff hx (mem_criticalPoints.1 hcrit)
  have hlt : (2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart (powerConnection α k (s k) x)‖ <
      η := by
    rw [heq]
    exact (hCk x).trans_lt hsk
  rcases le_max_iff.1 (hk x) with h | h
  · exact h
  · exact absurd h hlt.not_ge

omit [FiniteDimensional ℝ E] [CompactSpace M] [∀ x, Nonempty (P x)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- At a critical point `x` of `log ‖s‖²` where `s x ≠ 0` and the reading `F` of `s` in the chart
centred at `x` is `C²` at `0`, the sum of the critical Hessians in the directions `v` and `J v` is
the sum of the second derivatives of `log ‖F‖²` at `0` in the directions `u` and `J₀ u`, for `u`
the image of `v` under the derivative of the chart. -/
private theorem criticalHessian_add_criticalHessian_eq [I.Boundaryless]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) {k : ℕ} (hk : k₀ ≤ k) {x : M}
    {s : Π y, PowerBundle P k y} (hF : ContDiffAt ℝ 2 (D.reading k x s) 0) (hx : s x ≠ 0)
    (hcrit : x ∈ criticalPoints I (fun y ↦ Real.log (‖s y‖ ^ 2))) (v : TangentSpace I x) :
    criticalHessian I (fun y ↦ Real.log (‖s y‖ ^ 2)) x v v +
        criticalHessian I (fun y ↦ Real.log (‖s y‖ ^ 2)) x (J x v) (J x v) =
      fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖D.reading k x s z‖ ^ 2)) 0
          (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v)
          (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v) +
        fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖D.reading k x s z‖ ^ 2)) 0
          (stdComplexStructure ι (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v))
          (stdComplexStructure ι (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v)) := by
  set f : M → ℝ := fun y ↦ Real.log (‖s y‖ ^ 2)
  set g : StdSpace ι → ℝ := fun z ↦ Real.log (‖D.reading k x s z‖ ^ 2)
  have hx0 : D.chart k x x = 0 := D.apply_self hk x
  have hsrc : x ∈ (D.chart k x).source := D.mem_source hk x
  have hfg : f ∘ (D.chart k x).symm = g := funext fun z ↦ by
    simp only [f, g, Function.comp_apply, D.norm_reading]
  have hF0 : D.reading k x s 0 ≠ 0 := by
    rw [← norm_ne_zero_iff, D.norm_reading, D.chart_symm_zero hk x]
    exact norm_ne_zero_iff.2 hx
  have hg : ContDiffAt ℝ 2 (f ∘ (D.chart k x).symm) (D.chart k x x) := by
    rw [hfg, hx0]
    exact (Real.contDiffAt_log.2 (by positivity)).comp _ (hF.norm_sq ℝ)
  have hH (w : TangentSpace I x) :
      criticalHessian I f x w w = fderiv ℝ (fderiv ℝ g) 0
        (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x w)
        (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x w) := by
    rw [(D.chart k x).criticalHessian_apply_eq_fderiv_fderiv (by simp) hsrc hg hcrit, hfg, hx0]
  have hJv : stdComplexStructure ι (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v) =
      mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x (J x v) := by
    refine (D.chartPushforward_zero hk x _).symm.trans (Eq.trans (α := StdSpace ι) ?_
      (J.mfderiv_apply_eq_chartPushforward_apply (D.chart k x) hsrc v).symm)
    rw [hx0]
  rw [hH, hH, hJv]

omit [FiniteDimensional ℝ E] [CompactSpace M] [∀ x, Nonempty (P x)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
/-- If the `1`-jet norm of the reading `F` of `s` in the chart centred at `x` is at most `C`, that
of its `∂̄` reading `G` at most `C * k ^ (-1/2)`, and `η ≤ ‖F 0‖` with `η > 0`, then the error term
of the chart estimate `fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le` is at most
`(C / η + B * C / η + C * C / η ^ 2) * k ^ (-1/2)`, for `B` the bound of order `1` on the
derivative of the pushed-forward almost complex structure. -/
private theorem chartError_le (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hρ₀ : 0 < ρ₀)
    {k : ℕ} (hk : k₀ ≤ k) (hk1 : 1 ≤ k) {x : M} {s : Π y, PowerBundle P k y} {C η : ℝ}
    (hη : 0 < η) (hjet : D.jetNorm k 1 s x ≤ C)
    (hdbar : D.dbarJetNorm k 1 s x ≤ C * (k : ℝ) ^ (-1 / 2 : ℝ))
    (hFη : η ≤ ‖D.reading k x s 0‖) :
    ‖fderiv ℝ (D.dbarReading k x s) 0‖ / ‖D.reading k x s 0‖ +
        ‖fderiv ℝ (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) 0‖ *
          ‖fderiv ℝ (D.reading k x s) 0‖ / ‖D.reading k x s 0‖ +
        ‖D.dbarReading k x s 0‖ * ‖fderiv ℝ (D.reading k x s) 0‖ / ‖D.reading k x s 0‖ ^ 2 ≤
      (C / η + D.bound 1 * C / η + C * C / η ^ 2) * (k : ℝ) ^ (-1 / 2 : ℝ) := by
  set t : ℝ := (k : ℝ) ^ (-1 / 2 : ℝ)
  rw [D.dbarJetNorm_def] at hdbar
  rw [D.jetNorm_def] at hjet
  have hdG := (norm_fderiv_le_jetNormAt le_rfl _ _).trans hdbar
  have hG0 := (norm_le_jetNormAt 1 _ _).trans hdbar
  have hdF := (norm_fderiv_le_jetNormAt le_rfl _ _).trans hjet
  have hball : (0 : StdSpace ι) ∈ Metric.ball 0 (ρ₀ * √k) :=
    Metric.mem_ball_self (by positivity)
  have hJ1 := D.iteratedFDeriv_jStruct_le hk one_ne_zero x 0 hball
  rw [Real.inv_sqrt_eq_rpow] at hJ1
  -- Read off the sign from the iterated form: the norm on the space of bilinear maps that the
  -- form with `fderiv` has takes instance search past its default limit.
  have hbt : 0 ≤ D.bound 1 * t := hJ1.trans' (norm_nonneg _)
  have hdJ : ‖fderiv ℝ (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) 0‖ ≤
      D.bound 1 * t := by
    rwa [norm_iteratedFDeriv_one] at hJ1
  have hCt : 0 ≤ C * t := hG0.trans' (norm_nonneg _)
  have hC0 : 0 ≤ C := hdF.trans' (norm_nonneg _)
  have h₁ := div_le_div₀ hCt hdG hη hFη
  have h₂ := div_le_div₀ (mul_nonneg hbt hC0) (mul_le_mul hdJ hdF (norm_nonneg _) hbt) hη hFη
  have h₃ := div_le_div₀ (mul_nonneg hCt hC0) (mul_le_mul hG0 hdF (norm_nonneg _) hCt)
    (by positivity) (pow_le_pow_left₀ hη.le hFη 2)
  calc _ ≤ C * t / η + D.bound 1 * t * C / η + C * t * C / η ^ 2 := by gcongr
    _ = _ := by ring

/-- **The critical Hessian of `log |s_k|²` is negative in complex directions.** In the setting of
`SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`, on a boundaryless
manifold and with `η > 0`: for `k` large, at every point `x` where `s k` is differentiable and
does not vanish and which is a critical point of `f = log (‖s k‖ ^ 2)`, the critical Hessian
satisfies `Hess f (v, v) + Hess f (J v, J v) < 0` for every nonzero tangent vector `v` at `x`. -/
theorem IsUniformlyTransverse.criticalHessian_add_criticalHessian_neg [I.Boundaryless]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, PowerModel k))
        (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y)) x → s k x ≠ 0 →
      x ∈ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2)) →
      ∀ v : TangentSpace I x, v ≠ 0 →
        criticalHessian I (fun y ↦ Real.log (‖s k y‖ ^ 2)) x v v +
          criticalHessian I (fun y ↦ Real.log (‖s k y‖ ^ 2)) x (J x v) (J x v) < 0 := by
  obtain ⟨hreg, hjets⟩ := (D.isAsymptoticallyHolomorphic_def s).1 hs
  obtain ⟨C, hC⟩ := hjets 1
  have hsmall := Real.eventually_mul_rpow_neg_half_lt (C / η + D.bound 1 * C / η + C * C / η ^ 2)
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hreg, hC, ht.le_norm_of_mem_criticalPoints D hJ hα hρ₀ hs, hsmall,
    Filter.eventually_ge_atTop k₀, Filter.eventually_ge_atTop 1]
    with k hregk hCk hle hsk hk hk1 x hdiff hx hcrit v hv
  obtain ⟨hF, hGd⟩ := hregk x
  obtain ⟨hjet, hdbar⟩ := hCk x
  have hsrc := D.mem_source hk x
  have h0 : (0 : StdSpace ι) ∈ (D.chart k x).target :=
    D.apply_self hk x ▸ (D.chart k x).map_source hsrc
  have hF0 : ‖D.reading k x (s k) 0‖ = ‖s k x‖ := by
    rw [D.norm_reading, D.chart_symm_zero hk x]
  have hJd : DifferentiableAt ℝ (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) 0 :=
    (J.contDiffAt_chartPushforward (D.chart k x) h0).differentiableAt (by simp)
  rw [criticalHessian_add_criticalHessian_eq D hk (hF.of_le (by simp)) hx hcrit v]
  have hu : (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v : StdSpace ι) ≠ 0 := by
    intro h
    have hv' := (D.chart k x).mfderiv_symm_apply_mfderiv_apply (by simp) hsrc v
    rw [h, map_zero] at hv'
    exact hv hv'.symm
  refine (fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le (hF.of_le (by simp)) hJd
    (D.chartPushforward_zero hk x) (hGd.differentiableAt (by simp))
    (Filter.Eventually.of_forall (D.dbarReading_def k x (s k)))
    (norm_ne_zero_iff.1 (hF0 ▸ norm_ne_zero_iff.2 hx)) _).trans_lt ?_
  -- The error term is at most a constant times `k ^ (-1/2)`, which is below `1 / 4`.
  have hε := chartError_le D hρ₀ hk hk1 hη hjet hdbar (hF0 ▸ hle x hdiff hx hcrit)
  refine mul_neg_of_neg_of_pos ?_ (pow_pos ((@norm_pos_iff (StdSpace ι) _).2 hu) 2)
  linarith

/-- **The Morse index of `log |s_k|²` at its critical points is at least half the dimension.**
In the setting of `SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`, on a
boundaryless manifold and with `η > 0`: for `k` large, at every point `x` where `s k` is
differentiable and does not vanish and which is a critical point of `log (‖s k‖ ^ 2)`, the Morse
index there is at least `dim M / 2`. -/
theorem IsUniformlyTransverse.finrank_div_two_le_manifoldMorseIndex [I.Boundaryless]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, PowerModel k))
        (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y)) x → s k x ≠ 0 →
      x ∈ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2)) →
      Module.finrank ℝ E / 2 ≤ manifoldMorseIndex I (fun y ↦ Real.log (‖s k y‖ ^ 2)) x := by
  filter_upwards [ht.criticalHessian_add_criticalHessian_neg D hJ hα hρ₀ hη hs]
    with k hk x hdiff hx hcrit
  exact J.finrank_div_two_le_manifoldMorseIndex _ x (hk x hdiff hx hcrit)

end SymplecticGeometry

end
