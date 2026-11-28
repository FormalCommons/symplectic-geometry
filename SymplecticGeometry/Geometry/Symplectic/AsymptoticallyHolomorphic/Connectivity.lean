/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import SymplecticGeometry.Geometry.Manifold.Morse.ComplexNegativity
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Riemannian.Norm
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import SymplecticGeometry.Analysis.SpecialFunctions.Pow.Asymptotics
import SymplecticGeometry.Geometry.Manifold.Morse.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Metric
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartHessian
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Geometry.Manifold.Morse.Deformation.Cofibration
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

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
a point `f = log ‖s k‖²` is complex negative for `J`
(`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt`):
`Hess f (v, v) + Hess f (J v, J v) < 0` for every nonzero tangent vector `v`
(`SymplecticGeometry.IsUniformlyTransverse.isComplexNegativeAt_log_norm_sq`). In the chart
centred at `x`, the reading `F` of `s k` has `|F 0| ≥ η` and a bounded first derivative, while its
`∂̄` reading, with its first derivative, and the derivative of the pushed-forward almost complex
structure are `O(k ^ (-1/2))`. So the chart estimate
`SymplecticGeometry.fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le` bounds the sum by a
negative multiple of the square norm. The critical Hessian is carried to the chart by
`PartialDiffeomorph.criticalHessian_apply_eq_fderiv_fderiv`, and the derivative of the chart
carries `J` at `x` to the standard structure. The Morse index of `f` at `x` is then at least
half the dimension of `M`
(`SymplecticGeometry.IsUniformlyTransverse.finrank_div_two_le_manifoldMorseIndex`), by
`TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt.finrank_div_two_le_manifoldMorseIndex`.

When each `s k` is smooth, the negativity above passes to the critical points of the smooth
function `Bundle.logNormSq`, which is `y ↦ log ‖s k y‖²` on the open submanifold
`Bundle.nonzeroOpens` where `s k` does not vanish, for the restricted almost complex
structure `J.restrictOpen`
(`SymplecticGeometry.IsUniformlyTransverse.isComplexNegativeAt_logNormSq`),
by `TauCeti.SmoothAlmostComplexStructure.IsComplexNegativeAt.comp_subtypeVal`.

On a Hausdorff manifold, given `ε > 0` such that no point with `0 < ‖s k x‖² ≤ ε` is critical,
this function can then be made Morse without changing it on `{‖s k‖² ≤ ε}` and without losing the
index bound, by a compactly supported change; its sublevel set at `log ε` is still
`{‖s k‖² ≤ ε}`, `log ε` stays a regular value, the bands above it are compact, and the perturbed
function lies below one of its regular values, which can be taken above `log ε`
(`SymplecticGeometry.IsUniformlyTransverse.exists_isMorse_eqOn_logNormSq`, from
`TauCeti.SmoothAlmostComplexStructure.exists_isMorse_eqOn_preimage_Iic`).

The Morse theory of this perturbation gives a relative CW model of `W = {s k ≠ 0}` over
`A = {0 < ‖s k‖² ≤ ε}` with cells only in dimensions at least `dim M / 2`, together with the
homotopy extension property of `A` in `W`
(`SymplecticGeometry.IsUniformlyTransverse.exists_relCWComplex_homotopyEquiv_nonzeroOpens`).
Tau Ceti's `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel` models the full sublevel
over the sublevel at `log ε`, with one cell for each critical point between them, and
`TauCeti.hasHomotopyExtensionProperty_sublevel_of_isRegularValue` gives the homotopy extension
property. Both are carried to `A` and `W`, as sets of `M`, along the identifications of the two
sublevels with them; this is the form that
`SymplecticGeometry.exists_relCWComplex_homotopyEquiv_of_isPushout` takes.

These are the first steps of the Morse theory of `log |s_k|²` away from the zero set.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  Proposition 2 and §5.1
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
-/

public section

open scoped Manifold ContDiff ContinuousMap
open TauCeti Bundle Topology

namespace SymplecticGeometry

universe u

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] {ι : Type*} [Fintype ι]
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
    have h : J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chart k x x)
        (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v) =
          mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x (J x v) := by
      rw [J.chartPushforward_toOpenPartialHomeomorph]
      exact (D.chart k x).pushforwardEndomorphism_mfderiv_apply J hsrc v
    rw [hx0] at h
    exact (D.chartPushforward_zero hk x _).symm.trans h
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
does not vanish and which is a critical point of `f = log (‖s k‖ ^ 2)`, the function `f` is
complex negative for `J`: `Hess f (v, v) + Hess f (J v, J v) < 0` for every nonzero tangent vector
`v` at `x`. -/
theorem IsUniformlyTransverse.isComplexNegativeAt_log_norm_sq [I.Boundaryless]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x : M,
      MDifferentiableAt I (I.prod 𝓘(ℝ, PowerModel k))
        (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y)) x → s k x ≠ 0 →
      x ∈ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2)) →
      J.IsComplexNegativeAt (fun y ↦ Real.log (‖s k y‖ ^ 2)) x := by
  obtain ⟨hreg, hjets⟩ := (D.isAsymptoticallyHolomorphic_def s).1 hs
  obtain ⟨C, hC⟩ := hjets 1
  have hsmall := Real.eventually_mul_rpow_neg_half_lt (C / η + D.bound 1 * C / η + C * C / η ^ 2)
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hreg, hC, ht.le_norm_of_mem_criticalPoints D hJ hα hρ₀ hs, hsmall,
    Filter.eventually_ge_atTop k₀, Filter.eventually_ge_atTop 1]
    with k hregk hCk hle hsk hk hk1 x hdiff hx hcrit
  refine SmoothAlmostComplexStructure.isComplexNegativeAt_def.2 fun v hv ↦ ?_
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
  filter_upwards [ht.isComplexNegativeAt_log_norm_sq D hJ hα hρ₀ hη hs]
    with k hk x hdiff hx hcrit
  exact (hk x hdiff hx hcrit).finrank_div_two_le_manifoldMorseIndex

/-- **The critical Hessian of `log |s_k|²` on `{s_k ≠ 0}` is negative in complex directions.**
In the setting of `SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`, on a
boundaryless manifold, with `η > 0` and each `s k` smooth: for `k` large, at every critical point
`x` of `g = logNormSq (hsm k)` on `U = nonzeroOpens (hsm k)`, the function `g` is complex
negative for `J_U = J.restrictOpen U`: `Hess g (v, v) + Hess g (J_U v, J_U v) < 0` for every
nonzero tangent vector `v` at `x`. -/
theorem IsUniformlyTransverse.isComplexNegativeAt_logNormSq [I.Boundaryless]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s)
    (hsm : ∀ k : ℕ, ContMDiff I (I.prod 𝓘(ℝ, PowerModel k)) ∞
      (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y))) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ x ∈ criticalPoints I (logNormSq (hsm k)),
      (J.restrictOpen (nonzeroOpens (hsm k))).IsComplexNegativeAt (logNormSq (hsm k)) x := by
  filter_upwards [ht.isComplexNegativeAt_log_norm_sq D hJ hα hρ₀ hη hs]
    with k hk x hx
  rw [coe_logNormSq] at hx ⊢
  have hcrit := mem_criticalPoints_comp_subtypeVal.1 hx
  have hs0 : s k x ≠ 0 := mem_nonzeroOpens.1 x.property
  have hf := ((contMDiff_norm_sq_bundle I ∞ (PowerModel k) (PowerBundle P k)).comp
    (hsm k)).contMDiffAt.log (pow_ne_zero 2 (norm_ne_zero_iff.2 hs0))
  exact (hk x ((hsm k).mdifferentiableAt (by simp)) hs0 hcrit).comp_subtypeVal
    (hf.of_le (by simp)) hcrit

/-- **A Morse perturbation of `log |s_k|²` on `{s_k ≠ 0}` with index at least half the
dimension.** In the setting of
`SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`, on a Hausdorff
boundaryless manifold, with `η > 0` and each `s k` smooth: for `k` large and every
`ε > 0` such that `y ↦ log ‖s k y‖²` has no critical point `x` with `0 < ‖s k x‖² ≤ ε`, there is a
Morse function `g` on `U = nonzeroOpens (hsm k)` which agrees with `f = logNormSq (hsm k)` where
`‖s k‖² ≤ ε` and whose sublevel set `{g ≤ log ε}` is `{‖s k‖² ≤ ε}`, such that `g - f` has
compact support, whose Morse index at each critical point is at least `dim M / 2`, for which
`log ε` is a regular value, such that each band `g⁻¹[log ε, b]` is compact, and which has a
regular value `b > log ε` with `{g ≤ b}` all of `U`. -/
theorem IsUniformlyTransverse.exists_isMorse_eqOn_logNormSq [I.Boundaryless] [T2Space M]
    (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s)
    (hsm : ∀ k : ℕ, ContMDiff I (I.prod 𝓘(ℝ, PowerModel k)) ∞
      (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y))) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ ε : ℝ, 0 < ε →
      (∀ x : M, 0 < ‖s k x‖ ^ 2 → ‖s k x‖ ^ 2 ≤ ε →
        x ∉ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2))) →
      ∃ g : C^∞⟮I, nonzeroOpens (hsm k); 𝓘(ℝ), ℝ⟯, IsMorse I g ∧
        (∀ x : nonzeroOpens (hsm k), ‖s k x‖ ^ 2 ≤ ε → g x = logNormSq (hsm k) x) ∧
        (∀ x : nonzeroOpens (hsm k), g x ≤ Real.log ε ↔ ‖s k x‖ ^ 2 ≤ ε) ∧
        HasCompactSupport (fun x ↦ g x - logNormSq (hsm k) x) ∧
        (∀ x ∈ criticalPoints I g, Module.finrank ℝ E / 2 ≤ manifoldMorseIndex I g x) ∧
        IsRegularValue I 𝓘(ℝ) g (Real.log ε) ∧
        (∀ b, IsCompact (g ⁻¹' Set.Icc (Real.log ε) b)) ∧
        ∃ b, Real.log ε < b ∧ IsRegularValue I 𝓘(ℝ) g b ∧ {x | g x ≤ b} = Set.univ := by
  filter_upwards [ht.isComplexNegativeAt_logNormSq D hJ hα hρ₀ hη hs hsm]
    with k hk ε hε hcrit
  have hpos (x : nonzeroOpens (hsm k)) : 0 < ‖s k x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (mem_nonzeroOpens.1 x.property)) 2
  have hle (x : nonzeroOpens (hsm k)) :
      Real.log ε ≤ logNormSq (hsm k) x ↔ ε ≤ ‖s k x‖ ^ 2 := by
    rw [logNormSq_apply, Real.log_le_log_iff hε (hpos x)]
  -- The superlevel set `{log ε ≤ f}` is `{ε ≤ ‖s k‖²}`, a compact subset of `M` inside `U`.
  have hS : IsCompact {y : M | ε ≤ ‖s k y‖ ^ 2} :=
    (isClosed_le continuous_const ((contMDiff_norm_sq_bundle I ∞ (PowerModel k)
      (PowerBundle P k)).comp (hsm k)).continuous).isCompact
  have hSU : {y : M | ε ≤ ‖s k y‖ ^ 2} ⊆ nonzeroOpens (hsm k) := fun y hy ↦
    mem_nonzeroOpens.2 fun h ↦ by simp [h] at hy; linarith
  have hK : IsCompact (logNormSq (hsm k) ⁻¹' Set.Ici (Real.log ε)) := by
    have he : logNormSq (hsm k) ⁻¹' Set.Ici (Real.log ε) =
        Subtype.val ⁻¹' {y : M | ε ≤ ‖s k y‖ ^ 2} := Set.ext fun x ↦ hle x
    rw [he, Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hSU]
    exact hS
  have hcrit' (x : nonzeroOpens (hsm k)) (hx : x ∈ criticalPoints I (logNormSq (hsm k))) :
      Real.log ε < logNormSq (hsm k) x := by
    rw [coe_logNormSq, mem_criticalPoints_comp_subtypeVal] at hx
    refine lt_of_not_ge fun h ↦ hcrit x (hpos x) ?_ hx
    rwa [logNormSq_apply, Real.log_le_log_iff (hpos x) hε] at h
  obtain ⟨g, -, hgM, hgf, hIic, hgc, hgi, hreg, hgK, b, hεb, hb, hgb⟩ :=
    (J.restrictOpen (nonzeroOpens (hsm k))).exists_isMorse_eqOn_preimage_Iic hK hcrit' hk
      Filter.univ_mem
  have hgle (x : nonzeroOpens (hsm k)) : g x ≤ Real.log ε ↔ ‖s k x‖ ^ 2 ≤ ε := by
    have h := Set.ext_iff.1 hIic x
    simp only [Set.mem_preimage, Set.mem_Iic] at h
    rw [h, logNormSq_apply, Real.log_le_log_iff (hpos x) hε]
  refine ⟨g, hgM, fun x hx ↦ hgf ?_, hgle, hgc, hgi, hreg,
    fun b ↦ hgK.of_isClosed_subset (isClosed_Icc.preimage (map_continuous g))
      (Set.preimage_mono Set.Icc_subset_Ici_self),
    b, hεb, hb, Set.eq_univ_of_forall fun x ↦ (hgb x).le⟩
  rw [Set.mem_preimage, Set.mem_Iic, logNormSq_apply]
  exact Real.log_le_log (hpos x) hx

/-- **A relative CW model of `{s_k ≠ 0}` over `{0 < ‖s_k‖² ≤ ε}`.** In the setting of
`SymplecticGeometry.IsUniformlyTransverse.le_norm_of_mem_criticalPoints`, on a Hausdorff
boundaryless manifold, with `η > 0` and each `s k` smooth: for `k` large and every `ε > 0` such
that `y ↦ log ‖s k y‖²` has no critical point `x` with `0 < ‖s k x‖² ≤ ε`, write
`A = {x | 0 < ‖s k x‖² ≤ ε}` and `W = {x | s k x ≠ 0}`, the set of `nonzeroOpens (hsm k)`. Then
`A` has the homotopy extension property in `W`, and `W` is homotopy equivalent to a Hausdorff
relative CW complex `X`, in the universe of `M`, over the image of a closed embedding
`j : A → X`, with no cell of dimension less than `dim M / 2`, by a homotopy equivalence `h` with
`h (j a) = a`. -/
theorem IsUniformlyTransverse.exists_relCWComplex_homotopyEquiv_nonzeroOpens [I.Boundaryless]
    [T2Space M] (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀) (hJ : σ.Compatible J)
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) {η : ℝ} (hη : 0 < η)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s)
    (ht : IsUniformlyTransverse J α η s)
    (hsm : ∀ k : ℕ, ContMDiff I (I.prod 𝓘(ℝ, PowerModel k)) ∞
      (fun y ↦ TotalSpace.mk' (PowerModel k) y (s k y))) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ ε : ℝ, 0 < ε →
      (∀ x : M, 0 < ‖s k x‖ ^ 2 → ‖s k x‖ ^ 2 ≤ ε →
        x ∉ criticalPoints I (fun y ↦ Real.log (‖s k y‖ ^ 2))) →
      (∀ hAW : {x : M | 0 < ‖s k x‖ ^ 2 ∧ ‖s k x‖ ^ 2 ≤ ε} ⊆ (nonzeroOpens (hsm k) : Set M),
        HasHomotopyExtensionProperty (Set.range (ContinuousMap.inclusion hAW))) ∧
      ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
        (j : C({x : M | 0 < ‖s k x‖ ^ 2 ∧ ‖s k x‖ ^ 2 ≤ ε}, X))
        (_ : RelCWComplex (Set.univ : Set X) (Set.range j))
        (h : X ≃ₕ (nonzeroOpens (hsm k) : Set M)),
        IsClosedEmbedding j ∧ (∀ a, (h (j a) : M) = a) ∧
        ∀ m < Module.finrank ℝ E / 2, IsEmpty (RelCWComplex.cell (Set.univ : Set X) m) := by
  filter_upwards [ht.exists_isMorse_eqOn_logNormSq D hJ hα hρ₀ hη hs hsm] with k hk ε hε hcrit
  set U := nonzeroOpens (hsm k)
  set A : Set M := {x : M | 0 < ‖s k x‖ ^ 2 ∧ ‖s k x‖ ^ 2 ≤ ε}
  obtain ⟨g, hgM, -, hgle, -, hgi, hreg, hgK, b, hεb, hb, hgb⟩ := hk ε hε hcrit
  have hpos (x : U) : 0 < ‖s k x‖ ^ 2 := pow_pos (norm_pos_iff.2 (mem_nonzeroOpens.1 x.property)) 2
  have hAU (x : M) (hx : x ∈ A) : x ∈ U :=
    mem_nonzeroOpens.2 fun h ↦ by simp [A, h] at hx
  -- `A` is the sublevel set `{g ≤ log ε}`, read in `M`.
  have hrange (hAW : A ⊆ (U : Set M)) :
      Set.range (ContinuousMap.inclusion hAW) = {x : U | g x ≤ Real.log ε} := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x, hpos x, (hgle x).1 hx⟩, rfl⟩⟩
    rintro ⟨a, rfl⟩
    exact (hgle _).2 a.property.2
  let eA : A ≃ₜ {x : U | g x ≤ Real.log ε} :=
    { toFun := fun x ↦ ⟨⟨x, hAU x x.property⟩, (hgle _).2 x.property.2⟩
      invFun := fun x ↦ ⟨x.val, hpos x.val, (hgle x.val).1 x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eW : {x : U | g x ≤ b} ≃ₜ (U : Set M) :=
    (Homeomorph.setCongr hgb).trans (Homeomorph.Set.univ U)
  have heA (a : A) : ((eA a : U) : M) = a := rfl
  have heW (y : {x : U | g x ≤ b}) : (eW y : M) = (y : U) := rfl
  refine ⟨fun hAW ↦ ?_, ?_⟩
  · -- The subtype of `U` as a set of `M` is the subtype of `U` itself.
    have hA := hasHomotopyExtensionProperty_sublevel_of_isRegularValue g.contMDiff hεb (hgK b) hreg
    rw [hrange hAW]
    exact hA
  obtain ⟨X, _, _, j, _, h, hj, hh, ⟨e⟩⟩ :=
    hgM.exists_relCWComplex_homotopyEquiv_sublevel hεb.le (hgK b) hreg hb
  -- The cells are indexed by critical points, of index at least `dim M / 2`.
  have hcell (m : ℕ) (hm : m < Module.finrank ℝ E / 2) :
      IsEmpty (RelCWComplex.cell (Set.univ : Set X) m) :=
    have : IsEmpty {x ∈ criticalPoints I g ∩ g ⁻¹' Set.Ioc (Real.log ε) b |
        manifoldMorseIndex I g x = m} :=
      ⟨fun ⟨x, ⟨hx, _⟩, hxm⟩ ↦ absurd (hgi x hx) (by omega)⟩
    (e m).isEmpty
  clear e
  -- Precomposing `j` with the homeomorphism `A ≃ₜ {g ≤ log ε}` does not change its range.
  have hr : Set.range (j.comp (eA : C(A, {x : U | g x ≤ Real.log ε}))) = Set.range j := by
    rw [ContinuousMap.coe_comp, ContinuousMap.coe_ofClass]
    exact eA.surjective.range_comp _
  clear_value eA eW
  revert hcell ‹RelCWComplex (Set.univ : Set X) (Set.range j)›
  rw [← hr]
  intro _ hcell
  refine ⟨X, _, ‹_›, _, ‹_›, h.trans eW.toHomotopyEquiv, ?_, fun a ↦ ?_, hcell⟩
  · rw [ContinuousMap.coe_comp, ContinuousMap.coe_ofClass]
    exact hj.comp eA.isClosedEmbedding
  · rw [ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv, heW,
      ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, hh, heA]

end SymplecticGeometry

end
