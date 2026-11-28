/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakFunction
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartChange
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartTransition
import SymplecticGeometry.LinearAlgebra.Complex.LinearPart

/-!
# Quotients by the cut-off Gaussian and their flat `∂̄`

To correct a section near a point `x`, its reading `f` in the chart centred at `x` is divided by
the cut-off Gaussian `SymplecticGeometry.peakFunction k`. On a ball of fixed radius `R`, and for
`k` so large that `R < k ^ (1 / 6)`, the cut-off is `1` and the quotient is
`q = f * exp (‖z‖ ^ 2 / 4)` (`SymplecticGeometry.div_peakFunction_eventuallyEq`). This file bounds
the jets of `q` and of its flat `∂̄` there, with constants that depend only on the order and on
`R`.

The Gaussian `G = exp (-‖z‖ ^ 2 / 4)` has model `∂̄` zero (`modelDbar_gaussian`), so by the
Leibniz rule `modelDbar_mul` the model `∂̄` of `f = q * G` for the constant structure `J₀` is
`G • flatDbar q`. For a field `J` of structures, `modelDbarWith_eq_add` writes the model `∂̄`
of `f` for `J` as the one for `J₀` plus `(i / 2) ∇f ∘ (J - J₀)`, with `∇f` the model connection
`modelConnection f`, and `exists_jetNormAt_modelDbarWith_sub_le` bounds the jets of that
difference.

## Main results

* `SymplecticGeometry.flatDbar_mul_exp_eq_smul_modelDbar`: `flatDbar q = exp (‖z‖ ^ 2 / 4) •
  modelDbar f` at every point where `f` is differentiable, and
  `SymplecticGeometry.flatDbar_mul_exp_eq`: for a field `J`,
  `flatDbar q = exp (‖z‖ ^ 2 / 4) • (modelDbarWith J f - (i / 2) ∇f ∘ (J - J₀))`.
* `SymplecticGeometry.modelDel_mul_gaussian`: for `q` differentiable at `z` and
  `G = exp (-‖z‖ ^ 2 / 4)`, the model `∂` of `q * G` at `z` is `G z • (∂q(z) + q z • μ z)`, for
  `∂q(z) = flatDel q z` the flat `∂` of `q` and `μ = gaussianConnectionForm`; so its operator
  norm is at least `G z * (‖∂q(z)‖ - ‖z‖ ‖q z‖ / 2)`
  (`SymplecticGeometry.mul_sub_le_norm_modelDel_mul_gaussian`).
* `SymplecticGeometry.exists_jetNormAt_div_peakFunction_le`: on the closed ball of radius `R` and
  for `R < k ^ (1 / 6)`, the `r`-jet norm of `f / peakFunction k` is at most `C` times that
  of `f`.
* `SymplecticGeometry.exists_jetNormAt_flatDbar_div_peakFunction_le`: there, the `r`-jet norm of
  its flat `∂̄` is at most `C` times the `r`-jet norm of `modelDbarWith J f` plus the `r`-jet norm
  of `J - J₀` times the `(r + 1)`-jet norm of `f`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_flatDbar_reading_div_peakFunction_le`:
  for the readings of sections in rescaled unitary charts of radius `ρ₀ > 0`, for large `k`, the
  `r`-jet norm of the flat `∂̄` of the quotient is at most `C` times the `r`-jet norm of the `∂̄`
  reading plus `k ^ (-1 / 2)` times the `(r + 1)`-jet norm of the reading. The structure read in
  the chart is `J_{k,x}`, whose distance to `J₀` is bounded by
  `RescaledUnitaryCharts.exists_jetNormAt_chartPushforward_sub_le`. The orders `r = 0` and `r = 1`
  bound the flat `∂̄` of the quotient and its derivative (`norm_le_jetNormAt`,
  `norm_fderiv_le_jetNormAt`).
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_norm_reading_div_peakFunction_le`: for
  explicit bounds on the `2`-jet of the reading and on the `1`-jet of its `∂̄` reading on the ball
  of radius `11 / 10`, the quotient meets there the hypotheses of the local transversality
  estimate `SymplecticGeometry.exists_norm_le_max_ge_of_flatDbar_le`, with a `C¹` bound `A ≥ 1`
  and a flat `∂̄` of order `k ^ (-1 / 2)`, uniformly in the centre and the section; and
  `IsAsymptoticallyHolomorphic.exists_forall_norm_reading_div_peakFunction_le`:
  in the same namespace, the same for an asymptotically holomorphic sequence.
* `RescaledUnitaryCharts.eventually_div_four_le_max_of_reading_eventuallyEq_mul_gaussian`:
  for the metric `σ(·, J ·)`, if the reading of `s` is `q` times the Gaussian near a point `z` of
  the closed unit ball and the connection read there is bounded by `B`, then
  `ε ≤ max ‖q z‖ ‖∂q(z)‖` gives `ε / 4 ≤ max ‖s y‖ ((2π k)^(-1/2) ‖∂ s(y)‖)` at the image `y` of
  `z`, for all `k` beyond a bound that does not depend on `x`, `s`, `q` or `z`. The right side is
  the quantity of `SymplecticGeometry.IsUniformlyTransverse`.
  If `‖q z‖ ≥ ε / 2` the section is large; otherwise the lower bound
  `mul_sub_le_norm_modelDel_mul_gaussian` meets the upper bound
  `RescaledUnitaryCharts.norm_modelDel_reading_le_of_inner_eq`, whose error
  terms are `O(k ^ (-1/2))`.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  proof of Proposition 2
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

open Metric TauCeti
open scoped Topology Manifold ContDiff

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- **The flat `∂̄` of the quotient by the Gaussian.** For `f` differentiable at `w`, the flat `∂̄`
of `q = f * exp (‖·‖ ^ 2 / 4)` at `w` is `exp (‖w‖ ^ 2 / 4)` times the model `∂̄` of `f` at `w`, for
the constant structure `J₀`. -/
theorem flatDbar_mul_exp_eq_smul_modelDbar {f : StdSpace ι → ℂ} {w : StdSpace ι}
    (hf : DifferentiableAt ℝ f w) :
    flatDbar (fun y ↦ f y * Real.exp (‖y‖ ^ 2 / 4)) w =
      (Real.exp (‖w‖ ^ 2 / 4) : ℂ) • modelDbar f w := by
  set E : StdSpace ι → ℂ := fun y ↦ Real.exp (‖y‖ ^ 2 / 4)
  set G : StdSpace ι → ℂ := fun y ↦ Real.exp (-‖y‖ ^ 2 / 4)
  have hEG (y : StdSpace ι) : E y * G y = 1 := by
    simp only [E, G, ← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
    simp
  have hq : DifferentiableAt ℝ (fun y ↦ f y * E y) w :=
    hf.mul ((contDiff_ofReal_exp_norm_sq_div_four (n := 1)).differentiable one_ne_zero w)
  have hG : DifferentiableAt ℝ G w :=
    (contDiff_ofReal_gaussian (n := 1)).differentiable one_ne_zero w
  have hf' : f = fun y ↦ (f y * E y) * G y := by
    funext y
    rw [mul_assoc, hEG, mul_one]
  -- The Gaussian has model `∂̄` zero, so the Leibniz rule leaves `G • flatDbar q`.
  have hmodel : modelDbar f w = G w • flatDbar (fun y ↦ f y * E y) w := by
    conv_lhs => rw [hf']
    have h0 : modelDbar G w = 0 := by rw [modelDbar_gaussian, Pi.zero_apply]
    rw [modelDbar_mul hq hG, h0]
    ext v
    simp
  rw [hmodel, smul_smul, show E w * G w = 1 from hEG w, one_smul]

/-- **The flat `∂̄` of the quotient by the Gaussian, for a field of structures.** For a field `J`
of real-linear endomorphisms of `StdSpace ι` and `f` differentiable at `w`, the flat `∂̄` of
`q = f * exp (‖·‖ ^ 2 / 4)` at `w` is `exp (‖w‖ ^ 2 / 4)` times the model `∂̄` of `f` for `J`
minus `(i / 2) ∇f ∘ (J w - J₀)`, for `∇f` the model connection of `f` at `w`. -/
theorem flatDbar_mul_exp_eq (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) {f : StdSpace ι → ℂ}
    {w : StdSpace ι} (hf : DifferentiableAt ℝ f w) :
    flatDbar (fun y ↦ f y * Real.exp (‖y‖ ^ 2 / 4)) w =
      (Real.exp (‖w‖ ^ 2 / 4) : ℂ) • (modelDbarWith J f w -
        (((2⁻¹ : ℂ) * Complex.I) • modelConnection f w).comp
          (J w - LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)) := by
  rw [flatDbar_mul_exp_eq_smul_modelDbar hf, modelDbarWith_eq_add J
    (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) f w,
    ← modelDbar_def, add_sub_cancel_right]

/-- **The model `∂` of a product with the Gaussian.** For `q` differentiable at `z` and
`G = exp (-‖·‖ ^ 2 / 4)`, the model `∂` of `q * G` at `z` is `G z` times the sum of the flat `∂`
of `q` at `z` and `q z` times the connection form `gaussianConnectionForm z`. -/
theorem modelDel_mul_gaussian {q : StdSpace ι → ℂ} {z : StdSpace ι}
    (hq : DifferentiableAt ℝ q z) :
    modelDel (fun y ↦ q y * Real.exp (-‖y‖ ^ 2 / 4)) z =
      Real.exp (-‖z‖ ^ 2 / 4) • (flatDel q z + q z • gaussianConnectionForm z) := by
  have hG : DifferentiableAt ℝ (fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ)) z :=
    (contDiff_ofReal_gaussian (n := 1)).differentiable one_ne_zero z
  rw [modelDel_mul hq hG, modelDel_gaussian]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- **A lower bound on the model `∂` of a product with the Gaussian.** For `q` differentiable at
`z` and `G = exp (-‖·‖ ^ 2 / 4)`, the operator norm of the model `∂` of `q * G` at `z` is at
least `G z * (‖∂q(z)‖ - ‖z‖ ‖q z‖ / 2)`, for `∂q(z)` the flat `∂` of `q` at `z`. -/
theorem mul_sub_le_norm_modelDel_mul_gaussian {q : StdSpace ι → ℂ} {z : StdSpace ι}
    (hq : DifferentiableAt ℝ q z) :
    Real.exp (-‖z‖ ^ 2 / 4) * (‖flatDel q z‖ - ‖z‖ * ‖q z‖ / 2) ≤
      ‖modelDel (fun y ↦ q y * Real.exp (-‖y‖ ^ 2 / 4)) z‖ := by
  rw [modelDel_mul_gaussian hq, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h1 : ‖q z • gaussianConnectionForm z‖ ≤ ‖z‖ * ‖q z‖ / 2 := by
    rw [norm_smul, mul_comm, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right (norm_gaussianConnectionForm_le z) (norm_nonneg _)
  have h2 := norm_sub_norm_le (flatDel q z) (-(q z • gaussianConnectionForm z))
  rw [norm_neg, sub_neg_eq_add] at h2
  linarith

/-- **Jets of the quotient by the cut-off Gaussian.** For every order `r` and radius `R` there is
a constant `C ≥ 0` such that, for every `k` with `R < k ^ (1 / 6)`, every `f` and every `z`
with `‖z‖ ≤ R` where `f` is `C^r`, the `r`-jet norm of `f / peakFunction k` at `z` is at most `C`
times that of `f`. -/
theorem exists_jetNormAt_div_peakFunction_le (r : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (f : StdSpace ι → ℂ) {z : StdSpace ι}, ‖z‖ ≤ R →
      R < (k : ℝ) ^ (1 / 6 : ℝ) → ContDiffAt ℝ r f z →
      jetNormAt ℝ r (fun y ↦ f y / peakFunction k y) z ≤ C * jetNormAt ℝ r f z := by
  obtain ⟨A, hA0, hA⟩ := exists_jetNormAt_le_of_isCompact
    (contDiff_ofReal_exp_norm_sq_div_four (E := StdSpace ι) (n := r)) (isCompact_closedBall 0 R)
  refine ⟨2 ^ r * A, by positivity, fun k f z hz hk hf ↦ ?_⟩
  rw [jetNormAt_congr_of_eventuallyEq r (div_peakFunction_eventuallyEq k f (hz.trans_lt hk))]
  have he : (fun y ↦ f y * (Real.exp (‖y‖ ^ 2 / 4) : ℂ)) =
      fun y ↦ (Real.exp (‖y‖ ^ 2 / 4) : ℂ) • f y :=
    funext fun y ↦ by rw [smul_eq_mul, mul_comm]
  rw [he]
  calc _ ≤ 2 ^ r * jetNormAt ℝ r (fun y : StdSpace ι ↦ (Real.exp (‖y‖ ^ 2 / 4) : ℂ)) z *
        jetNormAt ℝ r f z :=
        jetNormAt_fun_smul_le contDiff_ofReal_exp_norm_sq_div_four.contDiffAt hf
    _ ≤ 2 ^ r * A * jetNormAt ℝ r f z := by
        gcongr
        · exact jetNormAt_nonneg _ _ _
        · exact hA z (mem_closedBall_zero_iff.2 hz)

/-- **Jets of the flat `∂̄` of the quotient by the cut-off Gaussian.** For every order `r` and
radius `R` there is a constant `C ≥ 0` such that, for every `k` with `R < k ^ (1 / 6)`, every field
`J` of real-linear endomorphisms of `StdSpace ι`, every `f` and every `z` with `‖z‖ ≤ R` where `f`
is `C^(r + 1)` and `J` is `C^r`, the `r`-jet norm at `z` of the flat `∂̄` of `f / peakFunction k`
is at most `C` times the `r`-jet norm of the model `∂̄` of `f` for `J` plus the product of the
`r`-jet norm of `J - J₀` and the `(r + 1)`-jet norm of `f`. -/
theorem exists_jetNormAt_flatDbar_div_peakFunction_le (r : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
      {z : StdSpace ι}, ‖z‖ ≤ R → R < (k : ℝ) ^ (1 / 6 : ℝ) →
      ContDiffAt ℝ (r + 1 : ℕ) f z → ContDiffAt ℝ r J z →
      jetNormAt ℝ r (flatDbar fun y ↦ f y / peakFunction k y) z ≤
        C * (jetNormAt ℝ r (modelDbarWith J f) z +
          jetNormAt ℝ r (fun w ↦ J w -
              LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) z *
            jetNormAt ℝ (r + 1) f z) := by
  obtain ⟨A, hA0, hA⟩ := exists_jetNormAt_le_of_isCompact
    (contDiff_ofReal_exp_norm_sq_div_four (E := StdSpace ι) (n := r)) (isCompact_closedBall 0 R)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_jetNormAt_modelDbarWith_sub_le (ι := ι) r
  set J₀ := LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap
  set K := C₁ * (1 + |R|)
  have hK : 0 ≤ K := by positivity
  refine ⟨2 ^ r * A * (1 + K), by positivity, fun k J f z hz hk hf hJ ↦ ?_⟩
  set E : StdSpace ι → ℂ := fun y ↦ Real.exp (‖y‖ ^ 2 / 4)
  set T := fun w ↦ modelDbarWith J f w - modelDbarWith (fun _ ↦ J₀) f w
  have hE : ContDiffAt ℝ r E z := contDiff_ofReal_exp_norm_sq_div_four.contDiffAt
  have hf1 : ContDiffAt ℝ (r + 1) f z := by exact_mod_cast hf
  -- Near `z`, the quotient's flat `∂̄` is `E • modelDbar f`, by
  -- `flatDbar_mul_exp_eq_smul_modelDbar`, and `modelDbar f` is `modelDbarWith J f - T`.
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ f w :=
    (hf.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by simp)
  have hq : flatDbar (fun y ↦ f y / peakFunction k y) =ᶠ[𝓝 z]
      fun w ↦ E w • (modelDbarWith J f w + -T w) := by
    have h1 := (div_peakFunction_eventuallyEq k f (hz.trans_lt hk)).eventually_nhds
    filter_upwards [h1, hdiff] with w hw hfw
    rw [flatDbar_def, flatDbarWith_congr_of_eventuallyEq hw, ← flatDbar_def,
      flatDbar_mul_exp_eq_smul_modelDbar hfw, modelDbar_def]
    simp only [T, E, J₀, neg_sub, add_sub_cancel]
  rw [jetNormAt_congr_of_eventuallyEq r hq]
  have hD : ContDiffAt ℝ r (modelDbarWith J f) z := contDiffAt_modelDbarWith hJ hf1
  have hT : ContDiffAt ℝ r T z := hD.sub (contDiffAt_modelDbarWith contDiffAt_const hf1)
  have hsum := jetNormAt_add_le hD hT.neg
  rw [show jetNormAt ℝ r (fun w ↦ -T w) z = jetNormAt ℝ r T z from jetNormAt_neg r _ z] at hsum
  have hTle : jetNormAt ℝ r T z ≤
      K * (jetNormAt ℝ r (fun w ↦ J w - J₀) z * jetNormAt ℝ (r + 1) f z) := by
    have h := hC₁ J (fun _ ↦ J₀) f hf hJ contDiffAt_const
    have h1 : C₁ * (1 + ‖z‖) ≤ C₁ * (1 + |R|) := by
      have : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
      gcongr
    refine h.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right h1
      (mul_nonneg (jetNormAt_nonneg _ _ _) (jetNormAt_nonneg _ _ _))
  have hP := jetNormAt_fun_smul_le hE (hD.add hT.neg)
  have hAz : jetNormAt ℝ r E z ≤ A := hA z (mem_closedBall_zero_iff.2 hz)
  set a := jetNormAt ℝ r (modelDbarWith J f) z
  set b := jetNormAt ℝ r (fun w ↦ J w - J₀) z * jetNormAt ℝ (r + 1) f z
  have ha : 0 ≤ a := jetNormAt_nonneg _ _ _
  have hb : 0 ≤ b := mul_nonneg (jetNormAt_nonneg _ _ _) (jetNormAt_nonneg _ _ _)
  calc _ ≤ 2 ^ r * jetNormAt ℝ r E z *
        jetNormAt ℝ r (fun w ↦ modelDbarWith J f w + -T w) z := hP
    _ ≤ 2 ^ r * A * (a + K * b) := by
        gcongr
        · exact jetNormAt_nonneg _ _ _
        · exact hsum.trans (add_le_add le_rfl hTle)
    _ ≤ 2 ^ r * A * (1 + K) * (a + b) := by
        have : a + K * b ≤ (1 + K) * (a + b) := by nlinarith
        calc 2 ^ r * A * (a + K * b) ≤ 2 ^ r * A * ((1 + K) * (a + b)) := by gcongr
          _ = _ := by ring

namespace RescaledUnitaryCharts

open _root_.Bundle MulOpposite

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- **The flat `∂̄` of a reading divided by the cut-off Gaussian.** For every order `r` and radius
`R` there is a constant `C ≥ 0` such that, for rescaled unitary charts of radius `ρ₀ > 0`, for all
large `k`, every centre `x`, every section `s` of `PowerBundle P k` and every `z` with `‖z‖ ≤ R`
where the reading `f` of `s` is `C^(r + 1)`, the
`r`-jet norm at `z` of the flat `∂̄` of `f / peakFunction k` is at most `C` times the `r`-jet norm
of the `∂̄` reading of `s` plus `k ^ (-1 / 2)` times the `(r + 1)`-jet norm of `f`. -/
theorem exists_jetNormAt_flatDbar_reading_div_peakFunction_le (hρ₀ : 0 < ρ₀) (r : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M) (s : Π y, PowerBundle P k y) {z : StdSpace ι},
      ‖z‖ ≤ R → ContDiffAt ℝ (r + 1 : ℕ) (D.reading k x s) z →
      jetNormAt ℝ r (flatDbar fun y ↦ D.reading k x s y / peakFunction k y) z ≤
        C * (jetNormAt ℝ r (D.dbarReading k x s) z +
          (k : ℝ) ^ (-1 / 2 : ℝ) * jetNormAt ℝ (r + 1) (D.reading k x s) z) := by
  obtain ⟨C, hC0, hC⟩ := exists_jetNormAt_flatDbar_div_peakFunction_le (ι := ι) r R
  obtain ⟨C₀, hC₀0, hC₀⟩ := D.exists_jetNormAt_chartPushforward_sub_le r
  set C' := C₀ * (1 + |R|)
  have hC' : 0 ≤ C' := by positivity
  have h6 : ∀ᶠ k : ℕ in Filter.atTop, R < (k : ℝ) ^ (1 / 6 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop R
  have hρ : ∀ᶠ k : ℕ in Filter.atTop, R < ρ₀ * √k :=
    (((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ₀).eventually_gt_atTop R)
  refine ⟨C * (1 + C'), by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop k₀, h6, hρ] with k hk hk6 hkρ x s z hz hf
  have hzb : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k) := mem_ball_zero_iff.2 (hz.trans_lt hkρ)
  have hJ : ContDiffAt ℝ r (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) z :=
    (J.contDiffAt_chartPushforward (D.chart k x) (D.ball_subset_target hk x hzb)).of_le
      (by exact_mod_cast le_top)
  have h := hC k _ _ hz hk6 hf hJ
  rw [← funext (D.dbarReading_def k x s)] at h
  have hj := hC₀ hk x hzb
  rw [Real.inv_sqrt_eq_rpow] at hj
  refine h.trans ?_
  set a := jetNormAt ℝ r (D.dbarReading k x s) z
  set b := jetNormAt ℝ (r + 1) (D.reading k x s) z
  set j := jetNormAt ℝ r (fun w ↦ J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w -
    LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) z
  set t := (k : ℝ) ^ (-1 / 2 : ℝ)
  have ha : 0 ≤ a := jetNormAt_nonneg _ _ _
  have hb : 0 ≤ b := jetNormAt_nonneg _ _ _
  have ht : 0 ≤ t := by positivity
  have hz' : 1 + ‖z‖ ≤ 1 + |R| := by linarith [le_abs_self R]
  have hj' : j ≤ C' * t := by
    refine hj.trans ?_
    calc C₀ * t * (1 + ‖z‖) ≤ C₀ * t * (1 + |R|) :=
          mul_le_mul_of_nonneg_left hz' (by positivity)
      _ = C' * t := by ring
  calc C * (a + j * b) ≤ C * (a + C' * t * b) := by gcongr
    _ ≤ C * (1 + C') * (a + t * b) := by
        have : a + C' * t * b ≤ (1 + C') * (a + t * b) := by
          nlinarith [mul_nonneg ht hb]
        calc C * (a + C' * t * b) ≤ C * ((1 + C') * (a + t * b)) := by gcongr
          _ = _ := by ring

/-- **The quotient of a reading by the cut-off Gaussian is a `C¹`-bounded function with small
flat `∂̄`.** For rescaled unitary charts of radius `ρ₀ > 0` and every bound `B` there are `A ≥ 1`
and `C` such that, for all large `k`, every centre `x` and every section `s` of `PowerBundle P k`
whose reading `f` in the chart at `x` is, at each point of the ball of radius `11 / 10`, `C²` with
`2`-jet norm at most `B`, and whose `∂̄` reading has `1`-jet norm at most `B * k ^ (-1 / 2)`
there, the quotient `q = f / peakFunction k` satisfies, at each point of that ball: `q` is `C²`,
`‖q‖ ≤ A`, `‖dq‖ ≤ A`, `‖flatDbar q‖ ≤ C * k ^ (-1 / 2)`, and the derivative of
`y ↦ flatDbar q y b` has norm at most `C * k ^ (-1 / 2) * ‖b‖`. These are the hypotheses of
`SymplecticGeometry.exists_norm_le_max_ge_of_flatDbar_le`. -/
theorem exists_forall_norm_reading_div_peakFunction_le (hρ₀ : 0 < ρ₀) (B : ℝ) :
    ∃ A, 1 ≤ A ∧ ∃ C, ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M) (s : Π y, PowerBundle P k y),
      (∀ z ∈ ball (0 : StdSpace ι) (11 / 10), ContDiffAt ℝ 2 (D.reading k x s) z ∧
        jetNormAt ℝ 2 (D.reading k x s) z ≤ B ∧
        jetNormAt ℝ 1 (D.dbarReading k x s) z ≤ B * (k : ℝ) ^ (-1 / 2 : ℝ)) →
      ∀ z ∈ ball (0 : StdSpace ι) (11 / 10),
        ContDiffAt ℝ 2 (fun y ↦ D.reading k x s y / peakFunction k y) z ∧
        ‖D.reading k x s z / peakFunction k z‖ ≤ A ∧
        ‖fderiv ℝ (fun y ↦ D.reading k x s y / peakFunction k y) z‖ ≤ A ∧
        ‖flatDbar (fun y ↦ D.reading k x s y / peakFunction k y) z‖ ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) ∧
        ∀ b, ‖fderiv ℝ (fun y ↦ flatDbar (fun y ↦ D.reading k x s y / peakFunction k y) y b) z‖ ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) * ‖b‖ := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_jetNormAt_div_peakFunction_le (ι := ι) 1 (11 / 10)
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    D.exists_jetNormAt_flatDbar_reading_div_peakFunction_le hρ₀ 1 (11 / 10)
  have h6 : ∀ᶠ k : ℕ in Filter.atTop, (11 / 10 : ℝ) < (k : ℝ) ^ (1 / 6 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop (11 / 10 : ℝ)
  refine ⟨max 1 (C₁ * B), le_max_left _ _, 2 * C₂ * B, ?_⟩
  filter_upwards [h6, hC₂] with k hk6 hk x s hs z hz
  obtain ⟨hf, hfB, hdB⟩ := hs z hz
  set f := D.reading k x s
  set q := fun y ↦ f y / peakFunction k y
  set t := (k : ℝ) ^ (-1 / 2 : ℝ)
  have hz' : ‖z‖ ≤ 11 / 10 := (mem_ball_zero_iff.1 hz).le
  have hq : q =ᶠ[𝓝 z] fun y ↦ f y * Real.exp (‖y‖ ^ 2 / 4) :=
    div_peakFunction_eventuallyEq k f (hz'.trans_lt hk6)
  have hqC : ContDiffAt ℝ 2 q z :=
    (hf.mul contDiff_ofReal_exp_norm_sq_div_four.contDiffAt).congr_of_eventuallyEq hq
  have hf1 : jetNormAt ℝ 1 f z ≤ B := (jetNormAt_mono f z (by norm_num)).trans hfB
  -- The `1`-jet of `q` is bounded by `C₁ * B`.
  have hqJ : jetNormAt ℝ 1 q z ≤ max 1 (C₁ * B) :=
    calc jetNormAt ℝ 1 q z ≤ C₁ * jetNormAt ℝ 1 f z :=
          hC₁ k f hz' hk6 (hf.of_le (by norm_num))
      _ ≤ C₁ * B := by gcongr
      _ ≤ _ := le_max_right _ _
  -- The `1`-jet of its flat `∂̄` is bounded by `2 * C₂ * B * t`.
  have hdJ : jetNormAt ℝ 1 (flatDbar q) z ≤ 2 * C₂ * B * t :=
    calc jetNormAt ℝ 1 (flatDbar q) z ≤
          C₂ * (jetNormAt ℝ 1 (D.dbarReading k x s) z + t * jetNormAt ℝ (1 + 1) f z) :=
          hk x s hz' hf
      _ ≤ C₂ * (B * t + t * B) := by gcongr
      _ = 2 * C₂ * B * t := by ring
  have hdD : DifferentiableAt ℝ (flatDbar q) z :=
    (contDiffAt_flatDbar (n := 1) hqC).differentiableAt one_ne_zero
  refine ⟨hqC, (norm_le_jetNormAt 1 q z).trans hqJ,
    (norm_fderiv_le_jetNormAt le_rfl q z).trans hqJ,
    (norm_le_jetNormAt 1 _ z).trans hdJ, fun b ↦ ?_⟩
  rw [fderiv_clm_apply hdD (differentiableAt_const b), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add]
  calc ‖(fderiv ℝ (flatDbar q) z).flip b‖ ≤ ‖(fderiv ℝ (flatDbar q) z).flip‖ * ‖b‖ :=
        ContinuousLinearMap.le_opNorm _ b
    _ ≤ 2 * C₂ * B * t * ‖b‖ := by
        rw [ContinuousLinearMap.opNorm_flip]
        gcongr
        exact (norm_fderiv_le_jetNormAt le_rfl _ z).trans hdJ

/-- **The quotients of an asymptotically holomorphic sequence by the cut-off Gaussian.** Let `M`
be a Hausdorff boundaryless manifold, let `σ` be compatible with `J`, let `M` carry the metric
`g_J` of the pair, let `α` be a connection form and `ρ₀ > 0`, and let `s` be an asymptotically
holomorphic sequence of sections. There are `A ≥ 1` and `C` such that, for all large `k` and
every centre `x`, the quotient `q = f / peakFunction k` of the reading `f` of `s k` in the chart
at `x` satisfies, at each point of the ball of radius `11 / 10`: `q` is `C²`, `‖q‖ ≤ A`,
`‖dq‖ ≤ A`, `‖flatDbar q‖ ≤ C * k ^ (-1 / 2)`, and the derivative of `y ↦ flatDbar q y b` has
norm at most `C * k ^ (-1 / 2) * ‖b‖`. -/
theorem IsAsymptoticallyHolomorphic.exists_forall_norm_reading_div_peakFunction_le [T2Space M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s) :
    ∃ A, 1 ≤ A ∧ ∃ C, ∀ᶠ k : ℕ in Filter.atTop, ∀ x : M,
      ∀ z ∈ ball (0 : StdSpace ι) (11 / 10),
        ContDiffAt ℝ 2 (fun y ↦ D.reading k x (s k) y / peakFunction k y) z ∧
        ‖D.reading k x (s k) z / peakFunction k z‖ ≤ A ∧
        ‖fderiv ℝ (fun y ↦ D.reading k x (s k) y / peakFunction k y) z‖ ≤ A ∧
        ‖flatDbar (fun y ↦ D.reading k x (s k) y / peakFunction k y) z‖ ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) ∧
        ∀ b, ‖fderiv ℝ
            (fun y ↦ flatDbar (fun y ↦ D.reading k x (s k) y / peakFunction k y) y b) z‖ ≤
          C * (k : ℝ) ^ (-1 / 2 : ℝ) * ‖b‖ := by
  obtain ⟨B, hB⟩ := IsAsymptoticallyHolomorphic.exists_forall_jetNormAt_le D hg hJ hα hρ₀ hs
    (11 / 10) 2
  obtain ⟨A, hA, C, hC⟩ := D.exists_forall_norm_reading_div_peakFunction_le hρ₀ B
  refine ⟨A, hA, C, ?_⟩
  filter_upwards [hB, hC] with k hBk hCk x
  refine hCk x (s k) fun z hz ↦ ?_
  obtain ⟨hf, -, hfB, hdB⟩ := hBk x z hz
  exact ⟨hf.of_le (by simp), hfB,
    (jetNormAt_mono _ z (by norm_num)).trans hdB⟩
omit [I.Boundaryless] in
/-- **A lower bound on the quotient by the Gaussian gives the transversality quantity.** Let the
metric of `M` be `g(u, w) = σ(u, J w)`, and `ρ₀ > 0`. For every `ε` and `B`, for all large `k`,
every centre `x`, every section `s` of `PowerBundle P k`, every `q : StdSpace ι → ℂ` and every `z`
with `‖z‖ ≤ 1`: if the reading of `s` agrees near `z` with `q * exp (-‖·‖ ^ 2 / 4)`, `q` is
differentiable at `z`, the connection read in the chart has operator norm at most `B` at `z`, and
`ε ≤ max ‖q z‖ ‖∂q(z)‖`, for `∂q(z) = flatDel q z` the flat `∂` of `q` at `z`, then at
`y = (D.chart k x).symm z`,
`ε / 4 ≤ max ‖s y‖ ((2π k)^(-1/2) ‖∂ s(y)‖)`, where `∂ s(y)` is the `(1,0)`-part
`J.oneZeroPart` of `D_k s` at `y`, with its operator norm. -/
theorem eventually_div_four_le_max_of_reading_eventuallyEq_mul_gaussian
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [∀ y, Nonempty (P y)]
    (hg : ∀ (y : M) (v w : TangentSpace I y), inner ℝ v w = σ.eval₂ y v (J y w))
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (ε B : ℝ) :
    ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M) (s : Π y, PowerBundle P k y) (q : StdSpace ι → ℂ)
      (z : StdSpace ι), ‖z‖ ≤ 1 →
      D.reading k x s =ᶠ[𝓝 z] (fun y ↦ q y * Real.exp (-‖y‖ ^ 2 / 4)) →
      DifferentiableAt ℝ q z → ‖D.connectionReading k x s z‖ ≤ B →
      ε ≤ max ‖q z‖ ‖flatDel q z‖ →
      ε / 4 ≤ max ‖s ((D.chart k x).symm z)‖ ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) *
        ‖J.oneZeroPart (powerConnection α k s ((D.chart k x).symm z))‖) := by
  rcases le_or_gt ε 0 with hε | hε
  · exact Filter.Eventually.of_forall fun k x s _ _ _ _ _ _ _ ↦
      (by linarith : ε / 4 ≤ 0).trans (le_max_of_le_left (norm_nonneg _))
  set C := max (D.bound 1) 0
  set B' := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hB' : 0 ≤ B' := le_max_right _ _
  have hsqrt := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [Filter.eventually_ge_atTop k₀,
    (hsqrt.const_mul_atTop hρ₀).eventually_gt_atTop 1, hsqrt.eventually_gt_atTop (4 * C),
    hsqrt.eventually_gt_atTop (8 * C * B' / ε)] with k hk hkρ hk4 hk8 x s q z hz hfeq hq hB hmax
  simp only [Function.comp_apply] at hkρ hk4 hk8
  have hk0 : 0 < √(k : ℝ) := hC.trans_lt (by linarith)
  have hzb : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k) := mem_ball_zero_iff.2 (hz.trans_lt hkρ)
  have hGd : DifferentiableAt ℝ (fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ)) z :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_gaussian :
      ContDiff ℝ 1 fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ))).differentiable
      one_ne_zero z
  have hs : DifferentiableAt ℝ (D.reading k x s) z := (hq.mul hGd).congr_of_eventuallyEq hfeq
  set G := Real.exp (-‖z‖ ^ 2 / 4)
  set a := ‖q z‖
  set b := ‖flatDel q z‖
  have ha : 0 ≤ a := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  -- On the closed unit ball the Gaussian is at least `3 / 4`.
  have hG : 3 / 4 ≤ G := by
    have := Real.add_one_le_exp (-‖z‖ ^ 2 / 4)
    nlinarith
  rcases le_or_gt (ε / 2) a with hqz | hqz
  · -- The section itself is large.
    refine le_max_of_le_left ?_
    rw [← norm_reading, hfeq.eq_of_nhds, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    nlinarith
  · -- Its `∂` is large: compare the two bounds on the model `∂` of the reading.
    refine le_max_of_le_right ?_
    have hb : ε ≤ b := by
      rcases le_max_iff.1 hmax with h | h
      · linarith
      · exact h
    have hlow := mul_sub_le_norm_modelDel_mul_gaussian hq
    rw [modelDel_def, ← modelConnection_congr_of_eventuallyEq hfeq, ← modelDel_def] at hlow
    have hup := D.norm_modelDel_reading_le_of_inner_eq hg hα hk hzb hs
    set t := C * ‖z‖ / √k
    set X := (2 * Real.pi * k) ^ (-1 / 2 : ℝ) *
      ‖J.oneZeroPart (powerConnection α k s ((D.chart k x).symm z))‖
    set N := ‖D.connectionReading k x s z‖
    have hX : 0 ≤ X := by positivity
    have hN : N ≤ B' := hB.trans (le_max_left _ _)
    have htk : t * √k = C * ‖z‖ := div_mul_cancel₀ _ hk0.ne'
    have ht0 : 0 ≤ t := by positivity
    have ht1 : 4 * t ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hk0
      nlinarith
    have ht2 : 8 * (t * N) ≤ ε := by
      rw [div_lt_iff₀ hε] at hk8
      refine le_of_mul_le_mul_right ?_ hk0
      have : C * ‖z‖ * N ≤ C * B' := by
        calc C * ‖z‖ * N ≤ C * 1 * B' := by gcongr
          _ = C * B' := by ring
      nlinarith
    have hlow' : 9 / 16 * ε ≤ G * (b - ‖z‖ * a / 2) := by
      have : ‖z‖ * a ≤ a := by nlinarith
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ht1 hX]

end RescaledUnitaryCharts

end SymplecticGeometry

end
