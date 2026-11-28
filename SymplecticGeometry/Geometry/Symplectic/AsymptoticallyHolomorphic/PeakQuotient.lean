/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakFunction
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartTransition

/-!
# Quotients by the cut-off Gaussian and their flat `∂̄`

To correct a section near a point `x`, its reading `f` in the chart centred at `x` is divided by
the cut-off Gaussian `SymplecticGeometry.peakFunction k`. On a ball of fixed radius `R`, and for
`k` so large that `R < k ^ (1 / 6)`, the cut-off is `1` and the quotient is
`q = f * exp (‖z‖ ^ 2 / 4)`. This file bounds the jets of `q` and of its flat `∂̄` there, with
constants that depend only on the order and on `R`.

The Gaussian `G = exp (-‖z‖ ^ 2 / 4)` has model `∂̄` zero (`modelDbar_gaussian`), so by the
Leibniz rule `modelDbar_mul` the model `∂̄` of `f = q * G` for the constant structure `J₀` is
`G • flatDbar q`. For a field `J` of structures, `modelDbarWith_eq_add` writes the model `∂̄`
of `f` for `J` as the one for `J₀` plus `(i / 2) ∇f ∘ (J - J₀)`, with `∇f` the model connection
`modelConnection f`. Hence
`flatDbar q = exp (‖z‖ ^ 2 / 4) • (modelDbarWith J f - (i / 2) ∇f ∘ (J - J₀))`
(`SymplecticGeometry.flatDbar_mul_exp_eq`), and the jet bounds follow from the Leibniz bounds
for jet norms.

## Main results

* `SymplecticGeometry.contDiff_ofReal_exp_norm_sq_div_four`,
  `SymplecticGeometry.exists_jetNormAt_ofReal_exp_norm_sq_div_four_le`: the inverse Gaussian is
  smooth, and its jet norms are bounded on closed balls.
* `SymplecticGeometry.flatDbar_mul_exp_eq`: the identity above, at every point where `f` is
  differentiable.
* `SymplecticGeometry.div_peakFunction_eventuallyEq`: near a point of the ball of radius
  `k ^ (1 / 6)`, `f / peakFunction k` is `f * exp (‖z‖ ^ 2 / 4)`.
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

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  proof of Proposition 2
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

open Metric TauCeti ContinuousLinearMap
open scoped Topology Manifold ContDiff

namespace SymplecticGeometry

section InverseGaussian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The inverse Gaussian `exp (‖z‖ ^ 2 / 4)`, as a complex function, is smooth. -/
theorem contDiff_ofReal_exp_norm_sq_div_four {n : ℕ∞} :
    ContDiff ℝ n fun z : F ↦ (Real.exp (‖z‖ ^ 2 / 4) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const 4))

/-- On a closed ball, the jet norms of the inverse Gaussian `exp (‖·‖ ^ 2 / 4)` are bounded. -/
theorem exists_jetNormAt_ofReal_exp_norm_sq_div_four_le [ProperSpace F] (r : ℕ) (R : ℝ) :
    ∃ A, ∀ z : F, ‖z‖ ≤ R → jetNormAt ℝ r (fun y : F ↦ (Real.exp (‖y‖ ^ 2 / 4) : ℂ)) z ≤ A := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    (continuous_jetNormAt (contDiff_ofReal_exp_norm_sq_div_four (n := r))).continuousOn
  exact ⟨A, fun z hz ↦ (le_abs_self _).trans (hA z (mem_closedBall_zero_iff.2 hz))⟩

end InverseGaussian

variable {ι : Type*} [Fintype ι]

/-- **The flat `∂̄` of the quotient by the Gaussian.** For a field `J` of real-linear
endomorphisms of `StdSpace ι` and `f` differentiable at `w`, the flat `∂̄` of
`q = f * exp (‖·‖ ^ 2 / 4)` at `w` is `exp (‖w‖ ^ 2 / 4)` times the model `∂̄` of `f` for `J`
minus `(i / 2) ∇f ∘ (J w - J₀)`, for `∇f` the model connection of `f` at `w`. -/
theorem flatDbar_mul_exp_eq (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) {f : StdSpace ι → ℂ}
    {w : StdSpace ι} (hf : DifferentiableAt ℝ f w) :
    flatDbar (fun y ↦ f y * Real.exp (‖y‖ ^ 2 / 4)) w =
      (Real.exp (‖w‖ ^ 2 / 4) : ℂ) • (modelDbarWith J f w -
        (((2⁻¹ : ℂ) * Complex.I) • modelConnection f w).comp
          (J w - LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)) := by
  set E : StdSpace ι → ℂ := fun y ↦ Real.exp (‖y‖ ^ 2 / 4)
  set G : StdSpace ι → ℂ := fun y ↦ Real.exp (-‖y‖ ^ 2 / 4)
  have hEG (y : StdSpace ι) : E y * G y = 1 := by
    simp only [E, G, ← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
    simp
  have hq : DifferentiableAt ℝ (fun y ↦ f y * E y) w :=
    hf.mul ((contDiff_ofReal_exp_norm_sq_div_four (n := 1)).differentiable one_ne_zero w)
  have hG : DifferentiableAt ℝ G w :=
    ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
      ((contDiff_norm_sq ℝ).neg.div_const 4)) : ContDiff ℝ 1 G)).differentiable one_ne_zero w
  have hf' : f = fun y ↦ (f y * E y) * G y := by
    funext y
    rw [mul_assoc, hEG, mul_one]
  have hmodel : modelDbar f w = G w • flatDbar (fun y ↦ f y * E y) w := by
    conv_lhs => rw [hf']
    have h0 : modelDbar G w = 0 := by rw [modelDbar_gaussian, Pi.zero_apply]
    rw [modelDbar_mul hq hG, h0]
    ext v
    simp
  rw [modelDbarWith_eq_add J
    (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) f w,
    ← modelDbar_def, hmodel, add_sub_cancel_right, smul_smul,
    show (Real.exp (‖w‖ ^ 2 / 4) : ℂ) * G w = 1 from hEG w, one_smul]

/-- Near a point of the ball of radius `k ^ (1 / 6)`, where the cut-off Gaussian is the Gaussian,
the quotient of `f` by `peakFunction k` is `f * exp (‖·‖ ^ 2 / 4)`. -/
theorem div_peakFunction_eventuallyEq {E : Type*} [NormedAddCommGroup E] (k : ℕ) (f : E → ℂ)
    {z : E} (hz : ‖z‖ < (k : ℝ) ^ (1 / 6 : ℝ)) :
    (fun y ↦ f y / peakFunction k y) =ᶠ[𝓝 z] fun y ↦ f y * Real.exp (‖y‖ ^ 2 / 4) := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with y hy
  rw [peakFunction_eqOn_ball k hy, div_eq_mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg, neg_div,
    neg_neg]

/-- **Jets of the quotient by the cut-off Gaussian.** For every order `r` and radius `R` there is
a constant `C` such that, for every `k` with `R < k ^ (1 / 6)`, every `f` and every `z` with
`‖z‖ ≤ R` where `f` is `C^r`, the `r`-jet norm of `f / peakFunction k` at `z` is at most `C` times
that of `f`. -/
theorem exists_jetNormAt_div_peakFunction_le (r : ℕ) (R : ℝ) :
    ∃ C, ∀ (k : ℕ) (f : StdSpace ι → ℂ) {z : StdSpace ι}, ‖z‖ ≤ R →
      R < (k : ℝ) ^ (1 / 6 : ℝ) → ContDiffAt ℝ r f z →
      jetNormAt ℝ r (fun y ↦ f y / peakFunction k y) z ≤ C * jetNormAt ℝ r f z := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_ofReal_exp_norm_sq_div_four_le (F := StdSpace ι) r R
  refine ⟨2 ^ r * A, fun k f z hz hk hf ↦ ?_⟩
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
        · exact hA z hz

/-- **Jets of the flat `∂̄` of the quotient by the cut-off Gaussian.** For every order `r` and
radius `R` there is a constant `C` such that, for every `k` with `R < k ^ (1 / 6)`, every field
`J` of real-linear endomorphisms of `StdSpace ι`, every `f` and every `z` with `‖z‖ ≤ R` where `f`
is `C^(r + 1)` and `J` is `C^r`, the `r`-jet norm at `z` of the flat `∂̄` of `f / peakFunction k`
is at most `C` times the `r`-jet norm of the model `∂̄` of `f` for `J` plus the product of the
`r`-jet norm of `J - J₀` and the `(r + 1)`-jet norm of `f`. -/
theorem exists_jetNormAt_flatDbar_div_peakFunction_le (r : ℕ) (R : ℝ) :
    ∃ C, ∀ (k : ℕ) (J : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι) (f : StdSpace ι → ℂ)
      {z : StdSpace ι}, ‖z‖ ≤ R → R < (k : ℝ) ^ (1 / 6 : ℝ) →
      ContDiffAt ℝ (r + 1 : ℕ) f z → ContDiffAt ℝ r J z →
      jetNormAt ℝ r (flatDbar fun y ↦ f y / peakFunction k y) z ≤
        C * (jetNormAt ℝ r (modelDbarWith J f) z +
          jetNormAt ℝ r (fun w ↦ J w -
              LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) z *
            jetNormAt ℝ (r + 1) f z) := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_ofReal_exp_norm_sq_div_four_le (F := StdSpace ι) r R
  obtain ⟨C₁, hC₁⟩ := exists_jetNormAt_modelConnection_le (ι := ι) r
  set J₀ := LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap
  -- Instance search does not find the operator norm on this space of bilinear maps unaided.
  let : NormedAddCommGroup ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] StdSpace ι →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup ((StdSpace ι →L[ℝ] ℂ) →L[ℝ] (StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ]
      StdSpace ι →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ ((StdSpace ι →L[ℝ] ℂ) →L[ℝ] (StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ]
      StdSpace ι →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
  set B := compL ℝ (StdSpace ι) (StdSpace ι) ℂ
  set c : ℂ := 2⁻¹ * Complex.I
  set K := 2 ^ r * ‖B‖ * ‖c‖ * (|C₁| * (1 + |R|))
  refine ⟨2 ^ r * |A| * (1 + K), fun k J f z hz hk hf hJ ↦ ?_⟩
  set E : StdSpace ι → ℂ := fun y ↦ Real.exp (‖y‖ ^ 2 / 4)
  have hE : ContDiffAt ℝ r E z := contDiff_ofReal_exp_norm_sq_div_four.contDiffAt
  have hf1 : ContDiffAt ℝ (r + 1) f z := by exact_mod_cast hf
  -- The quotient's flat `∂̄` near `z`, by `flatDbar_mul_exp_eq`.
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ f w :=
    (hf.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by simp)
  have hq : flatDbar (fun y ↦ f y / peakFunction k y) =ᶠ[𝓝 z]
      fun w ↦ E w • (modelDbarWith J f w + -(c • B (modelConnection f w) (J w - J₀))) := by
    have h1 := (div_peakFunction_eventuallyEq k f (hz.trans_lt hk)).eventually_nhds
    filter_upwards [h1, hdiff] with w hw hfw
    rw [flatDbar_def, flatDbarWith_congr_of_eventuallyEq hw, ← flatDbar_def,
      flatDbar_mul_exp_eq J hfw, sub_eq_add_neg]
    simp only [B, compL_apply, smul_comp, c, E, J₀]
  rw [jetNormAt_congr_of_eventuallyEq r hq]
  have hM : ContDiffAt ℝ r (modelConnection f) z := contDiffAt_modelConnection hf1
  have hJ' : ContDiffAt ℝ r (fun w ↦ J w - J₀) z := hJ.sub contDiffAt_const
  have hT : ContDiffAt ℝ r (fun w ↦ c • B (modelConnection f w) (J w - J₀)) z :=
    ((B.contDiff.contDiffAt.comp z hM).clm_apply hJ').const_smul c
  have hD : ContDiffAt ℝ r (modelDbarWith J f) z := contDiffAt_modelDbarWith hJ hf1
  have hsum := jetNormAt_add_le hD hT.neg
  rw [show jetNormAt ℝ r (fun w ↦ -(c • B (modelConnection f w) (J w - J₀))) z =
      jetNormAt ℝ r (fun w ↦ c • B (modelConnection f w) (J w - J₀)) z from
    jetNormAt_neg r _ z] at hsum
  have hTle : jetNormAt ℝ r (fun w ↦ c • B (modelConnection f w) (J w - J₀)) z ≤
      K * (jetNormAt ℝ r (fun w ↦ J w - J₀) z * jetNormAt ℝ (r + 1) f z) := by
    have hs : (fun w ↦ c • B (modelConnection f w) (J w - J₀)) =
        c • fun w ↦ B (modelConnection f w) (J w - J₀) := by
      ext1 w
      rw [Pi.smul_apply]
    rw [hs, jetNormAt_smul]
    have hb := jetNormAt_bilinear_le B hM hJ'
    have hm := hC₁ f hf
    have h1 : C₁ * (1 + ‖z‖) ≤ |C₁| * (1 + |R|) := by
      have : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
      calc C₁ * (1 + ‖z‖) ≤ |C₁| * (1 + ‖z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C₁| * (1 + |R|) := by gcongr
    have hm' : jetNormAt ℝ r (modelConnection f) z ≤
        |C₁| * (1 + |R|) * jetNormAt ℝ (r + 1) f z :=
      hm.trans (mul_le_mul_of_nonneg_right h1 (jetNormAt_nonneg _ _ _))
    have := jetNormAt_nonneg (𝕜 := ℝ) r (fun w ↦ J w - J₀) z
    have := jetNormAt_nonneg (𝕜 := ℝ) (r + 1) f z
    have := jetNormAt_nonneg (𝕜 := ℝ) r (modelConnection f) z
    have := norm_nonneg B
    have := norm_nonneg c
    calc ‖c‖ * jetNormAt ℝ r (fun w ↦ B (modelConnection f w) (J w - J₀)) z
        ≤ ‖c‖ * (2 ^ r * ‖B‖ * jetNormAt ℝ r (modelConnection f) z *
            jetNormAt ℝ r (fun w ↦ J w - J₀) z) := by gcongr
      _ ≤ ‖c‖ * (2 ^ r * ‖B‖ * (|C₁| * (1 + |R|) * jetNormAt ℝ (r + 1) f z) *
            jetNormAt ℝ r (fun w ↦ J w - J₀) z) := by gcongr
      _ = _ := by simp only [K]; ring
  have hK : 0 ≤ K := by positivity
  have hP := jetNormAt_fun_smul_le hE (hD.add hT.neg)
  have hAz : jetNormAt ℝ r E z ≤ |A| := (hA z hz).trans (le_abs_self A)
  set a := jetNormAt ℝ r (modelDbarWith J f) z
  set b := jetNormAt ℝ r (fun w ↦ J w - J₀) z * jetNormAt ℝ (r + 1) f z
  have ha : 0 ≤ a := jetNormAt_nonneg _ _ _
  have hb : 0 ≤ b := mul_nonneg (jetNormAt_nonneg _ _ _) (jetNormAt_nonneg _ _ _)
  calc _ ≤ 2 ^ r * jetNormAt ℝ r E z *
        jetNormAt ℝ r (fun w ↦ modelDbarWith J f w + -(c • B (modelConnection f w) (J w - J₀)))
          z := hP
    _ ≤ 2 ^ r * |A| * (a + K * b) := by
        gcongr
        · exact jetNormAt_nonneg _ _ _
        · exact hsum.trans (add_le_add le_rfl hTle)
    _ ≤ 2 ^ r * |A| * (1 + K) * (a + b) := by
        have : a + K * b ≤ (1 + K) * (a + b) := by nlinarith
        calc 2 ^ r * |A| * (a + K * b) ≤ 2 ^ r * |A| * ((1 + K) * (a + b)) := by gcongr
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
`R` there is a constant `C` such that, for rescaled unitary charts of radius `ρ₀ > 0`, for all
large `k`, every centre `x`, every section `s` of `PowerBundle P k` and every `z` with `‖z‖ ≤ R`
where the reading `f` of `s` is `C^(r + 1)`, the
`r`-jet norm at `z` of the flat `∂̄` of `f / peakFunction k` is at most `C` times the `r`-jet norm
of the `∂̄` reading of `s` plus `k ^ (-1 / 2)` times the `(r + 1)`-jet norm of `f`. -/
theorem exists_jetNormAt_flatDbar_reading_div_peakFunction_le (hρ₀ : 0 < ρ₀) (r : ℕ) (R : ℝ) :
    ∃ C, ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M) (s : Π y, PowerBundle P k y) {z : StdSpace ι},
      ‖z‖ ≤ R → ContDiffAt ℝ (r + 1 : ℕ) (D.reading k x s) z →
      jetNormAt ℝ r (flatDbar fun y ↦ D.reading k x s y / peakFunction k y) z ≤
        C * (jetNormAt ℝ r (D.dbarReading k x s) z +
          (k : ℝ) ^ (-1 / 2 : ℝ) * jetNormAt ℝ (r + 1) (D.reading k x s) z) := by
  obtain ⟨C, hC⟩ := exists_jetNormAt_flatDbar_div_peakFunction_le (ι := ι) r R
  obtain ⟨C₀, hC₀⟩ := D.exists_jetNormAt_chartPushforward_sub_le r
  set C' := |C₀| * (1 + |R|)
  have h6 : ∀ᶠ k : ℕ in Filter.atTop, R < (k : ℝ) ^ (1 / 6 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop R
  have hρ : ∀ᶠ k : ℕ in Filter.atTop, R < ρ₀ * √k :=
    (((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ₀).eventually_gt_atTop R)
  refine ⟨|C| * (1 + |C'|), ?_⟩
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
  have hj0 : 0 ≤ j := jetNormAt_nonneg _ _ _
  have ht : 0 ≤ t := by positivity
  have hz' : 1 + ‖z‖ ≤ 1 + |R| := by linarith [le_abs_self R]
  have hj' : j ≤ |C'| * t := by
    refine hj.trans ?_
    rw [abs_of_nonneg (by positivity : 0 ≤ C')]
    calc C₀ * t * (1 + ‖z‖) ≤ |C₀| * t * (1 + |R|) := by gcongr; exact le_abs_self _
      _ = C' * t := by ring
  calc C * (a + j * b) ≤ |C| * (a + j * b) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C| * (a + |C'| * t * b) := by gcongr
    _ ≤ |C| * (1 + |C'|) * (a + t * b) := by
        have : a + |C'| * t * b ≤ (1 + |C'|) * (a + t * b) := by
          nlinarith [abs_nonneg C', mul_nonneg ht hb]
        calc |C| * (a + |C'| * t * b) ≤ |C| * ((1 + |C'|) * (a + t * b)) := by gcongr
          _ = _ := by ring

end RescaledUnitaryCharts

end SymplecticGeometry

end
