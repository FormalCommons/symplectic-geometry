/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakSection
public import Mathlib.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.LocalTransversality
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakQuotient

/-!
# Global uniform transversality: the local correction

Let `D` be rescaled unitary charts of radius `ρ₀ > 0` for `(σ, J)` and a connection form `α`, and
let `M` carry the metric `σ(·, J ·)`. This file corrects a section `s` of `PowerBundle P k` on
one ball, of radius one in the chart centred at `x`, so that it becomes transverse there in the
quantitative sense of `SymplecticGeometry.IsUniformlyTransverse`.

The correction is an affine combination of peak sections,
`D.affinePeakSection k x w = w₀ • peakSection k x + Σ_j w_j • peakSection_mul k x j` for
`w = (w₀, w₁, …, wₙ)`; its reading in the chart at `x` is `(w₀ + Σ_j w_j z_j)` times the cut-off
Gaussian (`RescaledUnitaryCharts.reading_affinePeakSection`).

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.exists_local_correction`: for every bound `B` there
  are an exponent `p > 0` and `δ₀ > 0` such that, for `0 < δ < δ₀` and `ε = δ / log (1 / δ) ^ p`,
  for all large `k`, every centre `x` and every section `s` whose reading is `C²` on the ball of
  radius `11 / 10` with `2`-jet norm at most `B` and with `∂̄` reading of `1`-jet norm at most
  `B * k ^ (-1 / 2)`, some `w` with `‖w‖ ≤ δ` makes `t = s - D.affinePeakSection k x w` satisfy
  `ε / 4 ≤ max ‖t y‖ ((2π k)^(-1/2) ‖∂ t(y)‖)` at every point `y` of the image of the closed unit
  ball. The constants are chosen in the order that the iteration over colours needs: `δ` first,
  then `k`, uniformly in `x` and `s`.

The proof divides the reading of `s` by the cut-off Gaussian, which meets the hypotheses of the
local transversality estimate (`exists_forall_norm_reading_div_peakFunction_le`); the estimate
`SymplecticGeometry.exists_norm_le_max_ge_of_flatDbar_le` gives `w`; the reading of the corrected
section is then the corrected quotient times the Gaussian near the closed unit ball, and
`eventually_div_four_le_max_of_reading_eventuallyEq_mul_gaussian` carries the lower bound back to
the section.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Theorem 1 and the proof of Proposition 2
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

open Metric TauCeti Bundle
open scoped Topology Manifold ContDiff

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- The **affine combination of peak sections** at `x` with coefficients
`w = (w₀, w₁, …, wₙ)`, indexed by `Option ι` with `w₀ = w none`:
`w₀ • D.peakSection k x + Σ_j w_j • D.peakSection_mul k x j`. -/
noncomputable def affinePeakSection (k : ℕ) (x : M) (w : EuclideanSpace ℂ (Option ι)) :
    Π y, PowerBundle P k y :=
  w none • D.peakSection k x + ∑ j, w (some j) • D.peakSection_mul k x j

theorem affinePeakSection_def (k : ℕ) (x : M) (w : EuclideanSpace ℂ (Option ι)) :
    D.affinePeakSection k x w =
      w none • D.peakSection k x + ∑ j, w (some j) • D.peakSection_mul k x j :=
  (rfl)

/-- For `k₀ ≤ k`, the reading of `D.affinePeakSection k x w` in the chart at `x` is
`(w₀ + Σ_j w_j z_j)` times the cut-off Gaussian on the ball of radius `ρ₀ * √k`, for
`z_j = (complexToRealEuclidean ι).symm z j`. -/
theorem reading_affinePeakSection {k : ℕ} (hk : k₀ ≤ k) (x : M)
    (w : EuclideanSpace ℂ (Option ι)) :
    Set.EqOn (D.reading k x (D.affinePeakSection k x w))
      (fun z ↦ (w none + ∑ j, w (some j) * (complexToRealEuclidean ι).symm z j) *
        peakFunction k z) (ball 0 (ρ₀ * √k)) := by
  intro z hz
  simp only [affinePeakSection_def, reading_add, reading_smul, reading_sum, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, D.reading_peakSection hk x hz,
    D.reading_peakSection_mul hk x _ hz, peakFunction_mul_def, add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The reading of a section corrected by peak sections.** For `k₀ ≤ k` and `z` in the balls of
radii `ρ₀ * √k` and `k ^ (1 / 6)`, near `z` the reading of `s - D.affinePeakSection k x w` in the
chart at `x` is `q - w₀ - Σ_j w_j z_j` times the Gaussian `exp (-‖·‖ ^ 2 / 4)`, for `q` the
quotient of the reading of `s` by the cut-off Gaussian `peakFunction k`. -/
theorem reading_sub_affinePeakSection_eventuallyEq {k : ℕ} (hk : k₀ ≤ k) (x : M)
    (s : Π y, PowerBundle P k y) (w : EuclideanSpace ℂ (Option ι)) {z : StdSpace ι}
    (hzρ : ‖z‖ < ρ₀ * √k) (hz6 : ‖z‖ < (k : ℝ) ^ (1 / 6 : ℝ)) :
    D.reading k x (s - D.affinePeakSection k x w) =ᶠ[𝓝 z]
      fun y ↦ (D.reading k x s y / peakFunction k y - w none -
        ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j) * Real.exp (-‖y‖ ^ 2 / 4) := by
  have hzU : z ∈ ball (0 : StdSpace ι) (min (ρ₀ * √k) ((k : ℝ) ^ (1 / 6 : ℝ))) :=
    mem_ball_zero_iff.2 (lt_min hzρ hz6)
  filter_upwards [isOpen_ball.mem_nhds hzU] with y hy
  have hy₁ : y ∈ ball (0 : StdSpace ι) (ρ₀ * √k) := ball_subset_ball (min_le_left _ _) hy
  have hy₂ : y ∈ ball (0 : StdSpace ι) ((k : ℝ) ^ (1 / 6 : ℝ)) :=
    ball_subset_ball (min_le_right _ _) hy
  have hp : peakFunction k y = (Real.exp (-‖y‖ ^ 2 / 4) : ℂ) := peakFunction_eqOn_ball k hy₂
  rw [reading_sub, Pi.sub_apply, D.reading_affinePeakSection hk x w hy₁]
  simp only [hp]
  field_simp
  ring

/-- The connection read at a point `z` of the closed unit ball of a section corrected by peak
sections, with `‖w‖ ≤ 1`, is bounded in terms of bounds `A` on the quotient `q` of the reading of
`s` by the cut-off Gaussian and on its differential at `z`. -/
private theorem norm_connectionReading_sub_affinePeakSection_le {k : ℕ} (hk : k₀ ≤ k) (x : M)
    (s : Π y, PowerBundle P k y) {w : EuclideanSpace ℂ (Option ι)} (hw : ‖w‖ ≤ 1)
    {z : StdSpace ι} (hz : ‖z‖ ≤ 1) (hzρ : ‖z‖ < ρ₀ * √k)
    (hz6 : ‖z‖ < (k : ℝ) ^ (1 / 6 : ℝ)) {A : ℝ}
    (hqd : DifferentiableAt ℝ (fun y ↦ D.reading k x s y / peakFunction k y) z)
    (hqA : ‖D.reading k x s z / peakFunction k z‖ ≤ A)
    (hdqA : ‖fderiv ℝ (fun y ↦ D.reading k x s y / peakFunction k y) z‖ ≤ A) :
    ‖D.connectionReading k x (s - D.affinePeakSection k x w) z‖ ≤
      2 * A + 1 + 2 * Fintype.card ι := by
  set q := fun y ↦ D.reading k x s y / peakFunction k y
  set L : StdSpace ι →L[ℝ] ℂ := ∑ j, w (some j) • complexToRealEuclideanCoord ι j
  have hL (y : StdSpace ι) :
      L y = ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j := by
    simp [L]
  have hw' (i : Option ι) : ‖w i‖ ≤ 1 := (PiLp.norm_apply_le w i).trans hw
  set qw := fun y ↦ q y - w none - ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j
  have hqw : HasFDerivAt qw (fderiv ℝ q z - L) z := by
    have h := hqd.hasFDerivAt.sub (L.hasFDerivAt.const_add (w none))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_))
    simp only [qw, hL, Pi.sub_apply, sub_sub]
  -- Bounds on the corrected quotient and on its differential.
  have hLz : ‖L z‖ ≤ Fintype.card ι := by
    rw [hL]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖w (some j) * (complexToRealEuclidean ι).symm z j‖ ≤ ∑ _j : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [norm_mul]
            exact (mul_le_mul (hw' _) ((norm_complexToRealEuclidean_symm_apply_le z j).trans hz)
              (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = Fintype.card ι := by simp
  have hLn : ‖L‖ ≤ Fintype.card ι := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖w (some j) • complexToRealEuclideanCoord ι j‖ ≤ ∑ _j : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [norm_smul]
            exact (mul_le_mul (hw' _) (norm_complexToRealEuclideanCoord_le j) (norm_nonneg _)
              zero_le_one).trans_eq (one_mul 1)
      _ = Fintype.card ι := by simp
  have hqwz : ‖qw z‖ ≤ A + 1 + Fintype.card ι := by
    have : qw z = q z - w none - L z := by simp only [qw, hL]
    rw [this]
    have := norm_sub_le (q z - w none) (L z)
    have := norm_sub_le (q z) (w none)
    linarith [hw' none]
  have hdqw : ‖fderiv ℝ qw z‖ ≤ A + Fintype.card ι := by
    rw [hqw.fderiv]
    exact (norm_sub_le _ _).trans (add_le_add hdqA hLn)
  have hb := norm_modelConnection_mul_gaussian_le hqw.differentiableAt
  rw [← modelConnection_congr_of_eventuallyEq
    (D.reading_sub_affinePeakSection_eventuallyEq hk x s w hzρ hz6), ← connectionReading_def] at hb
  have hG1 : Real.exp (-‖z‖ ^ 2 / 4) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := sq_nonneg ‖z‖
    linarith)
  have hzq : ‖z‖ * ‖qw z‖ / 2 ≤ ‖qw z‖ := by nlinarith [norm_nonneg z, norm_nonneg (qw z)]
  have hsum : 0 ≤ ‖fderiv ℝ qw z‖ + ‖z‖ * ‖qw z‖ / 2 := by positivity
  nlinarith [Real.exp_pos (-‖z‖ ^ 2 / 4)]

/-- **The local correction.** Let the metric of `M` be `g(u, w) = σ(u, J w)`, let `α` be a
connection form and `ρ₀ > 0`. For every bound `B` there are an exponent `p > 0` and `δ₀ > 0`
such that, for `0 < δ < δ₀` and `ε = δ / log (1 / δ) ^ p`, the following holds for all large
`k`, every centre `x` and every section `s` of `PowerBundle P k` whose reading in the chart at
`x` is, at each point of the ball of radius `11 / 10`, `C²` with `2`-jet norm at most `B`, and
whose `∂̄` reading has `1`-jet norm at most `B * k ^ (-1 / 2)` there. Some `w ∈ ℂⁿ⁺¹` with
`‖w‖ ≤ δ` makes the corrected section `t = s - D.affinePeakSection k x w` satisfy
`ε / 4 ≤ max ‖t y‖ ((2π k)^(-1/2) ‖∂ t(y)‖)` at `y = (D.chart k x).symm z` for every `z` of the
closed unit ball, where `∂ t(y)` is the `(1,0)`-part `J.oneZeroPart` of `D_k t` at `y`, with its
operator norm. -/
theorem exists_local_correction [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [∀ y, Nonempty (P y)]
    (hg : ∀ (y : M) (v w : TangentSpace I y), inner ℝ v w = σ.eval₂ y v (J y w))
    (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (B : ℝ) :
    ∃ p : ℕ, 0 < p ∧ ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M) (s : Π y, PowerBundle P k y),
        (∀ z ∈ ball (0 : StdSpace ι) (11 / 10), ContDiffAt ℝ 2 (D.reading k x s) z ∧
          jetNormAt ℝ 2 (D.reading k x s) z ≤ B ∧
          jetNormAt ℝ 1 (D.dbarReading k x s) z ≤ B * (k : ℝ) ^ (-1 / 2 : ℝ)) →
        ∃ w : EuclideanSpace ℂ (Option ι), ‖w‖ ≤ δ ∧ ∀ z ∈ closedBall (0 : StdSpace ι) 1,
          δ / Real.log (1 / δ) ^ p / 4 ≤
            max ‖(s - D.affinePeakSection k x w) ((D.chart k x).symm z)‖
              ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart
                (powerConnection α k (s - D.affinePeakSection k x w) ((D.chart k x).symm z))‖) := by
  obtain ⟨A, hA, C, hC⟩ := D.exists_forall_norm_reading_div_peakFunction_le hρ₀ B
  obtain ⟨p, hp, δ₀, hδ₀, H⟩ := exists_norm_le_max_ge_of_flatDbar_le (ι := ι) hA
  refine ⟨p, hp, min δ₀ (1 / 2), lt_min hδ₀ (by norm_num), fun δ hδ hδδ₀ ↦ ?_⟩
  have hδ1 : δ < 1 / 2 := hδδ₀.trans_le (min_le_right _ _)
  set ε := δ / Real.log (1 / δ) ^ p
  have hε : 0 < ε := by
    refine div_pos hδ (pow_pos (Real.log_pos ?_) _)
    rw [one_div]
    exact (one_lt_inv₀ hδ).2 (by linarith)
  have hCk : ∀ᶠ k : ℕ in Filter.atTop, C * (k : ℝ) ^ (-1 / 2 : ℝ) ≤ ε := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul C
    rw [mul_zero] at h
    filter_upwards [h.eventually (eventually_le_nhds hε)] with k hk
    simpa [neg_div] using hk
  have h6 : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) < (k : ℝ) ^ (1 / 6 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop 1
  have hρ : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) < ρ₀ * √k :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ₀).eventually_gt_atTop 1
  filter_upwards [hC, hCk, D.eventually_div_four_le_max_of_reading_eventuallyEq_mul_gaussian hg
    hα hρ₀ ε (2 * A + 1 + 2 * Fintype.card ι), Filter.eventually_ge_atTop k₀, h6, hρ]
    with k hCk' hck hDk hk hk6 hkρ x s hs
  have hq := hCk' x s hs
  -- The local transversality estimate applies to the quotient by the cut-off Gaussian.
  obtain ⟨w, hw, hwz⟩ := H δ hδ (hδδ₀.trans_le (min_le_left _ _)) _
    (fun z hz ↦ (hq z hz).1) (fun z hz ↦ ⟨(hq z hz).2.1, (hq z hz).2.2.1⟩)
    (fun z hz ↦ ⟨(hq z hz).2.2.2.1.trans hck, fun b ↦ ((hq z hz).2.2.2.2 b).trans
      (mul_le_mul_of_nonneg_right hck (norm_nonneg b))⟩)
  refine ⟨w, hw, fun z hz ↦ ?_⟩
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.1 hz
  obtain ⟨hqC, hqA, hdqA, -, -⟩ := hq z (mem_ball_zero_iff.2 (by linarith))
  have hqd := hqC.differentiableAt two_ne_zero
  have hqwd : DifferentiableAt ℝ (fun y ↦ D.reading k x s y / peakFunction k y - w none -
      ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j) z :=
    (hqd.sub_const _).sub (DifferentiableAt.fun_sum fun j _ ↦
      (differentiableAt_const _).mul
        ((complexToRealEuclideanCoord ι j).differentiableAt.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y ↦ (complexToRealEuclideanCoord_apply j y).symm)))
  exact hDk x _ _ z hz1
    (D.reading_sub_affinePeakSection_eventuallyEq hk x s w (hz1.trans_lt hkρ) (hz1.trans_lt hk6))
    hqwd (D.norm_connectionReading_sub_affinePeakSection_le hk x s (hw.trans (by linarith)) hz1
      (hz1.trans_lt hkρ) (hz1.trans_lt hk6) hqd hqA hdqA) (hwz z hz)

end RescaledUnitaryCharts

end SymplecticGeometry

end
