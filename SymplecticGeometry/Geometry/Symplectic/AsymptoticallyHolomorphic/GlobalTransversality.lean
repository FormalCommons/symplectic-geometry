/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakSection
public import Mathlib.Analysis.InnerProductSpace.PiL2
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartChange
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.LocalTransversality
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.PeakQuotient
import SymplecticGeometry.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Global uniform transversality: the local correction and one colour

Let `D` be rescaled unitary charts of radius `ρ₀ > 0` for `(σ, J)` and a connection form `α`, and
let `M` carry the metric `σ(·, J ·)`. This file corrects a section `s` of `PowerBundle P k` on
one ball, of radius one in the chart centred at `x`, so that it becomes transverse there in the
quantitative sense of `SymplecticGeometry.IsUniformlyTransverse`, and then corrects a section at
all centres of one colour of a separated set at once.

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
* `SymplecticGeometry.RescaledUnitaryCharts.exists_correction_of_separated`: one step of the
  iteration over colours. All centres of a finite set `T` of polynomial counting whose distinct
  points are at rescaled distance at least `R` are corrected at once, with coefficients of norm at
  most `δ`. Near each centre of `T` the corrected section has transversality quantity at least
  `ε / 4 - C₂ * δ * exp (-c₂ * R ^ 2)`, and at every point the quantity drops by at most `C₁ * δ`.
  Its hypotheses are global bounds on the `2`-jet of `s` and the `1`-jet of `∂̄ s`.

The proof of the local correction divides the reading of `s` by the cut-off Gaussian, which meets
the hypotheses of the local transversality estimate
(`exists_forall_norm_reading_div_peakFunction_le`); the estimate
`SymplecticGeometry.exists_norm_le_max_ge_of_flatDbar_le` gives `w`; the reading of the corrected
section is then the corrected quotient times the Gaussian near the closed unit ball, and
`eventually_div_four_le_max_of_reading_eventuallyEq_mul_gaussian` carries the lower bound back to
the section.

For one colour, the changes of chart of `ChartChange.lean` turn the global bounds on `s` into the
hypotheses of the local correction at each centre. Near a centre `x ∈ T`, the corrections at the
other centres are at rescaled distance at least `R - 2` and form a Gaussian tail
(`exists_jetNorm_sum_affinePeakSection_le`), and at every point the whole sum has `1`-jet norm
`O(δ)`.
Both effects on the transversality quantity are bounded by
`abs_max_norm_add_sub_max_norm_le_jetNorm`.

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

/-- Let `q` be the quotient of the reading of `s` by the cut-off Gaussian, differentiable at a
point `z` of the closed unit ball, with `‖q z‖ ≤ A` and `‖dq_z‖ ≤ A`. Then the corrected quotient
`q - w₀ - Σ_j w_j z_j` is differentiable at `z`, and, for `‖w‖ ≤ 1`, the connection read at `z`
of the section corrected by peak sections has norm at most `2 * A + 1 + 2 * card ι`. -/
private theorem differentiableAt_and_norm_connectionReading_sub_affinePeakSection_le {k : ℕ}
    (hk : k₀ ≤ k) (x : M) (s : Π y, PowerBundle P k y) {w : EuclideanSpace ℂ (Option ι)}
    (hw : ‖w‖ ≤ 1) {z : StdSpace ι} (hz : ‖z‖ ≤ 1) (hzρ : ‖z‖ < ρ₀ * √k)
    (hz6 : ‖z‖ < (k : ℝ) ^ (1 / 6 : ℝ)) {A : ℝ}
    (hqd : DifferentiableAt ℝ (fun y ↦ D.reading k x s y / peakFunction k y) z)
    (hqA : ‖D.reading k x s z / peakFunction k z‖ ≤ A)
    (hdqA : ‖fderiv ℝ (fun y ↦ D.reading k x s y / peakFunction k y) z‖ ≤ A) :
    DifferentiableAt ℝ (fun y ↦ D.reading k x s y / peakFunction k y - w none -
        ∑ j, w (some j) * (complexToRealEuclidean ι).symm y j) z ∧
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
  have hLn : ‖L‖ ≤ Fintype.card ι := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖w (some j) • complexToRealEuclideanCoord ι j‖ ≤ ∑ _j : ι, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ by
            rw [norm_smul]
            exact (mul_le_mul (hw' _) (norm_complexToRealEuclideanCoord_le j) (norm_nonneg _)
              zero_le_one).trans_eq (one_mul 1)
      _ = Fintype.card ι := by simp
  have hLz : ‖L z‖ ≤ Fintype.card ι :=
    (L.le_of_opNorm_le hLn z).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hz)
  have hqwz : ‖qw z‖ ≤ A + 1 + Fintype.card ι := by
    have : qw z = q z - w none - L z := by simp only [qw, hL]
    rw [this]
    have := norm_sub_le (q z - w none) (L z)
    have := norm_sub_le (q z) (w none)
    linarith [hw' none]
  have hdqw : ‖fderiv ℝ qw z‖ ≤ A + Fintype.card ι := by
    rw [hqw.fderiv]
    exact (norm_sub_le _ _).trans (add_le_add hdqA hLn)
  refine ⟨hqw.differentiableAt, ?_⟩
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
  have hCk : ∀ᶠ k : ℕ in Filter.atTop, C * (k : ℝ) ^ (-1 / 2 : ℝ) ≤ ε :=
    (Real.eventually_mul_rpow_neg_half_lt C hε).mono fun _ h ↦ h.le
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
  obtain ⟨hqwd, hB⟩ := D.differentiableAt_and_norm_connectionReading_sub_affinePeakSection_le hk x
    s (hw.trans (by linarith)) hz1 (hz1.trans_lt hkρ) (hz1.trans_lt hk6) hqd hqA hdqA
  exact hDk x _ _ z hz1
    (D.reading_sub_affinePeakSection_eventuallyEq hk x s w (hz1.trans_lt hkρ) (hz1.trans_lt hk6))
    hqwd hB (hwz z hz)

/-- **Correcting one colour of a separated set of centres.** Let `M` be preconnected, Hausdorff and
boundaryless, with the metric `σ(·, J ·)`, let `α` be a connection form and `ρ₀ > 0`. For every
bound `B`, counting constant `C₀` and exponent `m` there are an exponent `p > 0`, `δ₀ > 0` and
constants `C₁`, `C₂` and `c₂ > 0` such that, for `0 < δ < δ₀` and `ε = δ / log (1 / δ) ^ p`, the
following holds for all large `k`. Let `T` be a finite set of centres with at most
`C₀ * (1 + ρ) ^ m` points at rescaled distance at most `ρ` from any point, for every `ρ ≥ 0`, whose
distinct points are at rescaled distance at least `R ≥ 0`. Let `s` be a section of
`PowerBundle P k` whose readings are `C²` and whose `∂̄` readings are `C¹` at the centre of every
chart, with `D.jetNorm k 2 s ≤ B` and `D.dbarJetNorm k 1 s ≤ B * k ^ (-1 / 2)` everywhere. Then
there are coefficients `w x` of norm at most `δ` on `T` such that the quantity
`max ‖t y‖ ((2π k)^(-1/2) ‖∂ t(y)‖)` of `t = s - Σ_{x ∈ T} D.affinePeakSection k x (w x)` is
* at least `ε / 4 - C₂ * δ * exp (-c₂ * R ^ 2)` at `y = (D.chart k x).symm z`, for `x ∈ T` and
  `‖z‖ ≤ 1`;
* at least the same quantity for `s` minus `C₁ * δ`, at every point `y`. -/
theorem exists_correction_of_separated [T2Space M] [I.Boundaryless] [PreconnectedSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] [∀ y, Nonempty (P y)]
    (hg : ∀ (y : M) (v w : TangentSpace I y), inner ℝ v w = σ.eval₂ y v (J y w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (B C₀ : ℝ) (m : ℕ) :
    ∃ p : ℕ, 0 < p ∧ ∃ δ₀ > 0, ∃ C₁ C₂ c₂ : ℝ, 0 < c₂ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      ∀ᶠ k : ℕ in Filter.atTop, ∀ (T : Finset M) (R : ℝ), 0 ≤ R →
        (∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
          ((T.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m) →
        (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → R ≤ rescaledDist I k x x') →
        ∀ s : Π y, PowerBundle P k y,
        (∀ y, ContDiffAt ℝ 2 (D.reading k y s) 0 ∧ ContDiffAt ℝ 1 (D.dbarReading k y s) 0) →
        (∀ y, D.jetNorm k 2 s y ≤ B ∧ D.dbarJetNorm k 1 s y ≤ B * (k : ℝ) ^ (-1 / 2 : ℝ)) →
        ∃ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ T, ‖w x‖ ≤ δ) ∧
          (∀ x ∈ T, ∀ z ∈ closedBall (0 : StdSpace ι) 1,
            δ / Real.log (1 / δ) ^ p / 4 - C₂ * δ * Real.exp (-c₂ * R ^ 2) ≤
              max ‖(s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) ((D.chart k x).symm z)‖
                ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart (powerConnection α k
                  (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) ((D.chart k x).symm z))‖)) ∧
          ∀ y : M,
            max ‖s y‖ ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart
                (powerConnection α k s y)‖) - C₁ * δ ≤
              max ‖(s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) y‖
                ((2 * Real.pi * k) ^ (-1 / 2 : ℝ) * ‖J.oneZeroPart (powerConnection α k
                  (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) y)‖) := by
  classical
  obtain ⟨ρ₁, hρ₁, hρ₁₀, h₁⟩ := D.jetNormAt_reading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨C₃, hC₃, h₃⟩ := h₁ 2
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := D.jetNormAt_dbarReading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨C₄, hC₄, h₄⟩ := h₂ 1
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  set B' := max (C₃ * 3 ^ 2 * B) (C₄ * 3 * B)
  obtain ⟨p, hp, δ₀, hδ₀, H⟩ := D.exists_local_correction hg hα hρ₀ B'
  obtain ⟨C, c, hc, Hsum⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m 1
  refine ⟨p, hp, δ₀, hδ₀, max C 0, max C 0 * Real.exp (4 * c), c / 2, half_pos hc,
    fun δ hδ hδδ₀ ↦ ?_⟩
  set ρ := min (min ρ₁ ρ₂) ρ₃
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) hρ₃
  have hkρ : ∀ᶠ k : ℕ in Filter.atTop, (11 / 10 : ℝ) < ρ * √k :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ).eventually_gt_atTop _
  filter_upwards [H δ hδ hδδ₀, Hsum, Filter.eventually_ge_atTop k₀, Filter.eventually_ne_atTop 0,
    hkρ, D.eventually_contDiffAt_reading_and_dbarReading_affinePeakSection hρ₀,
    D.eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection hρ₀]
    with k hloc hsum hk hk0 hkρ hsm₁ hsm T R hR hT hsep s hs hsB
  -- Points of the ball of radius `11 / 10` lie in the balls where the chart changes apply, and
  -- at rescaled distance at most `2` from the centre.
  have hball {z : StdSpace ι} (hz : ‖z‖ < 11 / 10) {ρ' : ℝ} (hρ' : ρ ≤ ρ') :
      z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    mem_ball_zero_iff.2 (hz.trans (hkρ.trans_le (by gcongr)))
  have hdist (x : M) {z : StdSpace ι} (hz : ‖z‖ < 11 / 10) :
      rescaledDist I k x ((D.chart k x).symm z) ≤ 2 := by
    have h := D.rescaledEDist_symm_symm_le hg hρ₃₀ hk x (hcmp hk x)
      (hball (z := 0) (by simp) (min_le_right _ _)) (hball hz (min_le_right _ _))
    rw [D.chart_symm_zero hk x, zero_sub, norm_neg, rescaledEDist_le_ofReal_iff (by positivity)]
      at h
    refine h.trans ?_
    have h32 : √(3 / 2 : ℝ) ≤ 5 / 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    nlinarith [norm_nonneg z]
  have hdiff (y : M) : ∀ᶠ v in 𝓝 0, DifferentiableAt ℝ (D.reading k y s) v :=
    ((hs y).1.eventually (by simp)).mono fun _ hv ↦ hv.differentiableAt (by simp)
  -- The hypotheses of the local correction hold at every centre.
  have hhyp (x : M) : ∀ z ∈ ball (0 : StdSpace ι) (11 / 10), ContDiffAt ℝ 2 (D.reading k x s) z ∧
      jetNormAt ℝ 2 (D.reading k x s) z ≤ B' ∧
      jetNormAt ℝ 1 (D.dbarReading k x s) z ≤ B' * (k : ℝ) ^ (-1 / 2 : ℝ) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    set y := (D.chart k x).symm z
    have hd := hdist x hz
    have hd0 := rescaledDist_nonneg I k x y
    refine ⟨D.contDiffAt_reading_of_chart_change (n := 2) hk x
      (hball hz ((min_le_left _ _).trans ((min_le_left _ _).trans hρ₁₀))) (hs y).1, ?_, ?_⟩
    · refine (h₃ hk x z (hball hz ((min_le_left _ _).trans (min_le_left _ _))) (hs y).1).trans ?_
      have hJ0 := D.jetNorm_nonneg k 2 s y
      calc _ ≤ C₃ * 3 ^ 2 * D.jetNorm k 2 s y := by gcongr; linarith
        _ ≤ C₃ * 3 ^ 2 * B := by gcongr; exact (hsB y).1
        _ ≤ B' := le_max_left _ _
    · refine (h₄ hk x z (hball hz ((min_le_left _ _).trans (min_le_right _ _))) (hdiff y)
        (hs y).2).trans ?_
      have hJ0 := D.dbarJetNorm_nonneg k 1 s y
      calc _ ≤ C₄ * 3 * D.dbarJetNorm k 1 s y := by gcongr; linarith
        _ ≤ C₄ * 3 * (B * (k : ℝ) ^ (-1 / 2 : ℝ)) := by gcongr; exact (hsB y).2
        _ = C₄ * 3 * B * (k : ℝ) ^ (-1 / 2 : ℝ) := by ring
        _ ≤ B' * (k : ℝ) ^ (-1 / 2 : ℝ) := by gcongr; exact le_max_right _ _
  choose w hw hwQ using fun x ↦ hloc x s (hhyp x)
  refine ⟨w, fun x _ ↦ hw x, fun x hx z hz ↦ ?_, fun y ↦ ?_⟩
  · have hz1 : ‖z‖ < 11 / 10 := (mem_closedBall_zero_iff.1 hz).trans_lt (by norm_num)
    set y := (D.chart k x).symm z
    -- The other centres of `T` lie at rescaled distance at least `R - 2` from `y`.
    set R' := max (R - 2) 0
    have hfar : (T.erase x).filter (fun x' ↦ R' ≤ rescaledDist I k x' y) = T.erase x := by
      refine Finset.filter_true_of_mem fun x' hx' ↦ max_le ?_ (rescaledDist_nonneg I k x' y)
      obtain ⟨hne, hx'T⟩ := Finset.mem_erase.1 hx'
      have h1 := hsep x hx x' hx'T (Ne.symm hne)
      have h2 := rescaledDist_triangle (I := I) k x y x'
      rw [rescaledDist_comm (I := I) k y x'] at h2
      linarith [hdist x hz1]
    have hcount (y' : M) (ρ' : ℝ) (hρ' : 0 ≤ ρ') :
        (((T.erase x).filter fun x' ↦ rescaledDist I k x' y' ≤ ρ').card : ℝ) ≤
          C₀ * (1 + ρ') ^ m :=
      le_trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.erase_subset x T))) (hT y' ρ' hρ')
    have htail := (hsum y (T.erase x) (hcount y) δ w hδ.le fun x' _ ↦ hw x').2.2 R'
      (le_max_right _ _)
    rw [hfar] at htail
    have heq : s - ∑ x' ∈ T, D.affinePeakSection k x' (w x') =
        (s - D.affinePeakSection k x (w x)) +
          -∑ x' ∈ T.erase x, D.affinePeakSection k x' (w x') := by
      rw [← Finset.add_sum_erase T _ hx]
      abel
    have hstab := D.abs_max_norm_add_sub_max_norm_le_jetNorm hg hα hρ₀ hk hk0
      (s := s - D.affinePeakSection k x (w x))
      (t := -∑ x' ∈ T.erase x, D.affinePeakSection k x' (w x')) (y := y)
      (by rw [reading_sub]; exact (hdiff y).self_of_nhds.sub
            ((hsm₁ x y (w x)).1.differentiableAt (by simp)))
      (by rw [reading_neg]; exact ((hsm _ w y).1.differentiableAt (by simp)).neg)
    rw [jetNorm_neg, ← heq] at hstab
    have hexp : Real.exp (-c * R' ^ 2) ≤ Real.exp (4 * c) * Real.exp (-(c / 2) * R ^ 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : R ^ 2 / 2 - 4 ≤ R' ^ 2 := by
        rcases le_total R 2 with h | h
        · have : R' = 0 := max_eq_right (by linarith)
          rw [this]
          nlinarith
        · have : R' = R - 2 := max_eq_left (by linarith)
          rw [this]
          nlinarith [sq_nonneg (R - 4)]
      nlinarith
    have hC : C * δ * Real.exp (-c * R' ^ 2) ≤
        max C 0 * Real.exp (4 * c) * δ * Real.exp (-(c / 2) * R ^ 2) := by
      calc C * δ * Real.exp (-c * R' ^ 2) ≤ max C 0 * δ * Real.exp (-c * R' ^ 2) := by
            gcongr; exact le_max_left _ _
        _ ≤ max C 0 * δ * (Real.exp (4 * c) * Real.exp (-(c / 2) * R ^ 2)) := by
            gcongr
        _ = _ := by ring
    have := hwQ x z hz
    linarith [(abs_le.1 hstab).1]
  · have hstab := D.abs_max_norm_add_sub_max_norm_le_jetNorm hg hα hρ₀ hk hk0
      (s := s) (t := -∑ x' ∈ T, D.affinePeakSection k x' (w x')) (y := y)
      (hdiff y).self_of_nhds
      (by rw [reading_neg]; exact ((hsm _ w y).1.differentiableAt (by simp)).neg)
    rw [jetNorm_neg, ← sub_eq_add_neg] at hstab
    have h1 := (hsum y T (hT y) δ w hδ.le fun x _ ↦ hw x).1
    have h2 : C * δ ≤ max C 0 * δ := by gcongr; exact le_max_left _ _
    linarith [(abs_le.1 hstab).1]

end RescaledUnitaryCharts

end SymplecticGeometry

end
