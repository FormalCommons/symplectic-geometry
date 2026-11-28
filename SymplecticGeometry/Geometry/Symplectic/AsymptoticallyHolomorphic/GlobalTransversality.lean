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
import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.SeparatedNet
import SymplecticGeometry.Analysis.SpecialFunctions.Log.Recurrence
import SymplecticGeometry.Analysis.SpecialFunctions.Gaussian.Basic
import SymplecticGeometry.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Global uniform transversality

Let `D` be rescaled unitary charts of radius `ρ₀ > 0` for `(σ, J)` and a connection form `α`, and
let `M` carry the metric `σ(·, J ·)`. This file corrects a section `s` of `PowerBundle P k` on
one ball, of radius one in the chart centred at `x`, so that it becomes transverse there in the
quantitative sense of `SymplecticGeometry.IsUniformlyTransverse`, and then corrects a section at
all centres of one colour of a separated set at once. Iterating over the colours of a separated
net, it proves that asymptotically holomorphic sections that are uniformly transverse exist.

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
  `ε / 4 ≤ transversalityQuantity J α k t y` at every point `y` of the image of the closed unit
  ball. The constants are chosen in the order that the iteration over colours needs: `δ` first,
  then `k`, uniformly in `x` and `s`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_correction_of_separated`: one step of the
  iteration over colours. All centres of a finite set `T` of polynomial counting whose distinct
  points are at rescaled distance at least `R` are corrected at once, with coefficients of norm at
  most `δ`. Near each centre of `T` the corrected section has transversality quantity at least
  `ε / 4 - C₂ * δ * exp (-c₂ * R ^ 2)`, and at every point the quantity drops by at most `C₁ * δ`.
  Its hypotheses are global bounds on the `2`-jet of `s` and the `1`-jet of `∂̄ s`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_jetNorm_sum_erase_affinePeakSection_le`: near
  a centre `x` of such a set `T`, the peak sections at the other centres of `T` have jet norm
  `O(δ * exp (-c * R ^ 2))`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_isUniformlyTransverse`: on a compact,
  Hausdorff, preconnected and boundaryless `M`, there are an asymptotically holomorphic sequence
  `s` of sections and `η > 0` such that `s` is uniformly transverse with constant `η`.

The proof of the local correction divides the reading of `s` by the cut-off Gaussian, which meets
the hypotheses of the local transversality estimate
(`exists_forall_norm_reading_div_peakFunction_le`); the estimate
`SymplecticGeometry.exists_norm_le_max_ge_of_flatDbar_le` gives `w`; the reading of the corrected
section is then the corrected quotient times the Gaussian near the closed unit ball, and
`eventually_div_four_le_transversalityQuantity_of_mul_gaussian` carries the lower bound back to
the section.

For one colour, the changes of chart of `ChartChange.lean` turn the global bounds on `s` into the
hypotheses of the local correction at each centre. Near a centre `x ∈ T`, the corrections at the
other centres are at rescaled distance at least `R - 2` and form a Gaussian tail
(`exists_jetNorm_sum_affinePeakSection_le`, then `Real.exp_neg_mul_max_sub_sq_le`, in
`exists_jetNorm_sum_erase_affinePeakSection_le`), and at every point the whole sum has `1`-jet norm
`O(δ)`.
Both effects on the transversality quantity are bounded by
`abs_transversalityQuantity_add_sub_le_jetNorm`.

For the milestone, `exists_separated_chart_cover_coloring` gives, for each large `k`, a finite
set `S` of centres whose closed unit chart balls cover `M`, with polynomial counting, and for
every `R ≥ 1` a colouring with at most `C * R ^ m` colours in which centres of one colour are at
rescaled distance at least `R`. Starting from the zero section, colour `j` is corrected by
`exists_correction_of_separated` with coefficients of size `δ_j = b_j / A`, where `A = 2 C₁ + 2`
and `b_{j+1} = δ_j / log (1 / δ_j) ^ p / 8`. Then `b_{j+1} ≤ b_j - C₁ δ_j` keeps the bound on the
centres already treated, and on the new ones it is enough that
`8 C₂ exp (-c₂ R²) log (1 / δ_j) ^ p ≤ 1` for every colour `j`. The logarithms
`u_j = log (1 / b_j)` satisfy `u_{j+1} = u_j + log (8 A) + p log (u_j + log A)`, so
`Real.exists_le_mul_mul_log_of_le_add_log` bounds `log (1 / δ_j)` by a polynomial in `R` for
`j < C * R ^ m`, and the Gaussian factor beats it for a large `R`, chosen before `k`. Every
partial sum is a sum of `affinePeakSection` over a subset of `S` with coefficients of norm at
most `1`, so `exists_jetNorm_sum_affinePeakSection_le` gives the bounds on its jets that the
correction needs, uniformly in the colour, and
`isAsymptoticallyHolomorphic_sum_affinePeakSection` shows that the final sections are
asymptotically holomorphic.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Theorem 1 and the proof of Proposition 2
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 3
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
`ε / 4 ≤ transversalityQuantity J α k t y` at `y = (D.chart k x).symm z` for every `z` of the
closed unit ball. The transversality quantity is `max ‖t y‖ ((2π k)^(-1/2) ‖∂ t(y)‖)`, where
`∂ t(y)` is the `(1,0)`-part `J.oneZeroPart` of `D_k t` at `y`, with its operator norm. -/
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
            transversalityQuantity J α k (s - D.affinePeakSection k x w)
              ((D.chart k x).symm z) := by
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
  filter_upwards [hC, hCk, D.eventually_div_four_le_transversalityQuantity_of_mul_gaussian hg
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

/-- **Peak sections at the other centres of a separated set.** Let `M` be preconnected, Hausdorff
and boundaryless, with the metric `σ(·, J ·)`. For every counting constant `C₀`, exponent `m`,
order `r` and radius `a` there are `C` and `c > 0` such that for all large `k`: let `T` be a finite
set of centres with at most `C₀ * (1 + ρ) ^ m` points at rescaled distance at most `ρ` from any
point, for every `ρ ≥ 0`, whose distinct points are at rescaled distance at least `R ≥ 0`. Then
for `x ∈ T`, every point `y` at rescaled distance at most `a` from `x` and coefficients `w` of
norm at most `δ ≥ 0` on `T`, the `r`-jet norm at `y` of the sum of
`D.affinePeakSection k x' (w x')` over `x' ∈ T.erase x` is at most `C * δ * exp (-c * R ^ 2)`. -/
theorem exists_jetNorm_sum_erase_affinePeakSection_le [T2Space M] [I.Boundaryless]
    [PreconnectedSpace M] [DecidableEq M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (y : M) (v w : TangentSpace I y), inner ℝ v w = σ.eval₂ y v (J y w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (C₀ : ℝ) (m r : ℕ)
    (a : ℝ) :
    ∃ C c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop, ∀ (T : Finset M) (R : ℝ), 0 ≤ R →
      (∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
        ((T.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m) →
      (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → R ≤ rescaledDist I k x x') →
      ∀ x ∈ T, ∀ y : M, rescaledDist I k x y ≤ a →
      ∀ (δ : ℝ) (w : M → EuclideanSpace ℂ (Option ι)), 0 ≤ δ → (∀ x ∈ T, ‖w x‖ ≤ δ) →
        D.jetNorm k r (∑ x' ∈ T.erase x, D.affinePeakSection k x' (w x')) y ≤
          C * δ * Real.exp (-c * R ^ 2) := by
  obtain ⟨C, c, hc, Hsum⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m r
  refine ⟨max C 0 * Real.exp (c * a ^ 2), c / 2, half_pos hc, ?_⟩
  filter_upwards [Hsum] with k hsum T R hR hT hsep x hx y hy δ w hδ hw
  -- The other centres of `T` lie at rescaled distance at least `R - a` from `y`.
  set R' := max (R - a) 0
  have hfar : (T.erase x).filter (fun x' ↦ R' ≤ rescaledDist I k x' y) = T.erase x := by
    refine Finset.filter_true_of_mem fun x' hx' ↦ max_le ?_ (rescaledDist_nonneg I k x' y)
    obtain ⟨hne, hx'T⟩ := Finset.mem_erase.1 hx'
    have h1 := hsep x hx x' hx'T (Ne.symm hne)
    have h2 := rescaledDist_triangle (I := I) k x y x'
    rw [rescaledDist_comm (I := I) k y x'] at h2
    linarith
  have hcount (ρ : ℝ) (hρ : 0 ≤ ρ) :
      (((T.erase x).filter fun x' ↦ rescaledDist I k x' y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m :=
    le_trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.erase_subset x T))) (hT y ρ hρ)
  have htail := (hsum y (T.erase x) hcount δ w hδ fun x' hx' ↦
    hw x' (Finset.mem_of_mem_erase hx')).2.2 R' (le_max_right _ _)
  rw [hfar] at htail
  refine htail.trans ?_
  calc C * δ * Real.exp (-c * R' ^ 2) ≤ max C 0 * δ * Real.exp (-c * R' ^ 2) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * δ * (Real.exp (c * a ^ 2) * Real.exp (-(c / 2) * R ^ 2)) := by
        gcongr; exact Real.exp_neg_mul_max_sub_sq_le hc.le hR
    _ = _ := by ring

/-- **Correcting one colour of a separated set of centres.** Let `M` be preconnected, Hausdorff and
boundaryless, with the metric `σ(·, J ·)`, let `α` be a connection form and `ρ₀ > 0`. For every
bound `B`, counting constant `C₀` and exponent `m` there are an exponent `p > 0`, `δ₀ > 0` and
constants `C₁`, `C₂` and `c₂ > 0` such that, for `0 < δ < δ₀` and `ε = δ / log (1 / δ) ^ p`, the
following holds for all large `k`. Let `T` be a finite set of centres with at most
`C₀ * (1 + ρ) ^ m` points at rescaled distance at most `ρ` from any point, for every `ρ ≥ 0`, whose
distinct points are at rescaled distance at least `R ≥ 0`. Let `s` be a section of
`PowerBundle P k` whose readings are `C²` and whose `∂̄` readings are `C¹` at the centre of every
chart, with `D.jetNorm k 2 s ≤ B` and `D.dbarJetNorm k 1 s ≤ B * k ^ (-1 / 2)` everywhere. Then
there are coefficients `w x` of norm at most `δ` on `T` such that
`transversalityQuantity J α k t y`, for `t = s - Σ_{x ∈ T} D.affinePeakSection k x (w x)`, is
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
              transversalityQuantity J α k (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x'))
                ((D.chart k x).symm z)) ∧
          ∀ y : M, transversalityQuantity J α k s y - C₁ * δ ≤
            transversalityQuantity J α k (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) y := by
  classical
  obtain ⟨ρ₁, hρ₁, hρ₁₀, h₁⟩ := D.jetNormAt_reading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨C₃, hC₃, h₃⟩ := h₁ 2
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := D.jetNormAt_dbarReading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨C₄, hC₄, h₄⟩ := h₂ 1
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  set B' := max (C₃ * 3 ^ 2 * B) (C₄ * 3 * B)
  obtain ⟨p, hp, δ₀, hδ₀, H⟩ := D.exists_local_correction hg hα hρ₀ B'
  obtain ⟨C, c, -, Hsum⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m 1
  obtain ⟨C₂, c₂, hc₂, Htail⟩ :=
    D.exists_jetNorm_sum_erase_affinePeakSection_le hg hJ hα hρ₀ C₀ m 1 2
  refine ⟨p, hp, δ₀, hδ₀, max C 0, C₂, c₂, hc₂, fun δ hδ hδδ₀ ↦ ?_⟩
  set ρ := min (min ρ₁ ρ₂) ρ₃
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) hρ₃
  have hkρ : ∀ᶠ k : ℕ in Filter.atTop, (11 / 10 : ℝ) < ρ * √k :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ).eventually_gt_atTop _
  filter_upwards [H δ hδ hδδ₀, Hsum, Htail, Filter.eventually_ge_atTop k₀,
    Filter.eventually_ne_atTop 0,
    hkρ, D.eventually_contDiffAt_reading_and_dbarReading_affinePeakSection hρ₀,
    D.eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection hρ₀]
    with k hloc hsum htail hk hk0 hkρ hsm₁ hsm T R hR hT hsep s hs hsB
  -- Points of the ball of radius `11 / 10` lie in the balls where the chart changes apply, and
  -- at rescaled distance at most `2` from the centre.
  have hball {z : StdSpace ι} (hz : ‖z‖ < 11 / 10) {ρ' : ℝ} (hρ' : ρ ≤ ρ') :
      z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    mem_ball_zero_iff.2 (hz.trans (hkρ.trans_le (by gcongr)))
  have hdist (x : M) {z : StdSpace ι} (hz : ‖z‖ < 11 / 10) :
      rescaledDist I k x ((D.chart k x).symm z) ≤ 2 := by
    refine (D.rescaledDist_symm_le hg hρ₃₀ hk x (hcmp hk x) (hball hz (min_le_right _ _))).trans ?_
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
    have heq : s - ∑ x' ∈ T, D.affinePeakSection k x' (w x') =
        (s - D.affinePeakSection k x (w x)) +
          -∑ x' ∈ T.erase x, D.affinePeakSection k x' (w x') := by
      rw [← Finset.add_sum_erase T _ hx]
      abel
    have hstab := D.abs_transversalityQuantity_add_sub_le_jetNorm hg hα hρ₀ hk hk0
      (s := s - D.affinePeakSection k x (w x))
      (t := -∑ x' ∈ T.erase x, D.affinePeakSection k x' (w x')) (y := y)
      (by rw [reading_sub]; exact (hdiff y).self_of_nhds.sub
            ((hsm₁ x y (w x)).1.differentiableAt (by simp)))
      (by rw [reading_neg]; exact ((hsm _ w y).1.differentiableAt (by simp)).neg)
    rw [jetNorm_neg, ← heq] at hstab
    have htail' := htail T R hR hT hsep x hx y (hdist x hz1) δ w hδ.le fun x' _ ↦ hw x'
    have := hwQ x z hz
    linarith [(abs_le.1 hstab).1]
  · have hstab := D.abs_transversalityQuantity_add_sub_le_jetNorm hg hα hρ₀ hk hk0
      (s := s) (t := -∑ x' ∈ T, D.affinePeakSection k x' (w x')) (y := y)
      (hdiff y).self_of_nhds
      (by rw [reading_neg]; exact ((hsm _ w y).1.differentiableAt (by simp)).neg)
    rw [jetNorm_neg, ← sub_eq_add_neg] at hstab
    have h1 := (hsum y T (hT y) δ w hδ.le fun x _ ↦ hw x).1
    have h2 : C * δ ≤ max C 0 * δ := by gcongr; exact le_max_left _ _
    linarith [(abs_le.1 hstab).1]

/-- The constants of the iteration over colours. Given an exponent `p`, a dimension `m`, a bound
`δ₀ > 0` on the size of the corrections, constants `C₁, C₂ ≥ 0`, `c₂ > 0` and a colour constant
`C`, there are `R ≥ 1`, lower bounds `b j > 0` and sizes `0 < δ j < δ₀` with `δ j ≤ 1` such that
`b (j + 1) ≤ b j - C₁ * δ j` for every `j`, and
`b (j + 1) ≤ δ j / log (1 / δ j) ^ p / 4 - C₂ * δ j * exp (-c₂ * R ^ 2)` for `j < C * R ^ m`.
Here `δ j = b j / A` and `b (j + 1) = δ j / log (1 / δ j) ^ p / 8` for `A = 2 * C₁ + 2`, and
`R` is chosen with `Real.exists_le_mul_mul_log_of_le_add_log`. -/
private theorem exists_iteration_constants (p m : ℕ) {δ₀ C₁ C₂ c₂ : ℝ} (hδ₀ : 0 < δ₀)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc₂ : 0 < c₂) (C : ℝ) :
    ∃ R ≥ (1 : ℝ), ∃ b δ : ℕ → ℝ, (∀ j, 0 < b j) ∧ (∀ j, 0 < δ j ∧ δ j < δ₀ ∧ δ j ≤ 1) ∧
      (∀ j, b (j + 1) ≤ b j - C₁ * δ j) ∧
      ∀ j : ℕ, (j : ℝ) < C * R ^ m →
        b (j + 1) ≤ δ j / Real.log (1 / δ j) ^ p / 4 - C₂ * δ j * Real.exp (-c₂ * R ^ 2) := by
  set A := 2 * C₁ + 2
  set b₀ := min (δ₀ / 2) (Real.exp (-1))
  have hb₀ : 0 < b₀ := lt_min (half_pos hδ₀) (Real.exp_pos _)
  have hb₀1 : b₀ ≤ 1 := (min_le_right _ _).trans (Real.exp_le_one_iff.2 (by norm_num))
  set f : ℝ → ℝ := fun β ↦ β / A / Real.log (1 / (β / A)) ^ p / 8
  set b : ℕ → ℝ := fun j ↦ f^[j] b₀
  have hbs (j : ℕ) : b (j + 1) = f (b j) := Function.iterate_succ_apply' f j b₀
  -- For `0 < β ≤ b₀`, the logarithm `log (A / β)` is at least `1`.
  have hlog {β : ℝ} (hβ : 0 < β) (hβb : β ≤ b₀) : 1 ≤ Real.log (1 / (β / A)) := by
    rw [one_div_div, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hβ]
    calc Real.exp 1 * β ≤ Real.exp 1 * Real.exp (-1) := by
          gcongr; exact hβb.trans (min_le_right _ _)
      _ = 1 := by rw [← Real.exp_add]; simp
      _ ≤ A := by linarith
  have hf {β : ℝ} (hβ : 0 < β) (hβb : β ≤ b₀) : 0 < f β ∧ f β ≤ β / A / 8 := by
    have hL := hlog hβ hβb
    have hA0 : 0 < β / A := by positivity
    exact ⟨div_pos (div_pos hA0 (pow_pos (by linarith) _)) (by norm_num),
      div_le_div_of_nonneg_right (div_le_self hA0.le (one_le_pow₀ hL)) (by norm_num)⟩
  have hb (j : ℕ) : 0 < b j ∧ b j ≤ b₀ := by
    induction j with
    | zero => exact ⟨hb₀, le_rfl⟩
    | succ j ih =>
      rw [hbs]
      obtain ⟨h1, h2⟩ := hf ih.1 ih.2
      have : b j / A ≤ b j := div_le_self ih.1.le (by linarith)
      exact ⟨h1, by linarith [ih.2]⟩
  set δ : ℕ → ℝ := fun j ↦ b j / A
  have hδ (j : ℕ) : 0 < δ j ∧ δ j < δ₀ ∧ δ j ≤ 1 := by
    have h1 : δ j ≤ b j := div_le_self (hb j).1.le (by linarith)
    have h2 := (hb j).2
    have h3 : b₀ ≤ δ₀ / 2 := min_le_left _ _
    exact ⟨div_pos (hb j).1 (by linarith), by linarith, by linarith⟩
  set L : ℕ → ℝ := fun j ↦ Real.log (1 / δ j)
  have hL (j : ℕ) : 1 ≤ L j := hlog (hb j).1 (hb j).2
  have hbδ (j : ℕ) : b (j + 1) = δ j / L j ^ p / 8 := hbs j
  -- The logarithms `u j = log (1 / b j)` satisfy the recurrence of `Recurrence.lean`.
  set u : ℕ → ℝ := fun j ↦ Real.log (1 / b j)
  have hu (j : ℕ) : 0 ≤ u j := Real.log_nonneg (one_le_one_div (hb j).1 ((hb j).2.trans hb₀1))
  have hA0 : 0 < A := by linarith
  have hLu (j : ℕ) : L j = u j + Real.log A := by
    simp only [L, u, δ]
    rw [one_div_div, div_eq_mul_one_div, Real.log_mul hA0.ne' (one_div_pos.2 (hb j).1).ne']
    ring
  have hrec (j : ℕ) : u (j + 1) ≤ u j + Real.log (8 * A) + p * Real.log (u j + Real.log A) := by
    have hLj : 0 < L j := by linarith [hL j]
    have e : u (j + 1) = u j + Real.log (8 * A) + p * Real.log (L j) := by
      simp only [u, one_div, Real.log_inv]
      rw [hbδ, Real.log_div (div_pos (hδ j).1 (pow_pos hLj p)).ne' (by norm_num),
        Real.log_div (hδ j).1.ne' (pow_pos hLj p).ne', Real.log_pow, show δ j = b j / A from rfl,
        Real.log_div (hb j).1.ne' hA0.ne', Real.log_mul (by norm_num) hA0.ne']
      ring
    rw [e, hLu]
  obtain ⟨K, hK⟩ := Real.exists_le_mul_mul_log_of_le_add_log hu (Nat.cast_nonneg p)
    (Real.log_pos (by linarith : (1 : ℝ) < A)) hrec
  -- For `j < C * R ^ m` the logarithm `L j` is at most a polynomial in `R`.
  set K' := max K 0
  set C' := max C 0
  set Q := K' * (C' + 1) ^ 2 + Real.log A + 1
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hLQ (j : ℕ) {R : ℝ} (hR : 1 ≤ R) (hj : (j : ℝ) < C * R ^ m) : L j ≤ Q * (R ^ 2) ^ m := by
    have hRm : 1 ≤ R ^ m := one_le_pow₀ hR
    have hlj : Real.log ((j : ℝ) + 2) ≤ j + 1 := by
      linarith [Real.log_le_sub_one_of_pos (x := (j : ℝ) + 2) (by linarith)]
    have hlj0 : 0 ≤ Real.log ((j : ℝ) + 2) := Real.log_nonneg (by linarith)
    have h1 : u j ≤ K' * ((j + 1) * (j + 1)) :=
      calc u j ≤ K * (j + 1) * Real.log (j + 2) := hK j
        _ ≤ K' * ((j + 1) * Real.log (j + 2)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ K' * ((j + 1) * (j + 1)) := by gcongr
    have h2 : (j : ℝ) + 1 ≤ (C' + 1) * R ^ m := by
      have : C * R ^ m ≤ C' * R ^ m := by gcongr; exact le_max_left _ _
      linarith
    have h3 : ((j : ℝ) + 1) * (j + 1) ≤ (C' + 1) ^ 2 * (R ^ 2) ^ m := by
      rw [← pow_mul, mul_comm 2 m, pow_mul]
      nlinarith
    have hR2 : 1 ≤ (R ^ 2) ^ m := one_le_pow₀ (one_le_pow₀ hR)
    rw [hLu]
    calc u j + Real.log A ≤ K' * ((C' + 1) ^ 2 * (R ^ 2) ^ m) + Real.log A * (R ^ 2) ^ m := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact le_mul_of_one_le_right hlogA hR2
      _ ≤ Q * (R ^ 2) ^ m := by nlinarith
  -- The Gaussian `exp (-c₂ * R ^ 2)` beats every power of `R`.
  set n := m * p
  set ε := 1 / (8 * C₂ * Q ^ p + 1) with hεdef
  have hε : 0 < ε := by positivity
  have htend : Filter.Tendsto (fun R : ℝ ↦ (c₂ * R ^ 2) ^ n * Real.exp (-(c₂ * R ^ 2)))
      Filter.atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      ((Filter.tendsto_pow_atTop two_ne_zero).const_mul_atTop hc₂)
  obtain ⟨R, hRε, hR⟩ := ((htend.eventually_lt_const (mul_pos (pow_pos hc₂ n) hε)).and
    (Filter.eventually_ge_atTop 1)).exists
  refine ⟨R, hR, b, δ, fun j ↦ (hb j).1, hδ, fun j ↦ ?_, fun j hj ↦ ?_⟩
  · have hδj := (hδ j).1
    have hbA : b j = 2 * (C₁ * δ j) + 2 * δ j := by
      simp only [δ, A]; field_simp
    have : δ j / L j ^ p ≤ δ j := div_le_self hδj.le (one_le_pow₀ (hL j))
    have := mul_nonneg hC₁ hδj.le
    rw [hbδ]
    linarith
  · -- `8 * C₂ * exp (-c₂ * R ^ 2) * L j ^ p ≤ 1`.
    set X := (R ^ 2) ^ n * Real.exp (-(c₂ * R ^ 2))
    have hX0 : 0 ≤ X := by positivity
    have hXε : X < ε := by
      rw [mul_pow, mul_assoc] at hRε
      exact lt_of_mul_lt_mul_left hRε (pow_nonneg hc₂.le n)
    rw [hεdef] at hXε
    have hX1 : X * (8 * C₂ * Q ^ p + 1) < 1 := (lt_div_iff₀ (by positivity)).1 hXε
    have hLp : L j ^ p ≤ Q ^ p * (R ^ 2) ^ n := by
      rw [show n = m * p from rfl, pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hL j]) (hLQ j hR hj) p
    have hY : 0 ≤ δ j / L j ^ p :=
      div_nonneg (hδ j).1.le (pow_nonneg (by linarith [hL j]) p)
    have hδL : δ j = δ j / L j ^ p * L j ^ p := by
      rw [div_mul_cancel₀]; exact (pow_pos (by linarith [hL j]) p).ne'
    have hkey : C₂ * Real.exp (-c₂ * R ^ 2) * L j ^ p ≤ 1 / 8 := by
      rw [neg_mul]
      have h1 : C₂ * Real.exp (-(c₂ * R ^ 2)) * L j ^ p ≤ C₂ * Q ^ p * X := by
        simp only [X]
        have := Real.exp_pos (-(c₂ * R ^ 2))
        calc _ ≤ C₂ * Real.exp (-(c₂ * R ^ 2)) * (Q ^ p * (R ^ 2) ^ n) := by gcongr
          _ = _ := by ring
      have : 0 ≤ C₂ * Q ^ p * X := by positivity
      nlinarith
    rw [hbδ]
    have h := mul_le_mul_of_nonneg_left hkey hY
    have : C₂ * δ j * Real.exp (-c₂ * R ^ 2) =
        δ j / L j ^ p * (C₂ * Real.exp (-c₂ * R ^ 2) * L j ^ p) := by
      conv_lhs => rw [hδL]
      ring
    linarith

section Iteration

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The iteration over the colours `c : M → Fin N` of a finite set `S` of centres, for one `k`:
colour `j` is corrected with coefficients of size `δ j`, by `hcorr`, which is the conclusion of
`exists_correction_of_separated` for `δ j`, and the lower bound `b j` holds near the centres of
the colours below `j`. -/
private theorem exists_forall_le_transversalityQuantity_of_coloring [∀ y, Nonempty (P y)]
    {k : ℕ} {S : Finset M}
    {N : ℕ} (c : M → Fin N) {B C₁ C₂ c₂ R : ℝ} {p : ℕ} {b δ : ℕ → ℝ}
    (hδ : ∀ j, δ j ≤ 1) (hold : ∀ j, b (j + 1) ≤ b j - C₁ * δ j)
    (hnew : ∀ j < N,
      b (j + 1) ≤ δ j / Real.log (1 / δ j) ^ p / 4 - C₂ * δ j * Real.exp (-c₂ * R ^ 2))
    (hsep : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → c x = c x' → R ≤ rescaledDist I k x x')
    (hsm : ∀ (U : Finset M) (w : M → EuclideanSpace ℂ (Option ι)) (y : M),
      ContDiffAt ℝ ∞ (D.reading k y (∑ x ∈ U, D.affinePeakSection k x (w x))) 0 ∧
        ContDiffAt ℝ ∞ (D.dbarReading k y (∑ x ∈ U, D.affinePeakSection k x (w x))) 0)
    (hB : ∀ U ⊆ S, ∀ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ U, ‖w x‖ ≤ 1) → ∀ y,
      D.jetNorm k 2 (∑ x ∈ U, D.affinePeakSection k x (w x)) y ≤ B ∧
        D.dbarJetNorm k 1 (∑ x ∈ U, D.affinePeakSection k x (w x)) y ≤
          B * (k : ℝ) ^ (-1 / 2 : ℝ))
    (hcorr : ∀ j < N, ∀ T ⊆ S, (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → R ≤ rescaledDist I k x x') →
      ∀ s : Π y, PowerBundle P k y,
      (∀ y, ContDiffAt ℝ 2 (D.reading k y s) 0 ∧ ContDiffAt ℝ 1 (D.dbarReading k y s) 0) →
      (∀ y, D.jetNorm k 2 s y ≤ B ∧ D.dbarJetNorm k 1 s y ≤ B * (k : ℝ) ^ (-1 / 2 : ℝ)) →
      ∃ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ T, ‖w x‖ ≤ δ j) ∧
        (∀ x ∈ T, ∀ z ∈ closedBall (0 : StdSpace ι) 1,
          δ j / Real.log (1 / δ j) ^ p / 4 - C₂ * δ j * Real.exp (-c₂ * R ^ 2) ≤
            transversalityQuantity J α k (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x'))
              ((D.chart k x).symm z)) ∧
        ∀ y : M, transversalityQuantity J α k s y - C₁ * δ j ≤
          transversalityQuantity J α k (s - ∑ x' ∈ T, D.affinePeakSection k x' (w x')) y) :
    ∃ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ S, ‖w x‖ ≤ 1) ∧
      ∀ x ∈ S, ∀ z ∈ closedBall (0 : StdSpace ι) 1,
        b N ≤ transversalityQuantity J α k (-∑ x ∈ S, D.affinePeakSection k x (w x))
          ((D.chart k x).symm z) := by
  classical
  set U : ℕ → Finset M := fun j ↦ S.filter fun x ↦ (c x : ℕ) < j
  suffices h : ∀ j ≤ N, ∃ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ S, ‖w x‖ ≤ 1) ∧
      ∀ x ∈ U j, ∀ z ∈ closedBall (0 : StdSpace ι) 1,
        b j ≤ transversalityQuantity J α k (-∑ x ∈ U j, D.affinePeakSection k x (w x))
          ((D.chart k x).symm z) by
    obtain ⟨w, hw, hb⟩ := h N le_rfl
    have hU : U N = S := Finset.filter_true_of_mem fun x _ ↦ (c x).isLt
    rw [hU] at hb
    exact ⟨w, hw, hb⟩
  intro j hj
  induction j with
  | zero => exact ⟨0, fun _ _ ↦ by simp, fun x hx ↦ by simp [U] at hx⟩
  | succ j ih =>
    obtain ⟨w, hw, hb⟩ := ih (by omega)
    have hjN : j < N := by omega
    set T := S.filter fun x ↦ (c x : ℕ) = j
    set s : Π y, PowerBundle P k y := -∑ x ∈ U j, D.affinePeakSection k x (w x)
    have hUS : U j ⊆ S := Finset.filter_subset _ _
    have hwU : ∀ x ∈ U j, ‖w x‖ ≤ 1 := fun x hx ↦ hw x (hUS hx)
    have hdbar_neg (y : M) : D.dbarReading k y s =
        -D.dbarReading k y (∑ x ∈ U j, D.affinePeakSection k x (w x)) :=
      funext (D.dbarReading_neg k y _)
    obtain ⟨w', hw', hT, hall⟩ := hcorr j hjN T (Finset.filter_subset _ _)
      (fun x hx x' hx' hne ↦ hsep x (Finset.mem_filter.1 hx).1 x'
        (Finset.mem_filter.1 hx').1 hne
        (Fin.ext ((Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hx').2.symm))) s
      (fun y ↦ by
        rw [reading_neg, hdbar_neg]
        exact ⟨((hsm _ w y).1.of_le (by simp)).neg,
          ((hsm _ w y).2.of_le (by simp)).neg⟩)
      (fun y ↦ by rw [jetNorm_neg, dbarJetNorm_neg]; exact hB _ hUS w hwU y)
    set w'' : M → EuclideanSpace ℂ (Option ι) := fun x ↦ if (c x : ℕ) = j then w' x else w x
    -- The new section is the sum over the colours up to `j`.
    have hsum : s - ∑ x' ∈ T, D.affinePeakSection k x' (w' x') =
        -∑ x ∈ U (j + 1), D.affinePeakSection k x (w'' x) := by
      rw [← Finset.sum_filter_add_sum_filter_not (U (j + 1)) fun x ↦ (c x : ℕ) = j]
      have h1 : (U (j + 1)).filter (fun x ↦ (c x : ℕ) = j) = T := by
        ext x
        simp only [U, T, Finset.mem_filter]
        exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, by omega⟩, h.2⟩⟩
      have h2 : (U (j + 1)).filter (fun x ↦ ¬(c x : ℕ) = j) = U j := by
        ext x
        simp only [U, Finset.mem_filter]
        exact ⟨fun h ↦ ⟨h.1.1, by omega⟩, fun h ↦ ⟨⟨h.1, by omega⟩, by omega⟩⟩
      have e1 : ∑ x ∈ T, D.affinePeakSection k x (w'' x) =
          ∑ x ∈ T, D.affinePeakSection k x (w' x) :=
        Finset.sum_congr rfl fun x hx ↦ by simp [w'', (Finset.mem_filter.1 hx).2]
      have e2 : ∑ x ∈ U j, D.affinePeakSection k x (w'' x) =
          ∑ x ∈ U j, D.affinePeakSection k x (w x) :=
        Finset.sum_congr rfl fun x hx ↦ by simp [w'', (Finset.mem_filter.1 hx).2.ne]
      rw [h1, h2, e1, e2]
      simp only [s]
      abel
    refine ⟨w'', fun x hx ↦ ?_, fun x hx z hz ↦ ?_⟩
    · simp only [w'']
      split_ifs with hcx
      · exact (hw' x (Finset.mem_filter.2 ⟨hx, hcx⟩)).trans (hδ j)
      · exact hw x hx
    · rw [← hsum]
      obtain ⟨hxS, hxj⟩ := Finset.mem_filter.1 hx
      by_cases hcx : (c x : ℕ) = j
      · exact (hnew j hjN).trans (hT x (Finset.mem_filter.2 ⟨hxS, hcx⟩) z hz)
      · have := hb x (Finset.mem_filter.2 ⟨hxS, by omega⟩) z hz
        have := hall ((D.chart k x).symm z)
        linarith [hold j]

/-- **Global uniform transversality.** Let `M` be compact, Hausdorff, preconnected and
boundaryless, with the metric `g(u, w) = σ(u, J w)`, let `α` be a connection form and let `D` be
rescaled unitary charts of radius `ρ₀ > 0`. There are an asymptotically holomorphic sequence `s`
of sections, `s k` of `PowerBundle P k`, and `η > 0` such that `s` is uniformly transverse with
constant `η`: for all large `k` and every point `y`,
`η ≤ max ‖s k y‖ ((2π k)^(-1/2) ‖∂ (s k) y‖)`.

Milestone: *Global uniform transversality of asymptotically holomorphic sections*. -/
theorem exists_isUniformlyTransverse [CompactSpace M] [T2Space M] [I.Boundaryless]
    [PreconnectedSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [∀ y, Nonempty (P y)]
    (hg : ∀ (y : M) (v w : TangentSpace I y), inner ℝ v w = σ.eval₂ y v (J y w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ s : ∀ k : ℕ, Π y, PowerBundle P k y, D.IsAsymptoticallyHolomorphic s ∧
      ∃ η > 0, IsUniformlyTransverse J α η s := by
  classical
  set m := Module.finrank ℝ (StdSpace ι)
  obtain ⟨r₀, -, C₀, hnet⟩ := D.exists_separated_chart_cover_coloring hg hρ₀
  obtain ⟨C₅, _, -, H₂⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m 2
  obtain ⟨C₆, _, -, H₁⟩ := D.exists_jetNorm_sum_affinePeakSection_le hg hJ hα hρ₀ C₀ m 1
  set B := max (max C₅ 0) (max C₆ 0)
  obtain ⟨p, -, δ₀, hδ₀, C₁, C₂, c₂, hc₂, Hcorr⟩ :=
    D.exists_correction_of_separated hg hJ hα hρ₀ B C₀ m
  obtain ⟨R, hR, b, δ, hb, hδ, hold, hnew⟩ := exists_iteration_constants p m hδ₀
    (le_max_right C₁ 0) (le_max_right C₂ 0) hc₂ C₀
  set N₀ := ⌈C₀ * R ^ m⌉₊
  have hbanti : Antitone b := antitone_nat_of_succ_le fun j ↦ by
    have := hold j
    have := mul_nonneg (le_max_right C₁ 0) (hδ j).1.le
    linarith
  have hold' (j : ℕ) : b (j + 1) ≤ b j - C₁ * δ j := by
    have : C₁ * δ j ≤ max C₁ 0 * δ j := by gcongr; exacts [(hδ j).1.le, le_max_left _ _]
    linarith [hold j]
  have hnew' (j : ℕ) (hj : (j : ℝ) < C₀ * R ^ m) :
      b (j + 1) ≤ δ j / Real.log (1 / δ j) ^ p / 4 - C₂ * δ j * Real.exp (-c₂ * R ^ 2) := by
    have : C₂ * δ j * Real.exp (-c₂ * R ^ 2) ≤ max C₂ 0 * δ j * Real.exp (-c₂ * R ^ 2) := by
      gcongr; exacts [(hδ j).1.le, le_max_left _ _]
    linarith [hnew j hj]
  -- The bound `B` on the jets of all partial sums.
  have hBk : ∀ᶠ k : ℕ in Filter.atTop, ∀ (S : Finset M),
      (∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
        ((S.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m) →
      ∀ U ⊆ S, ∀ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ U, ‖w x‖ ≤ 1) → ∀ y,
        D.jetNorm k 2 (∑ x ∈ U, D.affinePeakSection k x (w x)) y ≤ B ∧
          D.dbarJetNorm k 1 (∑ x ∈ U, D.affinePeakSection k x (w x)) y ≤
            B * (k : ℝ) ^ (-1 / 2 : ℝ) := by
    filter_upwards [H₂, H₁] with k h₂ h₁ S hS U hU w hw y
    have hcount (ρ : ℝ) (hρ : 0 ≤ ρ) :
        ((U.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m :=
      le_trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hU))
        (hS y ρ hρ)
    obtain ⟨e₂, -, -⟩ := h₂ y U hcount 1 w zero_le_one hw
    obtain ⟨-, e₁, -⟩ := h₁ y U hcount 1 w zero_le_one hw
    have hB₅ : C₅ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
    have hB₆ : C₆ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
    rw [mul_one] at e₂ e₁
    exact ⟨e₂.trans hB₅, e₁.trans (by gcongr)⟩
  have hgood : ∀ᶠ k : ℕ in Filter.atTop, ∃ S : Finset M,
      (∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
        ((S.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m) ∧
      ∃ w : M → EuclideanSpace ℂ (Option ι), (∀ x ∈ S, ‖w x‖ ≤ 1) ∧
        ∀ y, b N₀ ≤ transversalityQuantity J α k (-∑ x ∈ S, D.affinePeakSection k x (w x)) y := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N₀ ↦ Hcorr (δ j) (hδ j).1 (hδ j).2.1,
      hBk, D.eventually_contDiffAt_reading_and_dbarReading_sum_affinePeakSection hρ₀,
      Filter.eventually_ge_atTop (max k₀ 1)] with k hck hBk hsm hk
    obtain ⟨S, -, hcover, hcount, hcol⟩ := hnet hk
    obtain ⟨N, hN, c, hc⟩ := hcol hR
    have hNN₀ : N ≤ N₀ := by exact_mod_cast hN.trans (Nat.le_ceil _)
    have hcount' (y : M) (ρ : ℝ) (hρ : 0 ≤ ρ) :
        ((S.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m :=
      hcount y hρ
    obtain ⟨w, hw, hlow⟩ := exists_forall_le_transversalityQuantity_of_coloring D c
      (fun j ↦ (hδ j).2.2) hold'
      (fun j hj ↦ hnew' j (lt_of_lt_of_le (by exact_mod_cast hj) hN)) hc hsm
      (hBk S hcount')
      (fun j hj T hT hsep ↦ hck ⟨j, hj.trans_le hNN₀⟩ T R (by linarith)
        (fun y ρ hρ ↦ le_trans (by exact_mod_cast (Finset.card_le_card
          (Finset.filter_subset_filter _ hT))) (hcount y hρ)) hsep)
    refine ⟨S, hcount', w, hw, fun y ↦ ?_⟩
    obtain ⟨x, hx, z, hz, rfl⟩ := hcover y
    exact (hbanti hNN₀).trans (hlow x hx z hz)
  -- Choose the centres and the coefficients for each `k`.
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.1 hgood
  have hch (k : ℕ) : ∃ (S : Finset M) (w : M → EuclideanSpace ℂ (Option ι)), k₁ ≤ k →
      (∀ (y : M) (ρ : ℝ), 0 ≤ ρ →
        ((S.filter fun x ↦ rescaledDist I k x y ≤ ρ).card : ℝ) ≤ C₀ * (1 + ρ) ^ m) ∧
      (∀ x ∈ S, ‖w x‖ ≤ 1) ∧
        ∀ y, b N₀ ≤ transversalityQuantity J α k (-∑ x ∈ S, D.affinePeakSection k x (w x)) y := by
    by_cases hk : k₁ ≤ k
    · obtain ⟨S, hS, w, hw, h⟩ := hk₁ k hk
      exact ⟨S, w, fun _ ↦ ⟨hS, hw, h⟩⟩
    · exact ⟨∅, 0, fun h ↦ absurd h hk⟩
  choose S w hSw using hch
  refine ⟨fun k ↦ -∑ x ∈ S k, D.affinePeakSection k x (w k x),
    (D.isAsymptoticallyHolomorphic_sum_affinePeakSection hg hJ hα hρ₀ S w zero_le_one
      (Filter.eventually_atTop.2 ⟨k₁, fun k hk ↦ (hSw k hk).1⟩)
      (Filter.eventually_atTop.2 ⟨k₁, fun k hk ↦ (hSw k hk).2.1⟩)).neg, b N₀, hb N₀,
    isUniformlyTransverse_def.2 (Filter.eventually_atTop.2 ⟨k₁, fun k hk ↦ (hSw k hk).2.2⟩)⟩

end Iteration

end RescaledUnitaryCharts

end SymplecticGeometry

end
