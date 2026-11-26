/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import SymplecticGeometry.Analysis.Normed.Lp.PiLp
public import SymplecticGeometry.Analysis.Complex.Polydisc.HolomorphicApproximation
public import SymplecticGeometry.Analysis.Complex.Polydisc.TaylorTruncation
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.MeasureTheory.Measure.AlgebraicTube
import SymplecticGeometry.RingTheory.MvPolynomial.ImageHypersurface

/-!
# Auroux's avoidance estimate

This file proves Auroux's avoidance estimate: a map from a ball of `ℂⁿ` to `ℂⁿ⁺¹` whose
conjugate Wirtinger derivatives are small stays, quantitatively, away from some small value. Its
first step compares such a map with a polynomial map on polydiscs.

## Main results

* `SymplecticGeometry.exists_mvPolynomial_norm_sub_eval_le`: a `C¹` map
  `G : (σ → ℂ) → EuclideanSpace ℂ ι` with `‖G‖ ≤ M` and conjugate Wirtinger derivatives in the
  coordinate directions bounded by `ε` on the polydisc `closedBall c ρ` is, on the polydisc of a
  quarter of the radius, within `K * (ρ * ε + (1 + d) * (M + ρ * ε) / 2 ^ d)` of a polynomial
  map of degree at most `d` in `z - c`, with `K = card ι * 4 * 2 ^ card σ`.
* `SymplecticGeometry.exists_infDist_image_ge`: the avoidance estimate. For
  `card ι = card σ + 1` and `1 < R` there are `c > 0` and `δ₀ > 0` such that, for
  `0 < δ < δ₀` and `η = c δ / (log (1 / δ)) ^ (2 * card σ * card ι)`, every map
  `G : EuclideanSpace ℂ σ → EuclideanSpace ℂ ι` that is `C¹` on `ball 0 R`, with `‖G‖ ≤ 1` and
  conjugate Wirtinger derivatives in the coordinate directions bounded by `η` there, has a point
  `w` with `‖w‖ ≤ δ` at distance at least `η` from the image of the closed unit ball.

The polynomial map is the Taylor polynomial at `c` of the holomorphic approximation of
`SymplecticGeometry.exists_differentiableOn_dist_le`, taken one component at a time. That
approximation is within `4 (2 ^ n - 1) ρ ε` of `G` on `closedBall c (ρ / 2)`, where `n = card σ`,
so it is bounded there by `M + 4 (2 ^ n - 1) ρ ε`, and
`SymplecticGeometry.norm_sub_taylorPolynomial_le` on the polydisc of radius `ρ / 2` bounds the
error of its Taylor polynomials on `closedBall c (ρ / 4)`. For `ρ ≤ 0` the small polydisc is
empty or `{c}`, and constant polynomials do.

The avoidance estimate is assembled as in Auroux's proof. Finitely many polydiscs, whose
concentric polydiscs of four times the radius lie in `ball 0 R`, cover the closed unit ball; the
cover depends only on `card σ` and `R`. On each of them `G` is close to a polynomial map of
degree `d = ⌈3 log (1 / δ)⌉₊`, whose image lies in the zero set of a nonzero polynomial by
`SymplecticGeometry.exists_mvPolynomial_ne_zero_eval_eq_zero`. The product `Q` of these
polynomials has degree of order `d ^ card σ`, and the image of the unit ball lies near its zero
set. If every point of the ball of radius `δ` were within `η` of that image, this ball would lie
in a thin neighbourhood of the zero set of `Q`, whose volume
`MvPolynomial.volume_thickening_zeroLocus_inter_ball_le` bounds by less than the volume of the
ball. The comparison uses that `(log (1 / δ)) ^ k * δ` tends to `0` as `δ → 0`
(`Real.tendsto_pow_log_div_mul_add_atTop`).

## References

* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2.
-/

public section

open MeasureTheory Metric TauCeti

namespace SymplecticGeometry

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]

/-- **Polynomial approximation on a polydisc.** Let `G : (σ → ℂ) → EuclideanSpace ℂ ι` be `C¹`
near the closed polydisc `closedBall c ρ`, with `‖G‖ ≤ M` there and with its conjugate Wirtinger
derivatives `∂G/∂(conj z_j)` bounded by `ε` there. Then for every `d` there are polynomials
`P i` of total degree at most `d` such that on `closedBall c (ρ / 4)`,
`‖G z - (P i (z - c))_i‖ ≤ K * (ρ * ε + (1 + d) * (M + ρ * ε) / 2 ^ d)` with
`K = card ι * 4 * 2 ^ card σ`. -/
theorem exists_mvPolynomial_norm_sub_eval_le {G : (σ → ℂ) → EuclideanSpace ℂ ι} {c : σ → ℂ}
    {ρ ε M : ℝ} (hε : 0 ≤ ε) (hG : ∀ z ∈ closedBall c ρ, ContDiffAt ℝ 1 G z)
    (hM : ∀ z ∈ closedBall c ρ, ‖G z‖ ≤ M)
    (hdG : ∀ z ∈ closedBall c ρ, ∀ j, ‖conjWirtingerDeriv G z (Pi.single j 1)‖ ≤ ε) (d : ℕ) :
    ∃ P : ι → MvPolynomial σ ℂ, (∀ i, (P i).totalDegree ≤ d) ∧
      ∀ z ∈ closedBall c (ρ / 4),
        ‖G z - WithLp.toLp 2 (fun i ↦ MvPolynomial.eval (z - c) (P i))‖ ≤
          Fintype.card ι * 4 * 2 ^ Fintype.card σ *
            (ρ * ε + (1 + d) * (M + ρ * ε) / 2 ^ d) := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · -- The polydisc `closedBall c (ρ / 4)` is empty or `{c}`, where constants approximate `G`.
    refine ⟨fun i ↦ MvPolynomial.C (G c i), fun i ↦ by simp, fun z hz ↦ ?_⟩
    have hρ0 : ρ = 0 := le_antisymm hρ (by linarith [dist_nonneg.trans (mem_closedBall.1 hz)])
    subst hρ0
    rw [zero_div, closedBall_zero, Set.mem_singleton_iff] at hz
    subst hz
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z (mem_closedBall_self le_rfl))
    simp only [MvPolynomial.eval_C, WithLp.toLp_ofLp, sub_self, norm_zero]
    positivity
  obtain ⟨h, hh, hGh⟩ := exists_differentiableOn_dist_le hG hdG
  set A := 4 * (2 ^ Fintype.card σ - 1) * ρ * ε
  -- The components of `h` are holomorphic on `ball c ρ` and bounded by `M + A` on
  -- `closedBall c (ρ / 2)`.
  have hhi : ∀ i, DifferentiableOn ℂ (fun z ↦ h z i) (ball c (ρ / 2)) := fun i ↦
    (differentiableOn_euclidean.1 hh i).mono (ball_subset_ball (by linarith))
  have hhM : ∀ i, ∀ z ∈ ball c (ρ / 2), ‖h z i‖ ≤ M + A := fun i z hz ↦ by
    have hz' := ball_subset_closedBall hz
    have := hGh z hz'
    rw [dist_eq_norm'] at this
    calc ‖h z i‖ ≤ ‖h z‖ := PiLp.norm_apply_le _ i
      _ ≤ ‖G z‖ + ‖h z - G z‖ := norm_le_insert' _ _
      _ ≤ M + A := add_le_add (hM z (closedBall_subset_closedBall (by linarith) hz')) this
  refine ⟨fun i ↦ taylorPolynomial (fun z ↦ h z i) c d, fun i ↦ ?_, fun z hz ↦ ?_⟩
  · exact (totalDegree_taylorPolynomial_le _ c d).trans (Nat.sub_le d 1)
  have hc : c ∈ closedBall c ρ := mem_closedBall_self hρ.le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c hc)
  have h2 : (1 : ℝ) ≤ 2 ^ Fintype.card σ := one_le_pow₀ one_le_two
  have hA : A ≤ 4 * 2 ^ Fintype.card σ * (ρ * ε) := by
    simp only [A]
    have : 0 ≤ ρ * ε := mul_nonneg hρ.le hε
    nlinarith
  have hz2 : z ∈ closedBall c (ρ / 2) := closedBall_subset_closedBall (by linarith) hz
  -- The bound for each component.
  set B := 4 * 2 ^ Fintype.card σ * (ρ * ε + (1 + d) * (M + ρ * ε) / 2 ^ d)
  have hcomp : ∀ i, ‖G z i - MvPolynomial.eval (z - c)
      (taylorPolynomial (fun z ↦ h z i) c d)‖ ≤ B := fun i ↦ by
    have h1 : ‖G z i - h z i‖ ≤ A := by
      have := hGh z hz2
      rw [dist_eq_norm] at this
      exact (PiLp.norm_apply_le (G z - h z) i).trans this
    have h2' := norm_sub_taylorPolynomial_le (half_pos hρ) (hhi i) (hhM i) d
      (z := z) (by rwa [div_div, show (2 : ℝ) * 2 = 4 by norm_num])
    have hdiv : (1 + d) * (M + A) / 2 ^ d ≤
        4 * 2 ^ Fintype.card σ * ((1 + d) * (M + ρ * ε) / 2 ^ d) := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hMA : M + A ≤ 4 * 2 ^ Fintype.card σ * (M + ρ * ε) := by nlinarith
      nlinarith
    calc _ ≤ ‖G z i - h z i‖ + ‖h z i - MvPolynomial.eval (z - c)
          (taylorPolynomial (fun z ↦ h z i) c d)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ A + (1 + d) * (M + A) / 2 ^ d := add_le_add h1 h2'
      _ ≤ B := by simp only [B]; nlinarith
  -- The Euclidean norm is at most the sum of the norms of the components.
  set x := G z - WithLp.toLp 2 (fun i ↦ MvPolynomial.eval (z - c)
    (taylorPolynomial (fun z ↦ h z i) c d))
  calc ‖x‖ ≤ ∑ i, ‖x i‖ := PiLp.norm_le_sum_norm x
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ ↦ by simpa [x] using hcomp i
    _ = _ := by simp [B, mul_assoc]

omit [DecidableEq σ] in
/-- The closed unit ball of `EuclideanSpace ℂ σ` is covered by finitely many polydiscs
`closedBall c (ρ / 4)` whose concentric polydiscs `closedBall c ρ` lie in `ball 0 R`, when
`1 + card σ * ρ < R`. -/
private theorem exists_finset_polydisc_cover {R ρ : ℝ} (hρ : 0 < ρ)
    (hρR : 1 + Fintype.card σ * ρ < R) :
    ∃ T : Finset (σ → ℂ), (∀ c ∈ T, ∀ z ∈ closedBall c ρ,
      WithLp.toLp 2 z ∈ ball (0 : EuclideanSpace ℂ σ) R) ∧
      ∀ z ∈ closedBall (0 : EuclideanSpace ℂ σ) 1, ∃ c ∈ T, z.ofLp ∈ closedBall c (ρ / 4) := by
  have hS : IsCompact (WithLp.ofLp '' closedBall (0 : EuclideanSpace ℂ σ) 1) :=
    (isCompact_closedBall 0 1).image (PiLp.continuous_ofLp 2 _)
  obtain ⟨t, hts, ht, hcover⟩ := finite_cover_balls_of_compact hS (by positivity : 0 < ρ / 4)
  refine ⟨ht.toFinset, fun c hc z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨c', hc', rfl⟩ := hts hc
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_closedBall_zero_iff] at hc'
    have hsplit : WithLp.toLp 2 z = c' + WithLp.toLp 2 (z - c'.ofLp) := by ext; simp
    have hsum : ‖WithLp.toLp 2 (z - c'.ofLp)‖ ≤ Fintype.card σ * ρ := by
      calc _ ≤ ∑ i, ‖WithLp.toLp 2 (z - c'.ofLp) i‖ := PiLp.norm_le_sum_norm _
        _ ≤ ∑ _i : σ, ρ := Finset.sum_le_sum fun i _ ↦ (norm_le_pi_norm (z - c'.ofLp) i).trans hz
        _ = _ := by simp
    rw [mem_ball_zero_iff, hsplit]
    linarith [norm_add_le c' (WithLp.toLp 2 (z - c'.ofLp))]
  · obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.1 (hcover ⟨z, hz, rfl⟩)
    exact ⟨c, ht.mem_toFinset.2 hc, ball_subset_closedBall hzc⟩

/-- On a finite cover of the closed unit ball by polydiscs as in `exists_finset_polydisc_cover`,
the image of the unit ball under a map `G` with `‖G‖ ≤ 1` and conjugate Wirtinger derivatives in
the coordinate directions bounded by `ε` lies near the zero set of one nonzero polynomial: the
product of the polynomials that vanish on the images of the polynomial approximations of `G` on
the polydiscs. -/
private theorem exists_zeroLocus_near_image (hι : Fintype.card ι = Fintype.card σ + 1)
    {R ρ ε : ℝ} {T : Finset (σ → ℂ)}
    (hT : ∀ c ∈ T, ∀ z ∈ closedBall c ρ, WithLp.toLp 2 z ∈ ball (0 : EuclideanSpace ℂ σ) R)
    (hcov : ∀ z ∈ closedBall (0 : EuclideanSpace ℂ σ) 1, ∃ c ∈ T, z.ofLp ∈ closedBall c (ρ / 4))
    {G : EuclideanSpace ℂ σ → EuclideanSpace ℂ ι} (hε : 0 ≤ ε)
    (hG : ∀ z ∈ ball 0 R, ContDiffAt ℝ 1 G z) (hM : ∀ z ∈ ball 0 R, ‖G z‖ ≤ 1)
    (hdG : ∀ z ∈ ball 0 R, ∀ j,
      ‖conjWirtingerDeriv G z (EuclideanSpace.single j 1)‖ ≤ ε) {d : ℕ} (hd : 1 ≤ d) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      Q.totalDegree ≤ T.card * ((Fintype.card σ + 1).factorial * d ^ Fintype.card σ) ∧
      ∀ z ∈ closedBall (0 : EuclideanSpace ℂ σ) 1, ∃ y : EuclideanSpace ℂ ι,
        MvPolynomial.eval y.ofLp Q = 0 ∧
        dist (G z) y ≤ Fintype.card ι * 4 * 2 ^ Fintype.card σ *
          (ρ * ε + (1 + d) * (1 + ρ * ε) / 2 ^ d) := by
  set e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : σ ↦ ℂ)).symm
  have hP : ∀ c ∈ T, ∃ P : ι → MvPolynomial σ ℂ, (∀ i, (P i).totalDegree ≤ d) ∧
      ∀ z ∈ closedBall c (ρ / 4),
        ‖(G ∘ e) z - WithLp.toLp 2 (fun i ↦ MvPolynomial.eval (z - c) (P i))‖ ≤
          Fintype.card ι * 4 * 2 ^ Fintype.card σ *
            (ρ * ε + (1 + d) * (1 + ρ * ε) / 2 ^ d) := fun c hc ↦
    exists_mvPolynomial_norm_sub_eval_le hε
      (fun z hz ↦ (hG _ (hT c hc z hz)).comp z
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : σ ↦ ℂ)).symm.contDiff.contDiffAt)
      (fun z hz ↦ hM _ (hT c hc z hz))
      (fun z hz j ↦ by
        rw [← PiLp.coe_symm_continuousLinearEquiv (𝕜 := ℂ),
          conjWirtingerDeriv_comp_continuousLinearEquiv]
        simpa [e, PiLp.toLp_single] using hdG _ (hT c hc z hz) j) d
  choose! P hPd hPG using hP
  have hQ : ∀ c ∈ T, ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      Q.totalDegree ≤ (Fintype.card σ + 1).factorial * d ^ Fintype.card σ ∧
      ∀ x : σ → ℂ, MvPolynomial.eval (fun i ↦ MvPolynomial.eval x (P c i)) Q = 0 :=
    fun c hc ↦ exists_mvPolynomial_ne_zero_eval_eq_zero hι hd (P c) (hPd c hc)
  choose! Q hQ0 hQd hQe using hQ
  refine ⟨∏ c ∈ T, Q c, Finset.prod_ne_zero_iff.2 hQ0, ?_, fun z hz ↦ ?_⟩
  · calc _ ≤ ∑ c ∈ T, (Q c).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ _c ∈ T, (Fintype.card σ + 1).factorial * d ^ Fintype.card σ :=
        Finset.sum_le_sum hQd
      _ = _ := by simp
  obtain ⟨c, hc, hzc⟩ := hcov z hz
  refine ⟨WithLp.toLp 2 (fun i ↦ MvPolynomial.eval (z.ofLp - c) (P c i)), ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_zero hc (hQe c hc _)
  · rw [dist_eq_norm]
    simpa [e] using hPG c hc _ hzc
/-- If the ball of radius `δ` lies in the `t`-neighbourhood of the zero set of a nonzero
polynomial of degree at most `D` on `ℂ^ι`, then `t` is at least a constant times
`δ / D ^ (2 * card ι)`: this is the tube-volume bound
`MvPolynomial.volume_thickening_zeroLocus_inter_ball_le` on `ball 0 δ`. -/
private theorem exists_mul_le_of_ball_subset_thickening :
    ∃ C > 0, ∀ Q : MvPolynomial ι ℂ, Q ≠ 0 → ∀ D : ℕ, Q.totalDegree ≤ D → ∀ δ, 0 < δ →
      ∀ t, ball (0 : EuclideanSpace ℂ ι) δ ⊆
          thickening t {z : EuclideanSpace ℂ ι | MvPolynomial.eval z.ofLp Q = 0} →
        volume.real (ball (0 : EuclideanSpace ℂ ι) 1) * δ ≤
          C * D ^ (2 * Fintype.card ι) * t := by
  obtain ⟨C₀, hC₀⟩ := MvPolynomial.volume_thickening_zeroLocus_inter_ball_le (ι := ι)
  refine ⟨max C₀ 1, lt_max_of_lt_right one_pos, fun Q hQ0 D hQd δ hδ t hsub ↦ ?_⟩
  set m := Fintype.card ι
  set V := volume.real (ball (0 : EuclideanSpace ℂ ι) 1)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have ht0 : 0 ≤ t := by
    by_contra! ht
    have := hsub (mem_ball_self hδ)
    rwa [thickening_of_nonpos ht.le] at this
  have hvol := (measure_mono (Set.subset_inter hsub subset_rfl)).trans (hC₀ Q hQ0 D hQd δ hδ t)
  rw [Measure.addHaar_ball_of_pos _ _ hδ, finrank_real_of_complex, finrank_euclideanSpace,
    ← ofReal_measureReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff'] at hvol
  have hvol' : δ ^ (2 * m) * V ≤ δ ^ (2 * m) * (max C₀ 1 * D ^ (2 * m) * t / δ) := by
    calc _ ≤ C₀ * D ^ (2 * m) * δ ^ (2 * m) * (t / δ) :=
          hvol.resolve_right (not_le.2 (by positivity))
      _ ≤ max C₀ 1 * D ^ (2 * m) * δ ^ (2 * m) * (t / δ) := by gcongr; exact le_max_left _ _
      _ = _ := by ring
  exact (le_div_iff₀ hδ).1 (le_of_mul_le_mul_left hvol' (by positivity))

/-- The choice of the degree in the avoidance estimate: for `1 < L`, the degree `d = ⌈3 L⌉₊` is
positive, at most `4 L`, and `2 ^ d` is at least `exp (2 L)`. -/
private theorem natCeil_three_mul_bounds {L : ℝ} (hL : 1 < L) :
    1 ≤ ⌈3 * L⌉₊ ∧ (⌈3 * L⌉₊ : ℝ) ≤ 4 * L ∧ Real.exp (2 * L) ≤ 2 ^ ⌈3 * L⌉₊ := by
  have hd3 : 3 * L ≤ ⌈3 * L⌉₊ := Nat.le_ceil _
  have hd4 : (⌈3 * L⌉₊ : ℝ) ≤ 4 * L := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * L)
    linarith
  refine ⟨by exact_mod_cast (show (1 : ℝ) ≤ ⌈3 * L⌉₊ by linarith), hd4, ?_⟩
  calc Real.exp (2 * L) ≤ Real.exp (⌈3 * L⌉₊ * Real.log 2) :=
        Real.exp_le_exp.2 (by nlinarith [Real.log_two_gt_d9])
    _ = 2 ^ ⌈3 * L⌉₊ := by rw [Real.exp_natCast_mul, Real.exp_log two_pos]

/-- The final comparison in the avoidance estimate: with `η = c δ / L ^ p`, the width
`η + K (ρ η + (1 + d) (1 + ρ η) / 2 ^ d)` of the neighbourhood of the zero set, times
`B d ^ p`, is at most `V δ / 2`, once `c` and `L ^ (p + 1) δ` are small enough. -/
private theorem mul_width_le {B K ρ V δ L c θ : ℝ} {p d : ℕ} (hB : 0 < B) (hK : 0 ≤ K)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hL : 1 < L) (hc : 0 ≤ c) (hd1 : 1 ≤ d) (hd4 : (d : ℝ) ≤ 4 * L)
    (h2d : 1 / δ ^ 2 ≤ 2 ^ d) (hcV : c * (4 * B * 4 ^ p * (1 + K * ρ)) ≤ V)
    (hθV : 8 * B * K * (1 + ρ) * 4 ^ (p + 1) * θ ≤ V) (hLδ : L ^ (p + 1) * δ < θ)
    (hη1 : c * δ / L ^ p ≤ 1) :
    B * d ^ p * (c * δ / L ^ p + K * (ρ * (c * δ / L ^ p) +
      (1 + d) * (1 + ρ * (c * δ / L ^ p)) / 2 ^ d)) ≤ V * δ / 2 := by
  set η := c * δ / L ^ p
  have hLη : L ^ p * η = c * δ := by simp only [η]; field_simp
  have hdp : (d : ℝ) ^ p ≤ 4 ^ p * L ^ p := by
    rw [← mul_pow]
    gcongr
  have hdd : (d : ℝ) ^ p * (1 + d) ≤ 2 * (4 ^ (p + 1) * L ^ (p + 1)) := by
    have h1 : (1 : ℝ) + d ≤ 2 * d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      linarith
    calc (d : ℝ) ^ p * (1 + d) ≤ d ^ p * (2 * d) := by gcongr
      _ = 2 * (d : ℝ) ^ (p + 1) := by ring
      _ ≤ 2 * (4 * L) ^ (p + 1) := by gcongr
      _ = _ := by rw [mul_pow]
  have h2d' : 1 / (2 : ℝ) ^ d ≤ δ ^ 2 :=
    (one_div_le (by positivity) (by positivity)).2 h2d
  have hE₁ : B * d ^ p * (η * (1 + K * ρ)) ≤ V * δ / 4 := by
    calc B * d ^ p * (η * (1 + K * ρ)) ≤ B * (4 ^ p * L ^ p) * (η * (1 + K * ρ)) := by gcongr
      _ = B * 4 ^ p * (1 + K * ρ) * (c * δ) := by rw [← hLη]; ring
      _ ≤ V * δ / 4 := by
          have := mul_le_mul_of_nonneg_right hcV hδ.le
          linarith
  have hE₂ : B * d ^ p * (K * (1 + d) * (1 + ρ * η) / 2 ^ d) ≤ V * δ / 4 := by
    calc B * d ^ p * (K * (1 + d) * (1 + ρ * η) / 2 ^ d) =
          B * K * (1 + ρ * η) * ((d : ℝ) ^ p * (1 + d)) * (1 / 2 ^ d) := by ring
      _ ≤ B * K * (1 + ρ) * (2 * (4 ^ (p + 1) * L ^ (p + 1))) * δ ^ 2 := by
          gcongr
          nlinarith
      _ = 2 * B * K * (1 + ρ) * 4 ^ (p + 1) * δ * (L ^ (p + 1) * δ) := by ring
      _ ≤ 2 * B * K * (1 + ρ) * 4 ^ (p + 1) * δ * θ := by gcongr
      _ ≤ V * δ / 4 := by
          have := mul_le_mul_of_nonneg_right hθV hδ.le
          linarith
  have hsplit : B * d ^ p * (η + K * (ρ * η + (1 + d) * (1 + ρ * η) / 2 ^ d)) =
      B * d ^ p * (η * (1 + K * ρ)) + B * d ^ p * (K * (1 + d) * (1 + ρ * η) / 2 ^ d) := by
    ring
  linarith

/-- **Auroux's avoidance estimate.** Let `card ι = card σ + 1` and `1 < R`. There are constants
`c > 0` and `δ₀ > 0` such that for every `0 < δ < δ₀`, with `η = c δ / (log (1 / δ)) ^ p₀` and
`p₀ = 2 * card σ * card ι`, the following holds. If `G : ℂ^σ → ℂ^ι` is `C¹` on `ball 0 R`, with
`‖G‖ ≤ 1` and conjugate Wirtinger derivatives in the coordinate directions bounded by `η` there,
then some `w` with `‖w‖ ≤ δ` lies at distance at least `η` from the image of the closed unit
ball under `G`. -/
theorem exists_infDist_image_ge (hι : Fintype.card ι = Fintype.card σ + 1) {R : ℝ}
    (hR : 1 < R) :
    ∃ c > 0, ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ∀ G : EuclideanSpace ℂ σ → EuclideanSpace ℂ ι,
        (∀ z ∈ ball 0 R, ContDiffAt ℝ 1 G z) → (∀ z ∈ ball 0 R, ‖G z‖ ≤ 1) →
        (∀ z ∈ ball 0 R, ∀ j, ‖conjWirtingerDeriv G z (EuclideanSpace.single j 1)‖ ≤
          c * δ / Real.log (1 / δ) ^ (2 * Fintype.card σ * Fintype.card ι)) →
        ∃ w : EuclideanSpace ℂ ι, ‖w‖ ≤ δ ∧
          c * δ / Real.log (1 / δ) ^ (2 * Fintype.card σ * Fintype.card ι) ≤
            infDist w (G '' closedBall 0 1) := by
  set s := Fintype.card σ
  set m := Fintype.card ι
  set p := 2 * s * m
  -- The cover by polydiscs, chosen once for all `δ`.
  set ρ := (R - 1) / (s + 1)
  have hρ : 0 < ρ := div_pos (by linarith) (by positivity)
  have hρR : 1 + s * ρ < R := by
    have : (s + 1) * ρ = R - 1 := mul_div_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨T, hT, hcov⟩ := exists_finset_polydisc_cover hρ hρR
  have hT0 : T.Nonempty := by
    obtain ⟨c, hc, -⟩ := hcov 0 (mem_closedBall_self zero_le_one)
    exact ⟨c, hc⟩
  obtain ⟨C, hC, hvol⟩ := exists_mul_le_of_ball_subset_thickening (ι := ι)
  set K : ℝ := m * 4 * 2 ^ s
  set A : ℝ := T.card * (s + 1).factorial
  set V := volume.real (ball (0 : EuclideanSpace ℂ ι) 1)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  set B := C * A ^ (2 * m)
  have hB : 0 < B := by
    have := hT0.card_pos
    positivity
  have hK : 0 ≤ K := by positivity
  set θ := V / (8 * B * K * (1 + ρ) * 4 ^ (p + 1) + 1)
  have hθ : 0 < θ := by positivity
  set c := min 1 (V / (4 * B * 4 ^ p * (1 + K * ρ)))
  have hc : 0 < c := lt_min one_pos (by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 <| (tendsto_order.1
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (p + 1) one_ne_zero)).2 θ hθ
  refine ⟨c, hc, min (Real.exp (-1)) (1 / max X 1), by positivity,
    fun δ hδ hδ₀ G hG hM hdG ↦ ?_⟩
  have hδ1 : δ < Real.exp (-1) := hδ₀.trans_le (min_le_left _ _)
  have hδX : max X 1 < 1 / δ :=
    (lt_one_div hδ (by positivity)).1 (hδ₀.trans_le (min_le_right _ _))
  have hδ1' : δ < 1 := hδ1.trans (by simp)
  set L := Real.log (1 / δ)
  have hL : 1 < L := by
    rw [Real.lt_log_iff_exp_lt (by positivity), lt_one_div (Real.exp_pos 1) hδ, one_div,
      ← Real.exp_neg]
    exact hδ1
  have hLδ : L ^ (p + 1) * δ < θ := by
    have h := hX (1 / δ) ((le_max_left _ _).trans hδX.le)
    have e : L ^ (p + 1) / (1 * (1 / δ) + 0) = L ^ (p + 1) * δ := by
      rw [one_mul, add_zero, div_div_eq_mul_div, div_one]
    rwa [e] at h
  set η := c * δ / L ^ p
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := by
    have hcδ : c * δ ≤ 1 := by nlinarith [min_le_left 1 (V / (4 * B * 4 ^ p * (1 + K * ρ)))]
    have : 1 ≤ L ^ p := one_le_pow₀ hL.le
    exact (div_le_one (by positivity)).2 (hcδ.trans this)
  -- The degree of the polynomial approximations.
  set d := ⌈3 * L⌉₊
  obtain ⟨hd1, hd4, hexp⟩ := natCeil_three_mul_bounds hL
  have h2d : 1 / δ ^ 2 ≤ 2 ^ d := by
    calc 1 / δ ^ 2 = Real.exp L ^ 2 := by rw [Real.exp_log (by positivity)]; ring
      _ = Real.exp (2 * L) := by rw [← Real.exp_natCast_mul]; norm_num
      _ ≤ 2 ^ d := hexp
  obtain ⟨Q, hQ0, hQd, hQG⟩ := exists_zeroLocus_near_image hι hT hcov hη0 hG hM hdG hd1
  set D := T.card * ((s + 1).factorial * d ^ s)
  by_contra! hcon
  -- Otherwise the parameter ball of radius `δ` lies in a thin neighbourhood of the zero set.
  set t := η + K * (ρ * η + (1 + d) * (1 + ρ * η) / 2 ^ d)
  set Z := {z : EuclideanSpace ℂ ι | MvPolynomial.eval z.ofLp Q = 0}
  have hsub : ball (0 : EuclideanSpace ℂ ι) δ ⊆ thickening t Z := by
    intro w hw
    obtain ⟨_, ⟨z, hz, rfl⟩, hwz⟩ :=
      (infDist_lt_iff ((nonempty_closedBall.2 zero_le_one).image G)).1
        (hcon w (mem_ball_zero_iff.1 hw).le)
    obtain ⟨y, hy, hzy⟩ := hQG z hz
    exact mem_thickening_iff.2
      ⟨y, hy, (dist_triangle w (G z) y).trans_lt (add_lt_add_of_lt_of_le hwz hzy)⟩
  have hmain := hvol Q hQ0 D hQd δ hδ t hsub
  -- But the volume of that neighbourhood is too small.
  have hD : C * (D : ℝ) ^ (2 * m) = B * (d : ℝ) ^ p := by
    simp only [D, B, A, p]
    push_cast
    ring
  have hcV : c * (4 * B * 4 ^ p * (1 + K * ρ)) ≤ V :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hθV : 8 * B * K * (1 + ρ) * 4 ^ (p + 1) * θ ≤ V := by
    have : θ * (8 * B * K * (1 + ρ) * 4 ^ (p + 1) + 1) = V := div_mul_cancel₀ _ (by positivity)
    linarith
  have := mul_width_le hB hK hρ hδ hL hc.le hd1 hd4 h2d hcV hθV hLδ hη1
  rw [hD] at hmain
  linarith [mul_pos hV hδ]

end SymplecticGeometry

end
