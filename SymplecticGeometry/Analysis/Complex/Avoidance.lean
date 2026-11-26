/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import SymplecticGeometry.Analysis.Normed.Lp.PiLp
import SymplecticGeometry.Analysis.Complex.Polydisc.HolomorphicApproximation
import SymplecticGeometry.Analysis.Complex.Polydisc.TaylorTruncation

/-!
# Auroux's avoidance estimate

This file proves the estimate through which Auroux's avoidance argument compares an
approximately holomorphic map with a polynomial map.

## Main results

* `SymplecticGeometry.exists_mvPolynomial_norm_sub_eval_le`: a `C¹` map
  `G : (σ → ℂ) → EuclideanSpace ℂ ι` with `‖G‖ ≤ M` and conjugate Wirtinger derivatives in the
  coordinate directions bounded by `ε` on the polydisc `closedBall c ρ` is, on the polydisc of a
  quarter of the radius, within `K * (ρ * ε + (1 + d) * (M + ρ * ε) / 2 ^ d)` of a polynomial
  map of degree at most `d` in `z - c`, with `K = card ι * 4 * 2 ^ card σ`.

The polynomial map is the Taylor polynomial at `c` of the holomorphic approximation of
`SymplecticGeometry.exists_differentiableOn_dist_le`, taken one component at a time. That
approximation is within `4 (2 ^ n - 1) ρ ε` of `G` on `closedBall c (ρ / 2)`, where `n = card σ`,
so it is bounded there by `M + 4 (2 ^ n - 1) ρ ε`, and
`SymplecticGeometry.norm_sub_taylorPolynomial_le` on the polydisc of radius `ρ / 2` bounds the
error of its Taylor polynomials on `closedBall c (ρ / 4)`. For `ρ ≤ 0` the small polydisc is
empty or `{c}`, and constant polynomials do.

## References

* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2.
-/

public section

open Metric TauCeti

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

end SymplecticGeometry

end
