/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# Gaussian sums over sets of polynomial growth

Let `S` be a finite set of points of a pseudometric space and `y` a point, such that every closed
ball `closedBall y r` contains at most `C * (1 + r) ^ m` points of `S`. For a `1`-separated set
`S` in a metric measure space, Tau Ceti's `Metric.IsSeparated.card_mul_le_measure_cthickening`
gives this, with `C` and `m` independent of `y`, under two conditions: the balls of radius
`1 / 2` about the points of `S` have measure at least a fixed `μ₀ > 0`, and the closed
`1 / 2`-thickening of `closedBall y r` has measure at most a fixed multiple of `(1 + r) ^ m`.
Both hold, for instance, for a separated net in a compact manifold of real dimension `m` with a
rescaled metric. We bound sums over `S` of Gaussians
centred at `y`, with constants that depend only on `C`, `m` and the Gaussian, not on `S` or `y`.

## Main results

* `Metric.sum_inv_one_add_dist_pow_le`: `∑ x ∈ S, (1 + dist x y) ^ (-(m + 2)) ≤ 2 ^ (m + 1) * C`.
* `Metric.sum_one_add_dist_pow_mul_exp_le`: the sum of `(1 + dist x y) ^ k * exp (-c dist x y ^ 2)`
  over `S` is bounded by a constant depending only on `C`, `m`, `k` and `c`.
* `Metric.sum_one_add_dist_pow_mul_exp_le_of_le_dist`: the same sum over the points at distance
  at least `R ≥ 0` from `y` is at most a constant times `exp (-(c / 2) * R ^ 2)`.

The first bound splits `S` into the shells `j ≤ dist x y < j + 1`; the others follow from it and
Tau Ceti's bound `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le` for `(1 + r) ^ n * exp (-c r ^ 2)`.
A polynomial in `dist x y` is bounded by a multiple of `(1 + dist x y) ^ k`, so the bounds also
hold for sums of a polynomial times a Gaussian.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000]
-/

public section

open Finset Real
open scoped Nat

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {S : Finset X} {y : X} {C : ℝ} {m : ℕ}

/-- If every closed ball of radius `r` about `y` contains at most `C * (1 + r) ^ m` points of `S`,
then `∑ x ∈ S, ((1 + dist x y) ^ (m + 2))⁻¹ ≤ 2 ^ (m + 1) * C`. -/
theorem sum_inv_one_add_dist_pow_le
    (hS : ∀ r : ℝ, 0 ≤ r → (#{x ∈ S | dist x y ≤ r} : ℝ) ≤ C * (1 + r) ^ m) :
    ∑ x ∈ S, ((1 + dist x y) ^ (m + 2))⁻¹ ≤ 2 ^ (m + 1) * C := by
  have hC : 0 ≤ C := by simpa using (Nat.cast_nonneg _).trans (hS 0 le_rfl)
  set N := S.sup (fun x ↦ ⌊dist x y⌋₊) + 1
  have hmaps : ∀ x ∈ S, ⌊dist x y⌋₊ ∈ range N := fun x hx ↦
    mem_range.2 (Nat.lt_succ_of_le (le_sup (f := fun x ↦ ⌊dist x y⌋₊) hx))
  rw [← sum_fiberwise_of_maps_to hmaps]
  -- The shell `j ≤ dist x y < j + 1` contributes at most `2 ^ m * C / (1 + j) ^ 2`.
  have hshell : ∀ j ∈ range N, ∑ x ∈ S with ⌊dist x y⌋₊ = j, ((1 + dist x y) ^ (m + 2))⁻¹ ≤
      2 ^ m * C * ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    intro j _
    calc ∑ x ∈ S with ⌊dist x y⌋₊ = j, ((1 + dist x y) ^ (m + 2))⁻¹
        ≤ #{x ∈ S | ⌊dist x y⌋₊ = j} • ((1 + (j : ℝ)) ^ (m + 2))⁻¹ := by
          refine sum_le_card_nsmul _ _ _ fun x hx ↦ ?_
          have := Nat.floor_le (dist_nonneg (x := x) (y := y))
          rw [(mem_filter.1 hx).2] at this
          gcongr
      _ ≤ (C * (1 + (j + 1 : ℝ)) ^ m) * ((1 + (j : ℝ)) ^ (m + 2))⁻¹ := by
          rw [nsmul_eq_mul]
          gcongr
          refine le_trans (Nat.cast_le.2 (card_le_card fun x hx ↦ ?_))
            (hS (j + 1) (by positivity))
          refine mem_filter.2 ⟨(mem_filter.1 hx).1, ?_⟩
          have := Nat.lt_floor_add_one (dist x y)
          rw [(mem_filter.1 hx).2] at this
          exact this.le
      _ ≤ (C * (2 * (1 + j)) ^ m) * ((1 + (j : ℝ)) ^ (m + 2))⁻¹ := by
          gcongr
          linarith
      _ = 2 ^ m * C * ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
          rw [mul_pow]
          push_cast
          field_simp
          ring
  -- `∑ j < N, 1 / (j + 1) ^ 2 ≤ 2`.
  have hsum : ∑ j ∈ range N, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
    rw [range_eq_Ico, sum_Ico_add' (fun i : ℕ ↦ ((i : ℝ) ^ 2)⁻¹),
      Finset.Ico_add_one_left_eq_Ioo]
    exact h.trans (by norm_num)
  calc _ ≤ ∑ j ∈ range N, 2 ^ m * C * ((((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) := sum_le_sum hshell
    _ = 2 ^ m * C * ∑ j ∈ range N, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ := (mul_sum ..).symm
    _ ≤ 2 ^ m * C * 2 := by gcongr
    _ = 2 ^ (m + 1) * C := by ring

/-- If every closed ball of radius `r` about `y` contains at most `C * (1 + r) ^ m` points of `S`,
then for `0 < c` the sum of `(1 + dist x y) ^ k * exp (-c * dist x y ^ 2)` over `S` is at most
an explicit constant that depends only on `C`, `m`, `k` and `c`. -/
theorem sum_one_add_dist_pow_mul_exp_le
    (hS : ∀ r : ℝ, 0 ≤ r → (#{x ∈ S | dist x y ≤ r} : ℝ) ≤ C * (1 + r) ^ m)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∑ x ∈ S, (1 + dist x y) ^ k * exp (-c * dist x y ^ 2) ≤
      (k + m + 2)! / (c / 2) ^ (k + m + 2) * exp c * (2 ^ (m + 1) * C) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_inv_one_add_dist_pow_le hS)
    (by positivity))
  rw [mul_sum]
  refine sum_le_sum fun x _ ↦ ?_
  calc (1 + dist x y) ^ k * exp (-c * dist x y ^ 2)
      = (1 + dist x y) ^ (k + m + 2) * exp (-c * dist x y ^ 2) *
          ((1 + dist x y) ^ (m + 2))⁻¹ := by
        rw [add_assoc k, pow_add]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (TauCeti.one_add_pow_mul_exp_neg_mul_sq_le hc _)
        (by positivity)

/-- If every closed ball of radius `r` about `y` contains at most `C * (1 + r) ^ m` points of `S`,
then for `0 < c` and `0 ≤ R` the sum of `(1 + dist x y) ^ k * exp (-c * dist x y ^ 2)` over the
points of `S` at distance at least `R` from `y` is at most `exp (-(c / 2) * R ^ 2)` times a
constant that depends only on `C`, `m`, `k` and `c`. -/
theorem sum_one_add_dist_pow_mul_exp_le_of_le_dist
    (hS : ∀ r : ℝ, 0 ≤ r → (#{x ∈ S | dist x y ≤ r} : ℝ) ≤ C * (1 + r) ^ m)
    {c : ℝ} (hc : 0 < c) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∑ x ∈ S with R ≤ dist x y, (1 + dist x y) ^ k * exp (-c * dist x y ^ 2) ≤
      (k + m + 2)! / (c / 4) ^ (k + m + 2) * exp (c / 2) * (2 ^ (m + 1) * C) *
        exp (-(c / 2) * R ^ 2) := by
  have hmain : ∑ x ∈ S, (1 + dist x y) ^ k * exp (-(c / 2) * dist x y ^ 2) ≤
      (k + m + 2)! / (c / 4) ^ (k + m + 2) * exp (c / 2) * (2 ^ (m + 1) * C) := by
    have h4 : c / 2 / 2 = c / 4 := by ring
    simpa only [h4] using sum_one_add_dist_pow_mul_exp_le hS (half_pos hc) k
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hmain (exp_pos _).le)
  rw [sum_mul]
  refine (sum_le_sum fun x hx ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun x _ _ ↦ by positivity)
  have hRd : R ^ 2 ≤ dist x y ^ 2 := pow_le_pow_left₀ hR (mem_filter.1 hx).2 2
  rw [mul_assoc, ← exp_add]
  gcongr
  nlinarith

end Metric

end
