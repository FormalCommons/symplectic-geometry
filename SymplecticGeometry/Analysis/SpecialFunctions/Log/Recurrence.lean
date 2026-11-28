/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Growth of sequences with a logarithmic increment

Let `u : ℕ → ℝ` be nonnegative, with `0 ≤ p` and `0 < a`, and suppose that each step adds at
most a constant and a multiple of a logarithm of the current term:

`u (j + 1) ≤ u j + C + p * log (u j + a)`.

Then `u j` grows at most like `(j + 1) * log (j + 2)`.

* `Real.le_mul_mul_log_of_le_add_log`: the bound `u j ≤ K * (j + 1) * log (j + 2)` for every
  `j`, for each `K` that satisfies explicit inequalities in terms of `C`, `p`, `a` and `u 0`.
  Since these involve nothing else of `u`, the constant is uniform over a family of such
  sequences with the same `C`, `p`, `a` and a common bound on `u 0`.
* `Real.exists_le_mul_mul_log_of_le_add_log`: some `K` works.
* `Real.exists_exp_neg_le_of_le_add_log`: the same statement for `u j = log (1 / b j)`, read as a
  lower bound `exp (-(K * (j + 1) * log (j + 2))) ≤ b j` on positive numbers `b j ≤ 1`.

The proof is an induction on `j`. Since `(j + 1) * log (j + 2)` grows by at least `log (j + 3)`
from `j` to `j + 1`, it is enough that `C + p * log (u j + a) ≤ K * log (j + 3)`; under the
induction hypothesis, `log (u j + a)` is at most `log K + log (max a 1) + 2 * log (j + 3)`, and
`log (j + 3) ≥ 1`.

## References

This is the elementary estimate in the iteration over colours of the proof of Donaldson's
theorem on asymptotically holomorphic sections.

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

namespace Real

/-- A nonnegative real sequence with `u (j + 1) ≤ u j + C + p * log (u j + a)`, where `0 ≤ p`
and `0 < a`, satisfies `u j ≤ K * (j + 1) * log (j + 2)` for every `j`, for each `K ≥ 1` with
`2 * p ≤ K`, `C + p * (log K + log (max a 1) + 2) ≤ K` and `u 0 ≤ K * log 2`. -/
theorem le_mul_mul_log_of_le_add_log {u : ℕ → ℝ} {C p a K : ℝ} (hu : ∀ j, 0 ≤ u j)
    (hp : 0 ≤ p) (ha : 0 < a) (hK : 1 ≤ K) (hKp : 2 * p ≤ K)
    (hKC : C + p * (log K + log (max a 1) + 2) ≤ K) (h0 : u 0 ≤ K * log 2)
    (hrec : ∀ j, u (j + 1) ≤ u j + C + p * log (u j + a)) (j : ℕ) :
    u j ≤ K * (j + 1) * log (j + 2) := by
  induction j with
  | zero => simpa [one_add_one_eq_two] using h0
  | succ j ih =>
    have hcast₁ : ((j + 1 : ℕ) : ℝ) + 1 = j + 2 := by push_cast; ring
    have hcast₂ : ((j + 1 : ℕ) : ℝ) + 2 = j + 3 := by push_cast; ring
    rw [hcast₁, hcast₂]
    rw [mul_assoc] at ih
    set A := max a 1
    set L := log ((j : ℝ) + 3)
    set g := ((j : ℝ) + 1) * log ((j : ℝ) + 2)
    have : (0 : ℝ) ≤ j := j.cast_nonneg
    have hA : 1 ≤ A := le_max_right a 1
    have haA : a ≤ A := le_max_left a 1
    have hlog2 : 0 ≤ log ((j : ℝ) + 2) := log_nonneg (by linarith)
    have hg : 0 ≤ g := mul_nonneg (by linarith) hlog2
    -- `log (j + 3) ≥ log 3 ≥ 1`, since `exp 1 < 3`.
    have hL : 1 ≤ L := by
      rw [le_log_iff_exp_le (by positivity)]
      linarith [exp_one_lt_d9]
    -- `(j + 1) * log (j + 2)` grows by at least `log (j + 3)`.
    have hstep : g + L ≤ ((j : ℝ) + 2) * L := by
      have : log ((j : ℝ) + 2) ≤ L := log_le_log (by linarith) (by linarith)
      have : g ≤ ((j : ℝ) + 1) * L := mul_le_mul_of_nonneg_left this (by linarith)
      linarith
    -- Under the induction hypothesis, `log (u j + a) ≤ log K + log A + 2 * L`.
    have hgle : g ≤ ((j : ℝ) + 3) ^ 2 - 1 := by
      have : log ((j : ℝ) + 2) ≤ (j : ℝ) + 1 := by
        linarith [log_le_sub_one_of_pos (x := (j : ℝ) + 2) (by linarith)]
      nlinarith
    have hlog : log (u j + a) ≤ log K + log A + 2 * L := by
      have hKA : K * g + a ≤ K * A * ((j : ℝ) + 3) ^ 2 := by
        have h1 : K * g ≤ K * A * g := by
          nlinarith [mul_nonneg (mul_nonneg (zero_le_one.trans hK) hg) (sub_nonneg.2 hA)]
        have h2 : K * A * g ≤ K * A * (((j : ℝ) + 3) ^ 2 - 1) :=
          mul_le_mul_of_nonneg_left hgle (by positivity)
        nlinarith
      calc log (u j + a) ≤ log (K * A * ((j : ℝ) + 3) ^ 2) :=
            log_le_log (by linarith [hu j]) (by linarith)
        _ = log K + log A + 2 * L := by
            rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
              log_pow]
            push_cast
            ring
    calc u (j + 1) ≤ u j + C + p * log (u j + a) := hrec j
      _ ≤ K * g + C + p * (log K + log A + 2 * L) := by gcongr
      _ ≤ K * ((j : ℝ) + 2) * L := by
          nlinarith [mul_nonneg (sub_nonneg.2 hKp) (sub_nonneg.2 hL)]

/-- A nonnegative real sequence with `u (j + 1) ≤ u j + C + p * log (u j + a)`, where `0 ≤ p`
and `0 < a`, grows at most like `(j + 1) * log (j + 2)`. -/
theorem exists_le_mul_mul_log_of_le_add_log {u : ℕ → ℝ} {C p a : ℝ} (hu : ∀ j, 0 ≤ u j)
    (hp : 0 ≤ p) (ha : 0 < a) (hrec : ∀ j, u (j + 1) ≤ u j + C + p * log (u j + a)) :
    ∃ K, ∀ j, u j ≤ K * (j + 1) * log (j + 2) := by
  set B := |C| + p * (log (max a 1) + 2) + p * log (2 * (p + 1))
  have hA : 0 ≤ log (max a 1) := log_nonneg (le_max_right a 1)
  have hP : 0 ≤ log (2 * (p + 1)) := log_nonneg (by linarith)
  have hB : 0 ≤ B := by positivity
  set K := 1 + 2 * u 0 + 2 * p + 2 * B
  have hK : 1 ≤ K := by linarith [hu 0]
  refine ⟨K, le_mul_mul_log_of_le_add_log hu hp ha hK (by linarith [hu 0]) ?_ ?_ hrec⟩
  · -- `p * log K ≤ K / 2 + p * log (2 * (p + 1))`, from `log x ≤ x - 1` at
    -- `x = K / (2 * (p + 1))`.
    have hp1 : 0 < 2 * (p + 1) := by linarith
    set q := K / (2 * (p + 1)) with hqdef
    have hq : 0 < q := by positivity
    have hKq : K = 2 * (p + 1) * q := by rw [hqdef]; field_simp
    have hlog : log K ≤ q - 1 + log (2 * (p + 1)) := by
      have := log_le_sub_one_of_pos hq
      rw [log_div (by positivity) hp1.ne'] at this
      linarith
    have : p * log K ≤ K / 2 + p * log (2 * (p + 1)) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hp]
    linarith [le_abs_self C, hu 0]
  · nlinarith [mul_le_mul_of_nonneg_left log_two_gt_d9.le (zero_le_one.trans hK), hu 0]

/-- Positive numbers `b j ≤ 1` whose logarithms `u j = log (1 / b j)` satisfy
`u (j + 1) ≤ u j + C + p * log (u j + a)`, where `0 ≤ p` and `0 < a`, are bounded below by
`exp (-(K * (j + 1) * log (j + 2)))` for some `K`. -/
theorem exists_exp_neg_le_of_le_add_log {b : ℕ → ℝ} {C p a : ℝ} (hb : ∀ j, 0 < b j)
    (hb₁ : ∀ j, b j ≤ 1) (hp : 0 ≤ p) (ha : 0 < a)
    (hrec : ∀ j, log (1 / b (j + 1)) ≤ log (1 / b j) + C + p * log (log (1 / b j) + a)) :
    ∃ K, ∀ j : ℕ, exp (-(K * (j + 1) * log (j + 2))) ≤ b j := by
  obtain ⟨K, hK⟩ := exists_le_mul_mul_log_of_le_add_log
    (fun j ↦ log_nonneg (one_le_one_div (hb j) (hb₁ j))) hp ha hrec
  refine ⟨K, fun j ↦ ?_⟩
  have h := hK j
  rw [one_div, log_inv] at h
  rw [← exp_log (hb j)]
  exact exp_le_exp.2 (by linarith)

end Real

end
