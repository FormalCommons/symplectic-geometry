/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian bounds under a change of variable

* `Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul`: a bound of the form
  `(1 + t) ^ N * exp (-c * t ^ 2)` gives one of the same form in any `d ≥ 0` comparable to `t`,
  with a smaller exponent `c / b ^ 2` and a constant factor. This is how a Gaussian decay in
  the coordinates of a chart becomes one in a distance comparable to them, as in the decay of
  Donaldson's peak sections.
* `Real.one_add_pow_mul_exp_neg_mul_sq_le_of_le`: for `t ≥ 0`, the weight
  `(1 + t) ^ N * exp (-c * t ^ 2)` grows with `N` and decreases as `c` grows.
* `Real.exists_forall_le_one_add_pow_mul_exp_neg_mul_sq`: finitely many eventual Gaussian bounds
  in a nonnegative `d`, each with its own nonnegative weight, hold with one set of constants.
* `Real.exists_le_one_add_pow_mul_exp_neg_mul_sq_and_le`: the case of two bounds, the first
  unweighted.
* `Real.exp_neg_mul_max_sub_sq_le`: for `R ≥ 0`, a Gaussian in `max (R - a) 0` is at most a
  constant times a Gaussian in `R` with half the exponent.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

namespace Real

/-- A Gaussian bound in `t` is one in any `d ≥ 0` comparable to `t`: if `t ≤ a * d` and
`d ≤ b * t` with `b > 0`, then for `c ≥ 0`,
`(1 + t) ^ N * exp (-c * t ^ 2) ≤ max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2)`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le_of_le_mul {t d a b c : ℝ} (N : ℕ) (hd : 0 ≤ d)
    (hb : 0 < b) (hc : 0 ≤ c) (htd : t ≤ a * d) (hdt : d ≤ b * t) :
    (1 + t) ^ N * exp (-c * t ^ 2) ≤
      max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2) := by
  have ht : 0 ≤ t := by nlinarith
  have hpoly : (1 + t) ^ N ≤ (max a 1 * (1 + d)) ^ N :=
    pow_le_pow_left₀ (by linarith)
      (by nlinarith [mul_le_mul_of_nonneg_right (le_max_left a 1) hd, le_max_right a 1]) N
  have hexp : exp (-c * t ^ 2) ≤ exp (-(c / b ^ 2) * d ^ 2) := by
    have h : c / b ^ 2 * d ^ 2 ≤ c * t ^ 2 :=
      calc c / b ^ 2 * d ^ 2 ≤ c / b ^ 2 * (b * t) ^ 2 := by gcongr
        _ = c * t ^ 2 := by field_simp
    exact exp_le_exp.2 (by linarith)
  calc (1 + t) ^ N * exp (-c * t ^ 2) ≤ (max a 1 * (1 + d)) ^ N * exp (-(c / b ^ 2) * d ^ 2) :=
        mul_le_mul hpoly hexp (exp_pos _).le (by positivity)
    _ = max a 1 ^ N * (1 + d) ^ N * exp (-(c / b ^ 2) * d ^ 2) := by rw [mul_pow]

/-- For `t ≥ 0`, the weight `(1 + t) ^ N * exp (-c * t ^ 2)` is monotone in `N` and antitone
in `c`: if `N ≤ N'` and `c' ≤ c`, then
`(1 + t) ^ N * exp (-c * t ^ 2) ≤ (1 + t) ^ N' * exp (-c' * t ^ 2)`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le_of_le {t c c' : ℝ} {N N' : ℕ} (ht : 0 ≤ t)
    (hN : N ≤ N') (hc : c' ≤ c) :
    (1 + t) ^ N * exp (-c * t ^ 2) ≤ (1 + t) ^ N' * exp (-c' * t ^ 2) := by
  gcongr
  linarith

/-- Finitely many eventual Gaussian bounds in `d ≥ 0`, each with its own weight `w j k ≥ 0`, hold
with one set of constants: if for each `j` of a finite type there are `C_j`, `N_j` and `c_j > 0`
such that eventually along `l`, for all `i`,
`F j k i ≤ C_j * w j k * (1 + d k i) ^ N_j * exp (-c_j * d k i ^ 2)`, then for some `C ≥ 0`, `N`
and `c > 0`, eventually along `l`, for all `j` and `i`, the same bound holds with `C`, `N` and
`c` in place of `C_j`, `N_j` and `c_j`. -/
theorem exists_forall_le_one_add_pow_mul_exp_neg_mul_sq {κ ι α : Type*} [Finite κ]
    {l : Filter ι} {F : κ → ι → α → ℝ} {d : ι → α → ℝ} {w : κ → ι → ℝ} (hd : ∀ k i, 0 ≤ d k i)
    (hw : ∀ j k, 0 ≤ w j k)
    (h : ∀ j, ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in l, ∀ i,
      F j k i ≤ C * w j k * (1 + d k i) ^ N * exp (-c * d k i ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in l, ∀ j i,
      F j k i ≤ C * w j k * (1 + d k i) ^ N * exp (-c * d k i ^ 2) := by
  have := Fintype.ofFinite κ
  choose C N c hc h using h
  have hC₀ : 0 ≤ ∑ j, max (C j) 0 := Finset.sum_nonneg fun _ _ ↦ le_max_right _ _
  have hc₀ : 0 ≤ ∑ j, (c j)⁻¹ := Finset.sum_nonneg fun j _ ↦ (inv_pos.2 (hc j)).le
  refine ⟨∑ j, max (C j) 0, hC₀, ∑ j, N j, (1 + ∑ j, (c j)⁻¹)⁻¹,
    inv_pos.2 (by linarith), ?_⟩
  filter_upwards [Filter.eventually_all.2 h] with k hk j i
  have ht : 0 ≤ 1 + d k i := by linarith [hd k i]
  have hcj : (1 + ∑ j, (c j)⁻¹)⁻¹ ≤ c j := by
    rw [inv_le_comm₀ (by linarith) (hc j)]
    linarith [Finset.single_le_sum (f := fun j ↦ (c j)⁻¹)
      (fun j _ ↦ (inv_pos.2 (hc j)).le) (Finset.mem_univ j)]
  have hC : C j ≤ ∑ j, max (C j) 0 := (le_max_left _ _).trans
    (Finset.single_le_sum (f := fun j ↦ max (C j) 0) (fun _ _ ↦ le_max_right _ _)
      (Finset.mem_univ j))
  have e := one_add_pow_mul_exp_neg_mul_sq_le_of_le (hd k i)
    (Finset.single_le_sum (f := N) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)) hcj
  calc F j k i ≤ C j * w j k * ((1 + d k i) ^ N j * exp (-c j * d k i ^ 2)) :=
        (hk j i).trans_eq (by ring)
    _ ≤ (∑ j, max (C j) 0) * w j k *
          ((1 + d k i) ^ (∑ j, N j) * exp (-(1 + ∑ j, (c j)⁻¹)⁻¹ * d k i ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC (hw j k)) e
          (mul_nonneg (pow_nonneg ht _) (exp_pos _).le) (mul_nonneg hC₀ (hw j k))
    _ = _ := by ring

/-- Two eventual Gaussian bounds in `d ≥ 0`, the second with a weight `w k ≥ 0`, hold with one
set of constants: if eventually along `l`, for all `i`,
`F k i ≤ C₁ * (1 + d k i) ^ N₁ * exp (-c₁ * d k i ^ 2)` and
`G k i ≤ C₂ * w k * (1 + d k i) ^ N₂ * exp (-c₂ * d k i ^ 2)`, with `c₁ > 0` and `c₂ > 0`, then
for some `C ≥ 0`, `N` and `c > 0`, eventually along `l`, for all `i`, both bounds hold with
`C`, `N` and `c` in place of their constants. -/
theorem exists_le_one_add_pow_mul_exp_neg_mul_sq_and_le {ι α : Type*} {l : Filter ι}
    {F G d : ι → α → ℝ} {w : ι → ℝ} (hd : ∀ k i, 0 ≤ d k i) (hw : ∀ k, 0 ≤ w k)
    (h₁ : ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in l, ∀ i,
      F k i ≤ C * (1 + d k i) ^ N * exp (-c * d k i ^ 2))
    (h₂ : ∃ C : ℝ, ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in l, ∀ i,
      G k i ≤ C * w k * (1 + d k i) ^ N * exp (-c * d k i ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∃ c > 0, ∀ᶠ k in l, ∀ i,
      F k i ≤ C * (1 + d k i) ^ N * exp (-c * d k i ^ 2) ∧
        G k i ≤ C * w k * (1 + d k i) ^ N * exp (-c * d k i ^ 2) := by
  obtain ⟨C, hC, N, c, hc, h⟩ := exists_forall_le_one_add_pow_mul_exp_neg_mul_sq (κ := Bool)
    (l := l) (F := fun b ↦ b.rec F G) (w := fun b k ↦ b.rec 1 (w k)) hd
    (by rintro (_ | _) k <;> simp [hw]) (by rintro (_ | _); exacts [by simpa using h₁, h₂])
  exact ⟨C, hC, N, c, hc, h.mono fun k hk i ↦ ⟨by simpa using hk false i, hk true i⟩⟩

/-- A Gaussian in the truncated difference `max (R - a) 0` is at most a constant times a Gaussian
in `R ≥ 0` with half the exponent: for `c ≥ 0`,
`exp (-c * max (R - a) 0 ^ 2) ≤ exp (c * a ^ 2) * exp (-(c / 2) * R ^ 2)`. -/
theorem exp_neg_mul_max_sub_sq_le {a c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) :
    exp (-c * max (R - a) 0 ^ 2) ≤ exp (c * a ^ 2) * exp (-(c / 2) * R ^ 2) := by
  rw [← exp_add, exp_le_exp]
  have : R ^ 2 / 2 - a ^ 2 ≤ max (R - a) 0 ^ 2 := by
    rcases le_total R a with h | h
    · rw [max_eq_right (by linarith)]
      nlinarith
    · rw [max_eq_left (by linarith)]
      nlinarith [sq_nonneg (R - 2 * a)]
  nlinarith

end Real

end
