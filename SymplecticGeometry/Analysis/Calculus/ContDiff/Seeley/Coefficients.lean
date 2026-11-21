/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Normed.Group.Tannery
public import SymplecticGeometry.LinearAlgebra.Lagrange

/-!
# Seeley's coefficients

Seeley extends a smooth function on a half-line across the boundary point by a series
`∑ₖ aₖ f (-2 ^ k t)`. For the extension to be smooth, the real coefficients `aₖ` must satisfy
the moment identities `∑ₖ aₖ (-2 ^ k) ^ n = 1` for every `n : ℕ`, with
`∑ₖ |aₖ| 2 ^ (k n) < ∞` for every `n`. This file defines Seeley's choice
`aₖ = ∏_{j ≠ k} (1 + 2 ^ j) / (2 ^ j - 2 ^ k)` and proves both properties.

For `N > n`, the numbers `∏_{j < N, j ≠ k} (1 + 2 ^ j) / (2 ^ j - 2 ^ k)` are the values at `1`
of the Lagrange basis polynomials of the nodes `-2 ^ k`, `k < N` (`Lagrange.eval_basis`), so
`Lagrange.sum_eval_basis_mul_pow`, which reproduces `X ^ n` from these values, gives the
moment identity for these finite products. They tend to `aₖ` as `N → ∞`, and are bounded
uniformly in `N` by `exp 8 * ∏_{i < k} 2 / 2 ^ i`, which decays faster than any exponential.
Dominated convergence (`tendsto_tsum_of_dominated_convergence`) then gives the identity for `aₖ`.

## Main definitions

* `SymplecticGeometry.seeleyCoeff`: Seeley's coefficients `aₖ`.

## Main results

* `SymplecticGeometry.hasProd_seeleyCoeff`: the product defining `aₖ` converges to `aₖ`.
* `SymplecticGeometry.summable_seeleyCoeff_mul_pow`: `∑ₖ |aₖ| 2 ^ (k n)` converges.
* `SymplecticGeometry.tsum_seeleyCoeff_mul_neg_two_pow`: `∑ₖ aₖ (-2 ^ k) ^ n = 1`, with
  `SymplecticGeometry.hasSum_seeleyCoeff_mul_neg_two_pow` its form as a sum.
* `SymplecticGeometry.hasSum_seeleyCoeff_smul`: `∑ₖ aₖ • x = x` in a module.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Filter Finset
open scoped Topology

namespace SymplecticGeometry

/-- The `j`-th factor of the product defining `seeleyCoeff k`, with the factor `j = k`
replaced by `1`. -/
private noncomputable def seeleyFactor (k j : ℕ) : ℝ :=
  if j = k then 1 else (1 + 2 ^ j) / (2 ^ j - 2 ^ k)

/-- Seeley's coefficients `a k = ∏_{j ≠ k} (1 + 2 ^ j) / (2 ^ j - 2 ^ k)`. -/
noncomputable def seeleyCoeff (k : ℕ) : ℝ :=
  ∏' j : ({k}ᶜ : Set ℕ), (1 + 2 ^ (j : ℕ)) / (2 ^ (j : ℕ) - 2 ^ k)

/-- The defining infinite product of `seeleyCoeff k`. -/
theorem seeleyCoeff_def (k : ℕ) :
    seeleyCoeff k = ∏' j : ({k}ᶜ : Set ℕ), (1 + 2 ^ (j : ℕ)) / (2 ^ (j : ℕ) - 2 ^ k) := (rfl)

private theorem mulIndicator_eq_seeleyFactor (k : ℕ) :
    Set.mulIndicator ({k}ᶜ : Set ℕ) (fun j : ℕ ↦ (1 + 2 ^ j : ℝ) / (2 ^ j - 2 ^ k)) =
      seeleyFactor k := by
  ext j
  by_cases h : j = k <;> simp [seeleyFactor, h, Set.mulIndicator]

private theorem abs_seeleyFactor_of_lt {k j : ℕ} (h : j < k) :
    |seeleyFactor k j| ≤ 2 / 2 ^ (k - 1 - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hm : j + m + 1 - 1 - j = m := by omega
  rw [seeleyFactor, ite_eq_right (by omega), hm]
  rw [pow_succ, pow_add]
  have hx : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hy : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hd : 2 ^ j - 2 ^ j * 2 ^ m * 2 < (0 : ℝ) := by nlinarith
  rw [abs_div, abs_of_pos (by positivity), abs_of_neg hd, div_le_div_iff₀ (by linarith)
    (by positivity)]
  nlinarith

private theorem seeleyFactor_add_bounds (k i : ℕ) :
    1 ≤ seeleyFactor k (k + i) ∧ seeleyFactor k (k + i) ≤ 1 + 4 * (1 / 2) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [seeleyFactor]
  rw [seeleyFactor, ite_eq_right (by omega)]
  rw [pow_add]
  have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hy : (2 : ℝ) ≤ 2 ^ i := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
  have hd : 0 < (2 : ℝ) ^ k * 2 ^ i - 2 ^ k := by nlinarith
  rw [one_div_pow, mul_one_div]
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]
    have h4 : 4 / (2 : ℝ) ^ i * 2 ^ i = 4 := div_mul_cancel₀ _ (by positivity)
    have h4' : 4 / (2 : ℝ) ^ i ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith

private theorem abs_prod_seeleyFactor_le {k N : ℕ} (hkN : k ≤ N) :
    |∏ j ∈ range N, seeleyFactor k j| ≤ Real.exp 8 * ∏ i ∈ range k, (2 : ℝ) / 2 ^ i := by
  rw [← prod_range_mul_prod_Ico _ hkN, abs_mul, abs_prod, abs_prod, mul_comm (Real.exp 8)]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · rw [← prod_range_reflect (fun i ↦ (2 : ℝ) / 2 ^ i) k]
    exact prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
      fun j hj ↦ abs_seeleyFactor_of_lt (mem_range.mp hj)
  · rw [prod_Ico_eq_prod_range]
    calc ∏ i ∈ range (N - k), |seeleyFactor k (k + i)|
        ≤ ∏ i ∈ range (N - k), (1 + 4 * (1 / 2 : ℝ) ^ i) := by
          refine prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ ?_
          obtain ⟨h1, h2⟩ := seeleyFactor_add_bounds k i
          rwa [abs_of_pos (by linarith)]
      _ ≤ Real.exp (∑ i ∈ range (N - k), 4 * (1 / 2 : ℝ) ^ i) :=
          Real.prod_one_add_le_exp_sum _ fun _ ↦ by positivity
      _ ≤ Real.exp 8 := by
          rw [← mul_sum]
          gcongr
          linarith [sum_geometric_two_le (N - k)]

private theorem multipliable_seeleyFactor (k : ℕ) : Multipliable (seeleyFactor k) := by
  have h : Summable fun j ↦ seeleyFactor k j - 1 := by
    refine (summable_nat_add_iff k).mp ?_
    refine Summable.of_nonneg_of_le (fun i ↦ ?_) (fun i ↦ ?_)
      ((summable_geometric_two).mul_left 4)
    · rw [add_comm]; linarith [(seeleyFactor_add_bounds k i).1]
    · rw [add_comm]; linarith [(seeleyFactor_add_bounds k i).2]
  simpa using Real.multipliable_one_add_of_summable h

/-- Seeley's product converges: `seeleyCoeff k` is the value of the infinite product
`∏_{j ≠ k} (1 + 2 ^ j) / (2 ^ j - 2 ^ k)`. -/
theorem hasProd_seeleyCoeff (k : ℕ) :
    HasProd (fun j : ({k}ᶜ : Set ℕ) ↦ (1 + 2 ^ (j : ℕ)) / (2 ^ (j : ℕ) - 2 ^ k))
      (seeleyCoeff k) := by
  rw [seeleyCoeff_def]
  refine Multipliable.hasProd <| (multipliable_subtype_iff_mulIndicator (s := {k}ᶜ)
    (f := fun j : ℕ ↦ (1 + 2 ^ j : ℝ) / (2 ^ j - 2 ^ k))).mpr ?_
  rw [mulIndicator_eq_seeleyFactor]
  exact multipliable_seeleyFactor k

private theorem tendsto_prod_seeleyFactor (k : ℕ) :
    Tendsto (fun N ↦ ∏ j ∈ range N, seeleyFactor k j) atTop (𝓝 (seeleyCoeff k)) := by
  have h := (hasProd_subtype_iff_mulIndicator (s := {k}ᶜ)
    (f := fun j : ℕ ↦ (1 + 2 ^ j : ℝ) / (2 ^ j - 2 ^ k))).mp (hasProd_seeleyCoeff k)
  rw [mulIndicator_eq_seeleyFactor] at h
  exact h.tendsto_prod_nat

/-- The moment identities for the partial products of length `N > n`: they are the values at `1`
of the Lagrange basis of the nodes `-2 ^ k`, `k < N`. -/
private theorem sum_prod_seeleyFactor_mul_pow {n N : ℕ} (hn : n < N) :
    ∑ k ∈ range N, (∏ j ∈ range N, seeleyFactor k j) * (-2 ^ k) ^ n = 1 := by
  set v : ℕ → ℝ := fun k ↦ -2 ^ k
  have hinj : Set.InjOn v (range N) := fun a _ b _ hab ↦
    pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) (neg_inj.mp hab)
  calc ∑ k ∈ range N, (∏ j ∈ range N, seeleyFactor k j) * v k ^ n
      = ∑ k ∈ range N, (Lagrange.basis (range N) v k).eval 1 * v k ^ n := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [Lagrange.eval_basis,
          ← prod_erase (range N) (f := seeleyFactor k) (a := k) (by simp [seeleyFactor])]
        congr 1
        refine prod_congr rfl fun j hj ↦ ?_
        rw [seeleyFactor, ite_eq_right (ne_of_mem_erase hj)]
        congr 1 <;> simp only [v] <;> ring
    _ = 1 ^ n := Lagrange.sum_eval_basis_mul_pow hinj (by rwa [card_range]) 1
    _ = 1 := one_pow n

/-- For `k ≤ N`, the partial product of length `N` for `aₖ`, times `2 ^ (k n)`, is bounded,
uniformly in `N`, by the `k`-th term of a summable sequence. -/
private theorem exists_summable_bound (n : ℕ) : ∃ b : ℕ → ℝ, Summable b ∧
    ∀ {k N : ℕ}, k ≤ N → |∏ j ∈ range N, seeleyFactor k j| * 2 ^ (k * n) ≤ b k := by
  refine ⟨fun k ↦ Real.exp 8 * ((∏ i ∈ range k, (2 : ℝ) / 2 ^ i) * 2 ^ (k * n)), ?_,
    fun hkN ↦ ?_⟩
  · refine Summable.mul_left _ <| summable_of_ratio_norm_eventually_le (r := 1 / 2)
      (by norm_num) ?_
    filter_upwards [eventually_ge_atTop (n + 2)] with k hk
    have hb : 0 ≤ (∏ i ∈ range k, (2 : ℝ) / 2 ^ i) * 2 ^ (k * n) := by positivity
    have hk' : (2 : ℝ) ^ n * 2 ^ 2 ≤ 2 ^ k := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hk
    rw [Real.norm_of_nonneg hb, Real.norm_of_nonneg (by positivity), prod_range_succ, add_mul,
      one_mul, pow_add, mul_mul_mul_comm, mul_comm (1 / 2 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ hb
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  · dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_prod_seeleyFactor_le hkN) (by positivity)

/-- For every `n`, the series `∑ₖ |aₖ| 2 ^ (k n)` of Seeley's coefficients converges. -/
theorem summable_seeleyCoeff_mul_pow (n : ℕ) :
    Summable fun k ↦ |seeleyCoeff k| * 2 ^ (k * n) := by
  obtain ⟨b, hb, hbound⟩ := exists_summable_bound n
  refine hb.of_nonneg_of_le (fun k ↦ by positivity) fun k ↦ ?_
  exact le_of_tendsto ((tendsto_prod_seeleyFactor k).abs.mul_const _)
    (eventually_atTop.2 ⟨k, fun _ hN ↦ hbound hN⟩)

/-- The moment identities of Seeley's coefficients: `∑ₖ aₖ (-2 ^ k) ^ n = 1` for every `n`. -/
theorem tsum_seeleyCoeff_mul_neg_two_pow (n : ℕ) :
    ∑' k, seeleyCoeff k * (-2 ^ k) ^ n = 1 := by
  obtain ⟨b, hb, hbound⟩ := exists_summable_bound n
  set F : ℕ → ℕ → ℝ := fun N k ↦
    if k < N then (∏ j ∈ range N, seeleyFactor k j) * (-2 ^ k) ^ n else 0
  have hF (N : ℕ) :
      ∑' k, F N k = ∑ k ∈ range N, (∏ j ∈ range N, seeleyFactor k j) * (-2 ^ k) ^ n := by
    rw [tsum_eq_sum (s := range N) fun k hk ↦ ite_eq_right (by simpa using hk)]
    exact sum_congr rfl fun k hk ↦ ite_eq_left (mem_range.mp hk)
  have hlim : Tendsto (fun N ↦ ∑' k, F N k) atTop (𝓝 (∑' k, seeleyCoeff k * (-2 ^ k) ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence hb (fun k ↦ ?_)
      (Eventually.of_forall fun N k ↦ ?_)
    · refine ((tendsto_prod_seeleyFactor k).mul_const _).congr' ?_
      filter_upwards [eventually_gt_atTop k] with N hN
      exact (ite_eq_left hN).symm
    · simp only [F]
      split_ifs with hk
      · rw [norm_mul, norm_pow, norm_neg, norm_pow, Real.norm_two, ← pow_mul, Real.norm_eq_abs]
        exact hbound hk.le
      · rw [norm_zero]
        exact (mul_nonneg (abs_nonneg _) (by positivity)).trans (hbound le_rfl)
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop n] with N hN
  rw [hF, sum_prod_seeleyFactor_mul_pow hN]

/-- The series `∑ₖ aₖ (-2 ^ k) ^ n` of the moment identities converges absolutely. -/
theorem summable_seeleyCoeff_mul_neg_two_pow (n : ℕ) :
    Summable fun k ↦ seeleyCoeff k * (-2 ^ k) ^ n :=
  (summable_seeleyCoeff_mul_pow n).of_norm_bounded fun k ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_pow, abs_two, pow_mul]

/-- The moment identities of Seeley's coefficients, as sums: `∑ₖ aₖ (-2 ^ k) ^ n = 1`. -/
theorem hasSum_seeleyCoeff_mul_neg_two_pow (n : ℕ) :
    HasSum (fun k ↦ seeleyCoeff k * (-2 ^ k) ^ n) 1 :=
  (summable_seeleyCoeff_mul_neg_two_pow n).hasSum_iff.mpr (tsum_seeleyCoeff_mul_neg_two_pow n)

/-- The moment identity of order `0`, in a module: `∑ₖ aₖ • x = x`. -/
theorem hasSum_seeleyCoeff_smul {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [Module ℝ M]
    [ContinuousSMul ℝ M] (x : M) : HasSum (fun k ↦ seeleyCoeff k • x) x := by
  simpa using (hasSum_seeleyCoeff_mul_neg_two_pow 0).smul_const x

end SymplecticGeometry

end
