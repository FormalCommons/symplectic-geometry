/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Convex combinations of functions

* `deriv_mul_add_one_sub_mul_pos`: a combination `c * f + (1 - c) * g` with `c ∈ [0, 1]` of two
  real functions with positive derivative at `x` has positive derivative at `x`. The derivative
  is computed by Mathlib's `deriv_const_mul`; the differentiability of `f` and `g` at `x` follows
  from their derivatives being nonzero (`differentiableAt_of_deriv_ne_zero`).
  `deriv_mul_add_one_sub_mul_neg` is the same for negative derivatives, applied to `-f`, `-g`.
* `iteratedDeriv_mul_add_one_sub_mul_sub_iteratedDeriv`: the `n`-th derivative of a blend
  `ρ * f + (1 - ρ) * g` differs from that of `g` by `∑ i ≤ n, (n choose i) ρ⁽ⁱ⁾ (f - g)⁽ⁿ⁻ⁱ⁾`,
  since the blend is `g + ρ * (f - g)`; this is Mathlib's Leibniz rule `iteratedDeriv_mul`.
* `exists_forall_abs_iteratedDeriv_mul_add_one_sub_mul_sub_lt`: the resulting bounds for a blend
  `β * φ + (1 - β) * χ` by a `C²` cutoff `β` on a compact set: when `φ` is close to `χ` in value
  and first derivative, so is the blend, and its second derivative is close to that of `χ` up to
  the term `β (φ'' - χ'')`. The bounds on `β` and its derivatives over the compact set come from
  Tau Ceti's `ContDiff.exists_norm_iteratedDeriv_le_of_isCompact`.
-/

public section

/-- A combination `c * f + (1 - c) * g`, with `0 ≤ c ≤ 1`, of two real functions with positive
derivatives at `x` has positive derivative at `x`. -/
theorem deriv_mul_add_one_sub_mul_pos {f g : ℝ → ℝ} {x c : ℝ} (hf : 0 < deriv f x)
    (hg : 0 < deriv g x) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    0 < deriv (fun y ↦ c * f y + (1 - c) * g y) x := by
  have hfd := differentiableAt_of_deriv_ne_zero hf.ne'
  have hgd := differentiableAt_of_deriv_ne_zero hg.ne'
  rw [deriv_fun_add (hfd.const_mul c) (hgd.const_mul (1 - c)), deriv_const_mul _ hfd,
    deriv_const_mul _ hgd]
  rcases hc₀.eq_or_lt with rfl | hc₀
  · simpa using hg
  · nlinarith

/-- A combination `c * f + (1 - c) * g`, with `0 ≤ c ≤ 1`, of two real functions with negative
derivatives at `x` has negative derivative at `x`. -/
theorem deriv_mul_add_one_sub_mul_neg {f g : ℝ → ℝ} {x c : ℝ} (hf : deriv f x < 0)
    (hg : deriv g x < 0) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    deriv (fun y ↦ c * f y + (1 - c) * g y) x < 0 := by
  have h := deriv_mul_add_one_sub_mul_pos (f := fun y ↦ -f y) (g := fun y ↦ -g y)
    (by rw [deriv.fun_neg]; linarith) (by rw [deriv.fun_neg]; linarith) hc₀ hc₁
  have he : (fun y ↦ c * -f y + (1 - c) * -g y) = fun y ↦ -(c * f y + (1 - c) * g y) := by
    funext y
    ring
  rw [he, deriv.fun_neg] at h
  linarith

/-- The `n`-th derivative of the blend `ρ * f + (1 - ρ) * g` of `f` and `g` by `ρ`, minus that of
`g`, is `∑ i ≤ n, (n choose i) ρ⁽ⁱ⁾ (f⁽ⁿ⁻ⁱ⁾ - g⁽ⁿ⁻ⁱ⁾)`, for `ρ`, `f` and `g` that are `Cⁿ` at
`x`. -/
theorem iteratedDeriv_mul_add_one_sub_mul_sub_iteratedDeriv {𝕜 𝔸 : Type*}
    [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : ℕ} {ρ f g : 𝕜 → 𝔸}
    {x : 𝕜} (hρ : ContDiffAt 𝕜 n ρ x) (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun y ↦ ρ y * f y + (1 - ρ y) * g y) x - iteratedDeriv n g x =
      ∑ i ∈ Finset.range (n + 1), n.choose i * iteratedDeriv i ρ x *
        (iteratedDeriv (n - i) f x - iteratedDeriv (n - i) g x) := by
  have hblend : (fun y ↦ ρ y * f y + (1 - ρ y) * g y) = g + ρ * (f - g) := by
    ext y
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, sub_mul, one_mul, mul_sub]
    abel
  have hfg : ContDiffAt 𝕜 n (f - g) x := hf.sub hg
  have hm : ContDiffAt 𝕜 n (ρ * (f - g)) x := hρ.mul hfg
  rw [hblend, iteratedDeriv_add hg hm, add_sub_cancel_left, iteratedDeriv_mul hρ hfg]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : ((n - i : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast Nat.sub_le n i
  rw [iteratedDeriv_sub (hf.of_le hi) (hg.of_le hi)]

/-- **The derivatives of a blend by a cutoff**, uniformly on a compact set. Let `K ⊆ ℝ` be
compact, `β : ℝ → ℝ` be `C²` and `η > 0`. Then there is `τ > 0` such that for every `r ∈ K`
and all `φ, χ : ℝ → ℝ` that are `C²` at `r`, with values and first derivatives at `r` within `τ`
of each other, the blend `ψ = fun s ↦ β s * φ s + (1 - β s) * χ s` has `|ψ r - χ r| < η`,
`|ψ' r - χ' r| < η` and `|β r| τ + |ψ'' r - χ'' r - β r (φ'' r - χ'' r)| < η`.

So a one-sided bound on `β r (φ'' r - χ'' r)` by `|β r| τ` gives a one-sided bound on
`ψ'' r - χ'' r` by `η`. The number `τ` depends only on `η` and on a bound for `β`, `β'` and `β''`
on `K`. -/
theorem exists_forall_abs_iteratedDeriv_mul_add_one_sub_mul_sub_lt {K : Set ℝ}
    (hK : IsCompact K) {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {η : ℝ} (hη : 0 < η) :
    ∃ τ > 0, ∀ φ χ : ℝ → ℝ, ∀ r ∈ K, ContDiffAt ℝ 2 φ r → ContDiffAt ℝ 2 χ r →
      |φ r - χ r| < τ → |deriv φ r - deriv χ r| < τ →
        |β r * φ r + (1 - β r) * χ r - χ r| < η ∧
        |deriv (fun s ↦ β s * φ s + (1 - β s) * χ s) r - deriv χ r| < η ∧
        |β r| * τ + |iteratedDeriv 2 (fun s ↦ β s * φ s + (1 - β s) * χ s) r -
          iteratedDeriv 2 χ r - β r * (iteratedDeriv 2 φ r - iteratedDeriv 2 χ r)| < η := by
  -- A bound `B` for the first two derivatives of `β` over `K`.
  obtain ⟨B, hB⟩ := hβ.exists_norm_iteratedDeriv_le_of_isCompact hK
  have hd : 0 < 4 * (B : ℝ) + 1 := by positivity
  set τ := η / (4 * B + 1)
  have hτ : 0 < τ := div_pos hη hd
  have hBτ : 4 * B * τ < η := by
    rw [mul_div_assoc', div_lt_iff₀ hd]
    nlinarith
  refine ⟨τ, hτ, fun φ χ r hr hφ hχ h₀ h₁ ↦ ?_⟩
  have hBk : ∀ k ≤ 2, |iteratedDeriv k β r| ≤ B := fun k hk ↦ by
    rw [← Real.norm_eq_abs]
    exact hB k hk r hr
  have hβ0 := hBk 0 (by norm_num)
  have hβ1 := hBk 1 (by norm_num)
  have hβ2 := hBk 2 le_rfl
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hβ0 hβ1
  -- The derivatives of the blend minus those of `χ`, by the Leibniz rule.
  have e : ∀ k ≤ 2, iteratedDeriv k (fun s ↦ β s * φ s + (1 - β s) * χ s) r -
      iteratedDeriv k χ r = ∑ i ∈ Finset.range (k + 1), k.choose i *
        iteratedDeriv i β r * (iteratedDeriv (k - i) φ r - iteratedDeriv (k - i) χ r) :=
    fun k hk ↦ by
      have hk' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
      exact iteratedDeriv_mul_add_one_sub_mul_sub_iteratedDeriv (hβ.of_le hk').contDiffAt
        (hφ.of_le hk') (hχ.of_le hk')
  have e₀ := e 0 (by norm_num)
  have e₁ := e 1 (by norm_num)
  have e₂ := e 2 le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, iteratedDeriv_zero,
    iteratedDeriv_one, Nat.cast_one, Nat.cast_ofNat, zero_add, one_mul, Nat.sub_self,
    tsub_zero, Nat.add_one_sub_one] at e₀ e₁ e₂
  -- Each term is a derivative of `β`, at most `B`, times a difference, at most `τ`.
  have hab : ∀ a b : ℝ, |a| ≤ B → |b| < τ → |a * b| ≤ B * τ := fun a b ha hb ↦ by
    rw [abs_mul]
    gcongr
  have hβτ : |β r| * τ ≤ B * τ := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · rw [e₀]
    linarith [hab _ _ hβ0 h₀]
  · rw [e₁]
    linarith [abs_add_le (β r * (deriv φ r - deriv χ r)) (deriv β r * (φ r - χ r)),
      hab _ _ hβ0 h₁, hab _ _ hβ1 h₀]
  · rw [e₂]
    have := abs_add_le (2 * (deriv β r * (deriv φ r - deriv χ r)))
      (iteratedDeriv 2 β r * (φ r - χ r))
    rw [abs_mul 2, abs_two] at this
    have e₃ : β r * (iteratedDeriv 2 φ r - iteratedDeriv 2 χ r) +
        2 * deriv β r * (deriv φ r - deriv χ r) + iteratedDeriv 2 β r * (φ r - χ r) -
          β r * (iteratedDeriv 2 φ r - iteratedDeriv 2 χ r) =
        2 * (deriv β r * (deriv φ r - deriv χ r)) + iteratedDeriv 2 β r * (φ r - χ r) := by
      ring
    rw [e₃]
    linarith [hab _ _ hβ1 h₁, hab _ _ hβ2 h₀]

end
