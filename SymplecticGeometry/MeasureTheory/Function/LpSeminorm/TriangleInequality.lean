/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Consequences of the triangle inequality for the `Lᵖ` seminorm

For functions `f i` in `L²(μ)`, indexed by a finite set `s`, the integral of
`(∑ i ∈ s, ‖f i x‖) ^ 2` is at most `(∑ i ∈ s, ‖f i‖_{L²(μ)}) ^ 2`
(`MeasureTheory.integral_sum_norm_sq_le`): the integral is the square of the `L²` norm of the sum
of the norms, which the triangle inequality `MeasureTheory.eLpNorm_sum_le` bounds.

If `‖μ‖ ≤ m` almost everywhere and `‖g‖_p ≤ ‖f‖_p < ∞`, then `(1 - m) ‖f‖_p ≤ ‖f + μ g‖_p`
(`MeasureTheory.one_sub_mul_eLpNorm_le_eLpNorm_add_smul`). An inequality `‖a n‖_p ≤ ‖b n‖_p`
passes to limits in `Lᵖ` (`MeasureTheory.eLpNorm_le_eLpNorm_of_tendsto`).
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

/-- For functions `f i` in `L²(μ)`, `∫ (∑ i ∈ s, ‖f i x‖) ^ 2 dμ ≤ (∑ i ∈ s, ‖f i‖_{L²(μ)}) ^ 2`. -/
theorem integral_sum_norm_sq_le {ι : Type*} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    ∫ x, (∑ i ∈ s, ‖f i x‖) ^ 2 ∂μ ≤ (∑ i ∈ s, (eLpNorm (f i) 2 μ).toReal) ^ 2 := by
  set N : α → ℝ := fun x ↦ ∑ i ∈ s, ‖f i x‖
  have hN : MemLp N 2 μ := memLp_finsetSum s fun i hi ↦ (hf i hi).norm
  have hint : ∫ x, N x ^ 2 ∂μ = (eLpNorm N 2 μ).toReal ^ 2 := by
    simpa only [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), N] using
      integral_norm_sq_eq_toReal_eLpNorm_sq hN.aestronglyMeasurable
  have hne (i : ι) (hi : i ∈ s) : eLpNorm (f i) 2 μ ≠ ∞ := (hf i hi).eLpNorm_ne_top
  have hle : eLpNorm N 2 μ ≤ ∑ i ∈ s, eLpNorm (f i) 2 μ := by
    have hfun : N = ∑ i ∈ s, fun x ↦ ‖f i x‖ := by
      ext x
      simp [N]
    rw [hfun]
    exact (eLpNorm_sum_le one_le_two).trans_eq
      (Finset.sum_congr rfl fun i hi ↦ eLpNorm_norm (f i) (hf i hi).aestronglyMeasurable)
  rw [hint, ← ENNReal.toReal_sum hne]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hne) hle) 2


/-- **Absorbing a small multiple.** If `‖μ‖ ≤ m` almost everywhere and `‖g‖_p ≤ ‖f‖_p < ∞`,
then `(1 - m) ‖f‖_p ≤ ‖f + μ g‖_p`. -/
theorem one_sub_mul_eLpNorm_le_eLpNorm_add_smul {α E : Type*} [MeasurableSpace α]
    {ν : Measure α} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : α → E} {μ : α → ℂ} {m : ℝ≥0} (hg : AEStronglyMeasurable g ν)
    (hμ : AEStronglyMeasurable μ ν)
    (hμm : ∀ᵐ x ∂ν, ‖μ x‖ ≤ m) (hgf : eLpNorm g p ν ≤ eLpNorm f p ν)
    (hf_top : eLpNorm f p ν ≠ ⊤) :
    (1 - (m : ℝ≥0∞)) * eLpNorm f p ν ≤ eLpNorm (fun x ↦ f x + μ x • g x) p ν := by
  have h₁ : eLpNorm f p ν ≤
      eLpNorm (fun x ↦ f x + μ x • g x) p ν + eLpNorm (fun x ↦ μ x • g x) p ν := by
    have h := eLpNorm_sub_le (f := fun x ↦ f x + μ x • g x) (g := fun x ↦ μ x • g x) (μ := ν) hp
    rwa [show ((fun x ↦ f x + μ x • g x) - fun x ↦ μ x • g x) = f from
      funext fun x ↦ add_sub_cancel_right _ _] at h
  have h₂ : eLpNorm (fun x ↦ μ x • g x) p ν ≤ m * eLpNorm f p ν := by
    have hμg : AEStronglyMeasurable (fun x ↦ μ x • g x) ν := hμ.smul hg
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (g := g) (c := m) hμg ?_ p).trans ?_
    · filter_upwards [hμm] with x hx
      rw [nnNorm_smul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx) zero_le
    · rw [ENNReal.smul_def, smul_eq_mul]
      gcongr
  rw [ENNReal.sub_mul fun _ _ ↦ hf_top, one_mul, tsub_le_iff_right]
  exact h₁.trans (by gcongr)

/-- **Passing an `Lᵖ` norm inequality to the limit.** If `a' n → a` and `b' n → b` in `Lᵖ` and
`‖a' n‖_p ≤ ‖b' n‖_p` for every `n`, then `‖a‖_p ≤ ‖b‖_p`. -/
theorem eLpNorm_le_eLpNorm_of_tendsto {α E : Type*} [MeasurableSpace α] {ν : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : α → E} {a' b' : ℕ → α → E}
    (hle : ∀ n, eLpNorm (a' n) p ν ≤ eLpNorm (b' n) p ν)
    (hta : Tendsto (fun n ↦ eLpNorm (a' n - a) p ν) atTop (𝓝 0))
    (htb : Tendsto (fun n ↦ eLpNorm (b' n - b) p ν) atTop (𝓝 0)) :
    eLpNorm a p ν ≤ eLpNorm b p ν := by
  refine ge_of_tendsto' (by simpa using (hta.add htb).add tendsto_const_nhds) fun n ↦ ?_
  calc eLpNorm a p ν = eLpNorm ((a - a' n) + a' n) p ν := by rw [sub_add_cancel]
    _ ≤ eLpNorm (a - a' n) p ν + eLpNorm (a' n) p ν := eLpNorm_add_le hp
    _ ≤ eLpNorm (a' n - a) p ν + eLpNorm ((b' n - b) + b) p ν := by
        rw [eLpNorm_sub_comm, sub_add_cancel]
        gcongr
        exact hle n
    _ ≤ eLpNorm (a' n - a) p ν + eLpNorm (b' n - b) p ν + eLpNorm b p ν := by
        rw [add_assoc]
        gcongr
        exact eLpNorm_add_le hp

end MeasureTheory

end
