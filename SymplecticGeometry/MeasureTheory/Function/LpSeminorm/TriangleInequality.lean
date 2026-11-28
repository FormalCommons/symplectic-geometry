/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Consequences of the triangle inequality for the `Lᵖ` seminorm

For functions `f i` in `L²(μ)`, indexed by a finite set `s`, the integral of
`(∑ i ∈ s, ‖f i x‖) ^ 2` is at most `(∑ i ∈ s, ‖f i‖_{L²(μ)}) ^ 2`
(`MeasureTheory.integral_sum_norm_sq_le`): the integral is the square of the `L²` norm of the sum
of the norms, which the triangle inequality `MeasureTheory.eLpNorm_sum_le` bounds.

If `‖c‖ ≤ m` almost everywhere and `‖g‖_p ≤ ‖f‖_p < ∞`, then `(1 - m) ‖f‖_p ≤ ‖f + c g‖_p`
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

/-- **Absorbing a small multiple.** If `‖c‖ ≤ m` almost everywhere and `‖g‖_p ≤ ‖f‖_p < ∞`,
then `(1 - m) ‖f‖_p ≤ ‖f + c g‖_p`. -/
theorem one_sub_mul_eLpNorm_le_eLpNorm_add_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : α → E} {c : α → 𝕜} {m : ℝ≥0}
    (hcm : ∀ᵐ x ∂μ, ‖c x‖ ≤ m) (hgf : eLpNorm g p μ ≤ eLpNorm f p μ)
    (hf_top : eLpNorm f p μ ≠ ⊤) :
    (1 - (m : ℝ≥0∞)) * eLpNorm f p μ ≤ eLpNorm (fun x ↦ f x + c x • g x) p μ := by
  by_cases hfcg : AEStronglyMeasurable (fun x ↦ f x + c x • g x) μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfcg]
    exact le_top
  have hcg : AEStronglyMeasurable (fun x ↦ c x • g x) μ := by
    exact (hfcg.sub (aestronglyMeasurable_of_eLpNorm_ne_top hf_top)).congr
      (.of_forall fun x ↦ add_sub_cancel_left (f x) _)
  have h₁ : eLpNorm f p μ ≤
      eLpNorm (fun x ↦ f x + c x • g x) p μ + eLpNorm (fun x ↦ c x • g x) p μ := by
    have h := eLpNorm_sub_le (f := fun x ↦ f x + c x • g x) (g := fun x ↦ c x • g x) (μ := μ) hp
    rwa [show ((fun x ↦ f x + c x • g x) - fun x ↦ c x • g x) = f from
      funext fun x ↦ add_sub_cancel_right _ _] at h
  have h₂ : eLpNorm (fun x ↦ c x • g x) p μ ≤ m * eLpNorm f p μ :=
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (g := g) hcg (by
      filter_upwards [hcm] with x hx
      rw [nnNorm_smul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hx) (by positivity)) p).trans
      (by rw [ENNReal.smul_def, smul_eq_mul]; gcongr)
  rw [ENNReal.sub_mul fun _ _ ↦ hf_top, one_mul, tsub_le_iff_right]
  exact h₁.trans (by gcongr)

/-- **Passing an `Lᵖ` norm inequality to the limit.** If `a' n → a` and `b' n → b` in `Lᵖ`
along a nontrivial filter `l`, and eventually `‖a' n‖_p ≤ ‖b' n‖_p`, then `‖a‖_p ≤ ‖b‖_p`. -/
theorem eLpNorm_le_eLpNorm_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {p : ℝ≥0∞}
    (hp : 1 ≤ p) {a b : α → E} {a' b' : ι → α → E}
    (hle : ∀ᶠ n in l, eLpNorm (a' n) p μ ≤ eLpNorm (b' n) p μ)
    (hta : Tendsto (fun n ↦ eLpNorm (a' n - a) p μ) l (𝓝 0))
    (htb : Tendsto (fun n ↦ eLpNorm (b' n - b) p μ) l (𝓝 0)) :
    eLpNorm a p μ ≤ eLpNorm b p μ := by
  refine ge_of_tendsto (by simpa using (hta.add htb).add tendsto_const_nhds) ?_
  filter_upwards [hle] with n hn
  calc eLpNorm a p μ = eLpNorm ((a - a' n) + a' n) p μ := by rw [sub_add_cancel]
    _ ≤ eLpNorm (a - a' n) p μ + eLpNorm (a' n) p μ := eLpNorm_add_le hp
    _ ≤ eLpNorm (a' n - a) p μ + eLpNorm ((b' n - b) + b) p μ := by
        rw [eLpNorm_sub_comm, sub_add_cancel]
        gcongr
    _ ≤ eLpNorm (a' n - a) p μ + eLpNorm (b' n - b) p μ + eLpNorm b p μ := by
        rw [add_assoc]
        gcongr
        exact eLpNorm_add_le hp

end MeasureTheory

end
