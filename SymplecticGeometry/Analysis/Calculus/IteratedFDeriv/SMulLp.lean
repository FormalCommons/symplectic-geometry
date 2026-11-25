/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# The Leibniz rule in `Lᵖ` on an open set, for a coefficient smooth near its closure

Let `s` be an open set contained in a compact set `K`, and `a` a scalar function of class `C^k`
on an open set containing `K`. Multiplication by `a` is then bounded on the functions `f` of
class `C^k` on `s`, for the norms `∑_{l ≤ k} ‖Dˡf‖_{Lᵖ(s)}`: the derivatives of order `j ≤ k` of
`a • f` satisfy `‖Dʲ(a • f)‖_{Lᵖ(s)} ≤ C ∑_{l ≤ k} ‖Dˡf‖_{Lᵖ(s)}` with `C` independent of `f`
(`exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen`).

Unlike Tau Ceti's `ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear`, nothing is assumed
of `f` off `s`. The proof bounds the derivatives of `a` on `K` and applies Mathlib's pointwise
`norm_iteratedFDerivWithin_smul_le` at the points of `s`.

## Main results

* `exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen`: the Leibniz rule above.
* `ContDiffOn.aestronglyMeasurable_iteratedFDeriv_restrict`: the derivatives of a `C^n` function
  on an open set `s` are a.e. strongly measurable for a measure restricted to `s`.
* `eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn`: functions equal on an open set `s` have
  derivatives with equal `Lᵖ` norms over `s`.
* `ContinuousLinearMap.eLpNorm_iteratedFDeriv_comp_left_restrict_le`: on an open set, composing on
  the left with `L` multiplies these norms by at most `‖L‖`; the `Lᵖ` form of Mathlib's
  `ContinuousLinearMap.norm_iteratedFDeriv_comp_left`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

variable {E 𝕜' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [SecondCountableTopology E] [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜' F] [IsScalarTower ℝ 𝕜' F]

/-- On an open set `s`, the derivatives of order at most `n` of a function of class `C^n` on `s`
are almost everywhere strongly measurable for `μ` restricted to `s`. -/
theorem ContDiffOn.aestronglyMeasurable_iteratedFDeriv_restrict {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : WithTop ℕ∞} {f : E → G} {s : Set E} (hf : ContDiffOn ℝ n f s)
    (hs : IsOpen s) {j : ℕ} (hj : j ≤ n) (μ : Measure E) :
    AEStronglyMeasurable (iteratedFDeriv ℝ j f) (μ.restrict s) := by
  refine ContinuousOn.aestronglyMeasurable ?_ hs.measurableSet
  exact (hf.continuousOn_iteratedFDerivWithin hj hs.uniqueDiffOn).congr fun x hx ↦
    (iteratedFDerivWithin_of_isOpen j hs hx).symm

/-- **The Leibniz rule in `Lᵖ` on an open set.** Let `s` be open, contained in a compact set `K`,
and `a` of class `C^k` on an open set `t ⊇ K`. For `1 ≤ p` there is a constant `C` such that every
`f` of class `C^k` on `s` satisfies, for every `j ≤ k`,
`‖Dʲ(a • f)‖_{Lᵖ(μ|s)} ≤ C ∑_{l ≤ k} ‖Dˡf‖_{Lᵖ(μ|s)}`. -/
theorem exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen (μ : Measure E) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {s t K : Set E} (hs : IsOpen s) (ht : IsOpen t) (hK : IsCompact K)
    (hsK : s ⊆ K) (hKt : K ⊆ t) {a : E → 𝕜'} {k : ℕ} (ha : ContDiffOn ℝ k a t) :
    ∃ C : ℝ≥0, ∀ f : E → F, ContDiffOn ℝ k f s → ∀ j ≤ k,
      eLpNorm (iteratedFDeriv ℝ j (fun x ↦ a x • f x)) p (μ.restrict s) ≤
        C * ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l f) p (μ.restrict s) := by
  -- A bound `M` on `K` of the derivatives of `a` of order at most `k`.
  have hcont : ContinuousOn
      (fun x ↦ ∑ i ∈ Finset.range (k + 1), ‖iteratedFDerivWithin ℝ i a t x‖) t :=
    continuousOn_finsetSum _ fun i hi ↦ (ha.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast Finset.mem_range_succ_iff.1 hi) ht.uniqueDiffOn).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKt)
  have hMi (i : ℕ) (hi : i ≤ k) (x : E) (hx : x ∈ s) : ‖iteratedFDeriv ℝ i a x‖ ≤ M := by
    have hxt : x ∈ t := hKt (hsK hx)
    rw [← iteratedFDerivWithin_of_isOpen i ht hxt]
    refine le_trans ?_ ((Real.le_norm_self _).trans (hM x (hsK hx)))
    exact Finset.single_le_sum (f := fun i ↦ ‖iteratedFDerivWithin ℝ i a t x‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_range_succ_iff.2 hi)
  set C : ℝ := (k + 1) * (2 ^ k * max M 0)
  refine ⟨C.toNNReal, fun f hf j hj ↦ ?_⟩
  set S : E → ℝ := fun x ↦ ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l f x‖
  -- The pointwise bound `‖Dʲ(a • f)(x)‖ ≤ C S(x)` on `s`.
  have hpt : ∀ᵐ x ∂μ.restrict s, ‖iteratedFDeriv ℝ j (fun x ↦ a x • f x) x‖ ≤ ‖C * S x‖ := by
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    have : 0 ≤ S x := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg (by positivity), ← iteratedFDerivWithin_of_isOpen j hs hx]
    refine (norm_iteratedFDerivWithin_smul_le (ha.mono (hsK.trans hKt)) hf hs.uniqueDiffOn hx
      (by exact_mod_cast hj)).trans ?_
    calc _ ≤ ∑ _i ∈ Finset.range (j + 1), 2 ^ k * max M 0 * S x := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hij : i ≤ j := Finset.mem_range_succ_iff.1 hi
          rw [iteratedFDerivWithin_of_isOpen i hs hx, iteratedFDerivWithin_of_isOpen _ hs hx]
          gcongr
          · exact_mod_cast (Nat.choose_le_two_pow j i).trans (Nat.pow_le_pow_right two_pos hj)
          · exact (hMi i (hij.trans hj) x hx).trans (le_max_left _ _)
          · exact Finset.single_le_sum (f := fun l ↦ ‖iteratedFDeriv ℝ l f x‖)
              (fun _ _ ↦ norm_nonneg _) (Finset.mem_range_succ_iff.2 (by omega))
      _ ≤ C * S x := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
          simp only [C]
          gcongr
          exact_mod_cast (by omega : j + 1 ≤ k + 1)
  have hmeas {g : E → F} (hg : ContDiffOn ℝ k g s) {l : ℕ} (hl : l ≤ k) :
      AEStronglyMeasurable (iteratedFDeriv ℝ l g) (μ.restrict s) :=
    hg.aestronglyMeasurable_iteratedFDeriv_restrict hs (by exact_mod_cast hl) μ
  have hC : ‖C‖ₑ = C.toNNReal := by
    rw [Real.eNorm_eq_ofReal (by positivity), ENNReal.ofReal]
  calc _ ≤ eLpNorm (C • S) p (μ.restrict s) :=
        eLpNorm_mono_ae (hmeas ((ha.mono (hsK.trans hKt)).smul hf) hj) hpt
    _ = C.toNNReal * eLpNorm S p (μ.restrict s) := by rw [eLpNorm_const_smul, hC]
    _ ≤ C.toNNReal * ∑ l ∈ Finset.range (k + 1),
          eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ l f x‖) p (μ.restrict s) := by
        gcongr
        have : S = ∑ l ∈ Finset.range (k + 1), fun x ↦ ‖iteratedFDeriv ℝ l f x‖ := by
          ext x; simp [S]
        rw [this]
        exact eLpNorm_sum_le hp
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun l hl ↦
          eLpNorm_norm _ (hmeas hf (Finset.mem_range_succ_iff.1 hl))

omit [SecondCountableTopology E] in
/-- On an open set `s`, two functions that agree on `s` have derivatives with the same `Lᵖ` norms
for `μ` restricted to `s`. -/
theorem eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (μ : Measure E) (p : ℝ≥0∞) {s : Set E} (hs : IsOpen s) {f g : E → G}
    (h : EqOn f g s) (j : ℕ) :
    eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict s) =
      eLpNorm (iteratedFDeriv ℝ j g) p (μ.restrict s) :=
  eLpNorm_congr_ae ((ae_restrict_mem hs.measurableSet).mono fun _ hx ↦
    ((h.eventuallyEq_of_mem (hs.mem_nhds hx)).iteratedFDeriv ℝ j).self_of_nhds)

/-- On an open set `s`, composing on the left with a continuous linear map `L` multiplies the
`Lᵖ(μ|s)` norms of the derivatives of order at most `n` of a `C^n` function on `s` by at most
`‖L‖`. -/
theorem ContinuousLinearMap.eLpNorm_iteratedFDeriv_comp_left_restrict_le {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) {n : WithTop ℕ∞} {f : E → G} {s : Set E} (hf : ContDiffOn ℝ n f s)
    (hs : IsOpen s) {j : ℕ} (hj : j ≤ n) (μ : Measure E) (p : ℝ≥0∞) :
    eLpNorm (iteratedFDeriv ℝ j (L ∘ f)) p (μ.restrict s) ≤
      ‖L‖₊ • eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict s) := by
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    ((L.contDiff.comp_contDiffOn hf).aestronglyMeasurable_iteratedFDeriv_restrict hs hj μ) ?_ p
  filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
  have h := L.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hs.mem_nhds hx)) hj
  simp only [eNorm_eq_nnNorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
    NNReal.coe_mul, coe_nnNorm]
  exact h
