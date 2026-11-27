/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import SymplecticGeometry.Analysis.Calculus.ContDiff.FTaylorSeries
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.Integrable
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear

/-!
# The Leibniz rule in `Lᵖ` on an open set, for a coefficient smooth near its closure

Let `s` be an open set contained in a compact set `K`, and `a` a scalar function of class `C^k`
on an open set containing `K`. Multiplication by `a` is then bounded on the functions `f` of
class `C^k` on `s`, for the norms `∑_{l ≤ k} ‖Dˡf‖_{Lᵖ(s)}`: the derivatives of order `j ≤ k` of
`a • f` satisfy `‖Dʲ(a • f)‖_{Lᵖ(s)} ≤ C ∑_{l ≤ k} ‖Dˡf‖_{Lᵖ(s)}` with `C` independent of `f`
(`exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen`).

Unlike Tau Ceti's `ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear`, nothing is assumed
of `f` off `s`. Tau Ceti's `TauCeti.eLpNormWkp_bilin_le` proves a bound of the same shape, with a
constant of the same form, for the `W^{k,p}` norms on planar open sets and Lebesgue measure; here
`E` is any normed space and `μ` any measure, and the bound on the derivatives of `a` comes from the
compactness of `K` instead of being a hypothesis. The proof follows that of
`TauCeti.eLpNormWkp_bilin_le`: it bounds the derivatives of `a` on `K` by Tau Ceti's
`ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen`, applies Tau Ceti's pointwise Leibniz
rule `TauCeti.exists_norm_iteratedFDeriv_bilinear_le` to the bilinear map
`ContinuousLinearMap.lsmul` at the points of `s`, and passes to `Lᵖ` norms by Mathlib's
`MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`.

## Main results

* `exists_eLpNorm_iteratedFDeriv_smul_le_of_isOpen`: the Leibniz rule above.
* `eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn`: functions equal on an open set `s` have
  derivatives with equal `Lᵖ` norms over `s`.
* `eLpNorm_iteratedFDeriv_add_restrict_le`: on an open set `s`, the triangle inequality for the
  `Lᵖ(μ|s)` norms of the derivatives of a sum of two functions of class `C^n` on `s`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace SymplecticGeometry

variable {E 𝕜' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [SecondCountableTopology E] [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜' F] [IsScalarTower ℝ 𝕜' F]

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
  -- A bound `M ≥ 0` on `K` of the derivatives of `a` of order at most `k`.
  obtain ⟨M, -, hM⟩ := ha.exists_nonneg_bound_iteratedFDeriv_of_isOpen ht hK hKt
  -- Tau Ceti's pointwise Leibniz rule for the bilinear map `lsmul`, with one constant `B` for
  -- every order at most `k`.
  obtain ⟨B, -, hB⟩ := TauCeti.exists_norm_iteratedFDeriv_bilinear_le E
    (ContinuousLinearMap.lsmul ℝ 𝕜' : 𝕜' →L[ℝ] F →L[ℝ] F) k
  refine ⟨(B * M).toNNReal, fun f hf j hj ↦ ?_⟩
  set S : E → ℝ := fun x ↦ jetNormAt ℝ k f x
  have hpt : ∀ᵐ x ∂μ.restrict s,
      ‖iteratedFDeriv ℝ j (fun x ↦ a x • f x) x‖ ≤ B * M * ‖S x‖ := by
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    have h := hB a f s x hs hx (ha.mono (hsK.trans hKt)) hf M (S x)
      (fun i hi ↦ hM i hi x (hsK hx))
      (fun i hi ↦ norm_iteratedFDeriv_le_jetNormAt hi f x) j hj
    simp only [ContinuousLinearMap.lsmul_apply] at h
    rw [Real.norm_of_nonneg (jetNormAt_nonneg k f x), mul_assoc]
    exact h
  calc _ ≤ ENNReal.ofReal (B * M) * eLpNorm S p (μ.restrict s) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (((ha.mono (hsK.trans hKt)).smul hf).aestronglyMeasurable_iteratedFDeriv hs hj) hpt p
    _ ≤ ENNReal.ofReal (B * M) * ∑ l ∈ Finset.range (k + 1),
          eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ l f x‖) p (μ.restrict s) := by
        gcongr
        have : S = ∑ l ∈ Finset.range (k + 1), fun x ↦ ‖iteratedFDeriv ℝ l f x‖ := by
          ext x; simp [S, jetNormAt_def]
        rw [this]
        exact eLpNorm_sum_le hp
    _ = _ := by
        rw [ENNReal.ofReal]
        congr 1
        exact Finset.sum_congr rfl fun l hl ↦
          eLpNorm_norm _
            (hf.aestronglyMeasurable_iteratedFDeriv hs (Finset.mem_range_succ_iff.1 hl))

omit [SecondCountableTopology E] in
/-- On an open set `s`, two functions that agree on `s` have derivatives with the same `Lᵖ` norms
for `μ` restricted to `s`. -/
theorem eLpNorm_iteratedFDeriv_restrict_congr_of_eqOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (μ : Measure E) (p : ℝ≥0∞) {s : Set E} (hs : IsOpen s) {f g : E → G}
    (h : EqOn f g s) (j : ℕ) :
    eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict s) =
      eLpNorm (iteratedFDeriv ℝ j g) p (μ.restrict s) :=
  eLpNorm_congr_ae ((ae_restrict_mem hs.measurableSet).mono fun _ hx ↦
    h.iteratedFDeriv_of_isOpen hs j hx)

omit [SecondCountableTopology E] in
/-- On an open set `s` and for `1 ≤ p`, the `Lᵖ(μ|s)` norm of a derivative of order `j ≤ n` of
`f + g`, for `f` and `g` of class `C^n` on `s`, is at most the sum of those of `f` and `g`. -/
theorem eLpNorm_iteratedFDeriv_add_restrict_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (μ : Measure E) {p : ℝ≥0∞} (hp : 1 ≤ p) {s : Set E} (hs : IsOpen s)
    {n : WithTop ℕ∞} {f g : E → G} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) {j : ℕ}
    (hj : j ≤ n) :
    eLpNorm (iteratedFDeriv ℝ j fun x ↦ f x + g x) p (μ.restrict s) ≤
      eLpNorm (iteratedFDeriv ℝ j f) p (μ.restrict s) +
        eLpNorm (iteratedFDeriv ℝ j g) p (μ.restrict s) := by
  have hfg : iteratedFDeriv ℝ j (fun x ↦ f x + g x) =ᵐ[μ.restrict s]
      iteratedFDeriv ℝ j f + iteratedFDeriv ℝ j g := by
    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
    exact iteratedFDeriv_add_apply ((hf.contDiffAt (hs.mem_nhds hx)).of_le hj)
      ((hg.contDiffAt (hs.mem_nhds hx)).of_le hj)
  refine (eLpNorm_congr_ae hfg).trans_le ?_
  exact eLpNorm_add_le (f := iteratedFDeriv ℝ j f) (g := iteratedFDeriv ℝ j g) hp

end SymplecticGeometry
