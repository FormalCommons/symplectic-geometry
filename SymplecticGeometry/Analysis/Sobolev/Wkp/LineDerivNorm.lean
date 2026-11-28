/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Seminorm
import SymplecticGeometry.MeasureTheory.Function.LpSpace.Basic

/-!
# Directional weak derivatives and the norm of `W^{k+1,p}(Ω)`

For an orthonormal basis `(eᵢ)` of `E`, the norm of `u ∈ W^{k+1,p}(Ω)` is bounded by the `Lᵖ`
norm of `u` and the `W^{k,p}` norms of its directional weak derivatives `TauCeti.Wkp.lineDerivL`
along the basis, with a constant that depends only on `k`:

* `TauCeti.Wkp.norm_le_mul_norm_value_add_sum_norm_lineDerivL`:
  `‖u‖ ≤ (k + 1) (‖u‖_{Lᵖ} + ∑ᵢ ‖∂ᵢu‖)`.

It is a converse of Tau Ceti's `TauCeti.Wkp.norm_lineDerivL_apply_le`, which bounds each
`‖∂ᵥu‖` by `√2 ‖v‖ ‖u‖`. The proof is by induction on `k`, through Tau Ceti's
`TauCeti.Wkp.lowerOrder_lineDerivL`, by which directional derivatives commute with forgetting the
highest weak derivative. At order zero, the weak gradient is bounded by the case `j = 0` of
Tau Ceti's `TauCeti.Wkp.norm_iteratedGradient_le_sum_norm_iteratedLineDerivZeroL`.
-/

public section

open MeasureTheory TopologicalSpace

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

variable {ι : Type*} [Fintype ι]

/-- **The norm of `W^{k+1,p}(Ω)` from directional derivatives.** For an orthonormal basis
`(eᵢ)` of `E`, the norm of `u ∈ W^{k+1,p}(Ω)` is at most `k + 1` times the sum of the `Lᵖ` norm
of `u` and the `W^{k,p}` norms of its weak derivatives `∂ᵢu` along the basis. -/
theorem norm_le_mul_norm_value_add_sum_norm_lineDerivL (b : OrthonormalBasis ι ℝ E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)),
      ‖u‖ ≤ (k + 1) * (‖value (k + 1) u‖ + ∑ i, ‖lineDerivL (b i) k u‖)
  | 0, u => by
    have hg : ‖iteratedGradient 0 u‖ ≤ ∑ i, ‖lineDerivL (b i) 0 u‖ := by
      -- the order-zero case of Tau Ceti's bound by iterated directional derivatives, whose sum
      -- runs over the one-element tuples of basis indices
      refine (norm_iteratedGradient_le_sum_norm_iteratedLineDerivZeroL 0 b u).trans_eq ?_
      exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun r => by
        simp [iteratedLineDerivZeroL_one, Equiv.funUnique_apply, Fin.default_eq_zero]
    have hv : ‖lowerOrder 0 u‖ = ‖value 1 u‖ := by rw [value_succ, value_zero]
    calc ‖u‖ ≤ ‖lowerOrder 0 u‖ + ‖iteratedGradient 0 u‖ :=
          norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      _ ≤ ‖value 1 u‖ + ∑ i, ‖lineDerivL (b i) 0 u‖ := by rw [hv]; gcongr
      _ = ((0 : ℕ) + 1) * (‖value (0 + 1) u‖ + ∑ i, ‖lineDerivL (b i) 0 u‖) := by simp
  | k + 1, u => by
    have hlow : ‖lowerOrder (k + 1) u‖ ≤
        (k + 1) * (‖value (k + 2) u‖ + ∑ i, ‖lineDerivL (b i) (k + 1) u‖) := by
      refine (norm_le_mul_norm_value_add_sum_norm_lineDerivL b k _).trans ?_
      rw [← value_succ]
      gcongr with i
      rw [← lowerOrder_lineDerivL]
      exact norm_lowerOrder_le _ _
    have htop : ‖iteratedGradient (k + 1) u‖ ≤ ∑ i, ‖lineDerivL (b i) (k + 1) u‖ := by
      refine (Lp.norm_le_sum_norm_compLp
        (fun i => ContinuousLinearMap.apply ℝ (IteratedGradient E k) (b i))
        (fun i => StrongDual.smulRightL ℝ E (IteratedGradient E k) (innerSL ℝ (b i))) (fun A => ?_)
        (fun i => ?_) _).trans (Finset.sum_le_sum fun i _ => ?_)
      · ext h
        conv_rhs => rw [← b.sum_repr' h]
        simp [map_sum, map_smul]
      · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
        rw [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.norm_smulRight_apply,
          innerSL_apply_norm, b.norm_eq_one, one_mul]
      · rw [← iteratedGradient_lineDerivL]
        exact norm_iteratedGradient_le _ _
    calc ‖u‖ ≤ ‖lowerOrder (k + 1) u‖ + ‖iteratedGradient (k + 1) u‖ :=
          norm_le_norm_lowerOrder_add_norm_iteratedGradient (k + 1) u
      _ ≤ (k + 1) * (‖value (k + 2) u‖ + ∑ i, ‖lineDerivL (b i) (k + 1) u‖) +
            ∑ i, ‖lineDerivL (b i) (k + 1) u‖ := add_le_add hlow htop
      _ ≤ ((k + 1 : ℕ) + 1) * (‖value (k + 1 + 1) u‖ + ∑ i, ‖lineDerivL (b i) (k + 1) u‖) := by
        push_cast
        nlinarith [norm_nonneg (value (k + 2) u),
          Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => norm_nonneg (lineDerivL (b i) (k + 1) u)]

end Wkp

end TauCeti

end
