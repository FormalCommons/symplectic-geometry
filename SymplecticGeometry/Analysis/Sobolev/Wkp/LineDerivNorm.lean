/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Normed.Operator.Bilinear
public import SymplecticGeometry.MeasureTheory.Function.LpSpace.Basic

/-!
# Directional weak derivatives and the norm of `W^{k+1,p}(Ω)`

Two estimates, with constants that do not depend on `Ω`, `p` or the measure, connect the norm of
`W^{k+1,p}(Ω)` with the directional weak derivatives `TauCeti.Wkp.lineDerivL`:

* `TauCeti.Wkp.norm_lineDerivL_apply_le`: `‖∂ᵥu‖ ≤ (k + 1) ‖v‖ ‖u‖`;
* `TauCeti.Wkp.norm_le_mul_norm_value_add_sum_norm_lineDerivL`: for an orthonormal basis
  `(eᵢ)`, `‖u‖ ≤ (k + 1) (‖u‖_{Lᵖ} + ∑ᵢ ‖∂ᵢu‖)`.

The first adapts the induction of Tau Ceti's private
`TauCeti.Wkp.exists_norm_le_of_hasWeakLineDerivOn`, which gives a bound for each `Ω` without
naming the constant. Along the way, `TauCeti.Wkp.lowerOrder_lineDerivL` says that directional
derivatives commute with forgetting the highest weak derivative, and
`TauCeti.Wkp.lineDerivL_zero` computes the directional derivative at order zero.
-/

public section

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Directional weak derivatives commute with forgetting the highest weak derivative. -/
theorem lowerOrder_lineDerivL (v : E) (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    lowerOrder k (lineDerivL v (k + 1) u) = lineDerivL v k (lowerOrder (k + 1) u) := by
  symm
  apply lineDerivL_eq_of_hasWeakLineDerivOn
  rw [← value_succ, ← value_succ]
  exact hasWeakLineDerivOn_lineDerivL v (k + 1) u

/-- At order zero, the directional derivative of `u ∈ W^{1,p}(Ω)` in the direction `v` is the
component `⟪v, ∇u⟫` of its weak gradient. -/
theorem lineDerivL_zero (v : E) (u : Wkp mu Omega p 1) :
    lineDerivL v 0 u = (innerSL ℝ v).compLp (iteratedGradient 0 u) :=
  lineDerivL_eq_of_hasWeakLineDerivOn (hasWeakLineDerivOn_value_innerSL_compLp v u)

/-- **The directional derivative is bounded uniformly in `Ω`.** The weak derivative of
`u ∈ W^{k+1,p}(Ω)` in the direction `v` has `W^{k,p}` norm at most `(k + 1) ‖v‖ ‖u‖`. -/
theorem norm_lineDerivL_apply_le (v : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)), ‖lineDerivL v k u‖ ≤ (k + 1) * ‖v‖ * ‖u‖
  | 0, u => by
    -- `Wkp mu Omega p 0` is `Lp ℝ p (mu.restrict Omega)`, with the same norm
    rw [lineDerivL_zero, Nat.cast_zero, zero_add, one_mul, ← innerSL_apply_norm ℝ v]
    exact ((innerSL ℝ v).norm_compLp_le _).trans
      (mul_le_mul_of_nonneg_left (norm_iteratedGradient_le 0 u) (norm_nonneg _))
  | k + 1, u => by
    have hlow : ‖lowerOrder k (lineDerivL v (k + 1) u)‖ ≤ (k + 1) * ‖v‖ * ‖u‖ := by
      rw [lowerOrder_lineDerivL]
      exact (norm_lineDerivL_apply_le v k _).trans
        (mul_le_mul_of_nonneg_left (norm_lowerOrder_le _ u) (by positivity))
    have htop : ‖iteratedGradient k (lineDerivL v (k + 1) u)‖ ≤ ‖v‖ * ‖u‖ := by
      rw [iteratedGradient_lineDerivL]
      exact ((ContinuousLinearMap.apply ℝ (IteratedGradient E k) v).norm_compLp_le _).trans
        (mul_le_mul (ContinuousLinearMap.opNorm_apply_apply_le v) (norm_iteratedGradient_le _ u)
          (norm_nonneg _) (norm_nonneg _))
    calc ‖lineDerivL v (k + 1) u‖
        ≤ ‖lowerOrder k (lineDerivL v (k + 1) u)‖ +
            ‖iteratedGradient k (lineDerivL v (k + 1) u)‖ :=
          norm_le_norm_lowerOrder_add_norm_iteratedGradient k _
      _ ≤ (k + 1) * ‖v‖ * ‖u‖ + ‖v‖ * ‖u‖ := add_le_add hlow htop
      _ = ((k + 1 : ℕ) + 1) * ‖v‖ * ‖u‖ := by push_cast; ring

variable {ι : Type*} [Fintype ι]

/-- **The norm of `W^{k+1,p}(Ω)` from directional derivatives.** For an orthonormal basis
`(eᵢ)` of `E`, the norm of `u ∈ W^{k+1,p}(Ω)` is at most `k + 1` times the sum of the `Lᵖ` norm
of `u` and the `W^{k,p}` norms of its weak derivatives `∂ᵢu` along the basis. -/
theorem norm_le_mul_norm_value_add_sum_norm_lineDerivL (b : OrthonormalBasis ι ℝ E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)),
      ‖u‖ ≤ (k + 1) * (‖value (k + 1) u‖ + ∑ i, ‖lineDerivL (b i) k u‖)
  | 0, u => by
    have hg : ‖iteratedGradient 0 u‖ ≤ ∑ i, ‖lineDerivL (b i) 0 u‖ := by
      -- as in `norm_lineDerivL_apply_le`, the norm of `Wkp mu Omega p 0` is the `Lᵖ` norm
      refine (Lp.norm_le_sum_norm_compLp (fun i => innerSL ℝ (b i))
        (fun i => ContinuousLinearMap.toSpanSingleton ℝ (b i)) (fun x => ?_) (fun i => ?_)
        _).trans_eq (Finset.sum_congr rfl fun i _ => by rw [lineDerivL_zero])
      · simpa only [ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply] using
          b.sum_repr' x
      · rw [ContinuousLinearMap.norm_toSpanSingleton, b.norm_eq_one]
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
