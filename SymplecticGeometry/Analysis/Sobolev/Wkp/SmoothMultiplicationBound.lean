/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Norm bounds for smooth multiplication on `W^{k,p}(Ω)`

Let `Ω` be an open set whose closure is compact and contained in a set `U` of unique
differentiability, and let `ψ` be smooth on `U`. Tau Ceti shows that multiplication by `ψ` is a
bounded operator on `W^{k,p}(Ω)` (`TauCeti.Wkp.contDiffOnSMulL`), through the closed graph
theorem, which gives no bound on its norm. This file bounds it: there is a constant `C`,
depending only on `k` and the dimension of `E`, such that

`‖ψ u‖_{W^{k,p}(Ω)} ≤ C M ‖u‖_{W^{k,p}(Ω)}`

whenever `‖D^j ψ‖ ≤ M` on `Ω` for all `j ≤ k`, the derivatives being taken within `U`
(`TauCeti.Wkp.exists_norm_contDiffOnSMulL_le`). The same holds for multiplication by a smooth
operator-valued coefficient in fixed bases (`TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le`),
with a constant that also depends on the bases.

The proof is by induction on `k`, along the proof of Tau Ceti's
`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`: the directional derivative of `ψ u` is
`ψ ∂ᵥu + (∂ᵥψ) u` (`TauCeti.Wkp.lineDerivL_contDiffOnSMulL`), and both terms are bounded by the
induction hypothesis. Two estimates, uniform in `Ω`, connect the norm of `W^{k+1,p}(Ω)` with
directional derivatives: `‖∂ᵥu‖ ≤ (k + 1) ‖v‖ ‖u‖` (`TauCeti.Wkp.norm_lineDerivL_apply_le`), and,
for an orthonormal basis `(eᵢ)`, `‖u‖ ≤ (k + 1) (‖u‖_{Lᵖ} + ∑ᵢ ‖∂ᵢu‖)`
(`TauCeti.Wkp.norm_le_mul_norm_value_add_sum_norm_lineDerivL`). The first adapts the induction
of Tau Ceti's private `TauCeti.Wkp.exists_norm_le_of_hasWeakLineDerivOn`, which gives a bound
for each `Ω` without naming the constant.

## Main declarations

* `TauCeti.Wkp.lowerOrder_lineDerivL`: directional derivatives commute with forgetting the highest
  weak derivative.
* `TauCeti.Wkp.norm_lineDerivL_apply_le`: the bound on directional derivatives.
* `TauCeti.Wkp.norm_le_mul_norm_value_add_sum_norm_lineDerivL`: the norm of `W^{k+1,p}(Ω)` is
  controlled by the `Lᵖ` norm and the `W^{k,p}` norms of the derivatives along a basis.
* `TauCeti.Wkp.lineDerivL_contDiffOnSMulL`: the Leibniz rule for smooth multiplication.
* `TauCeti.Wkp.exists_norm_contDiffOnSMulL_le`,
  `TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le`: the `C^k` bounds.

## References

L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv).
-/

public section

noncomputable section

open MeasureTheory Module TopologicalSpace
open scoped ContDiff InnerProductSpace

namespace MeasureTheory.Lp

variable {α F G : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal} [Fact (1 ≤ p)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]

/-- If `∑ᵢ Qᵢ ∘ Pᵢ` is the identity of `F` and every `Qᵢ` has norm at most one, then the `Lᵖ` norm
of `f` is at most the sum of the `Lᵖ` norms of the `Pᵢ f`. -/
theorem norm_le_sum_norm_compLp (P : ι → F →L[ℝ] G) (Q : ι → G →L[ℝ] F)
    (hPQ : ∀ x, ∑ i, Q i (P i x) = x) (hQ : ∀ i, ‖Q i‖ ≤ 1) (f : Lp F p μ) :
    ‖f‖ ≤ ∑ i, ‖(P i).compLp f‖ := by
  have hf : f = ∑ i, (Q i).compLp ((P i).compLp f) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i => (Q i).compLp ((P i).compLp f),
      ae_all_iff.2 fun i => (Q i).coeFn_compLp ((P i).compLp f),
      ae_all_iff.2 fun i => (P i).coeFn_compLp f] with x hs hQx hPx
    rw [hs]
    simp only [hQx, hPx, hPQ]
  calc ‖f‖ = ‖∑ i, (Q i).compLp ((P i).compLp f)‖ := congrArg _ hf
    _ ≤ ∑ i, ‖(Q i).compLp ((P i).compLp f)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖(P i).compLp f‖ := Finset.sum_le_sum fun i _ =>
        ((Q i).norm_compLp_le _).trans (mul_le_of_le_one_left (norm_nonneg _) (hQ i))

end MeasureTheory.Lp

namespace ContinuousLinearMap

/-- Evaluation at `v`, as a continuous linear map on `E →L[𝕜] F`, has norm at most `‖v‖`. -/
theorem norm_apply_le {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (v : E) :
    ‖apply 𝕜 F v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg v) fun A => by
    rw [apply_apply, mul_comm]
    exact A.le_opNorm v

end ContinuousLinearMap

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Directional derivatives and the norm of `W^{k+1,p}(Ω)` -/

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
        (mul_le_mul (ContinuousLinearMap.norm_apply_le v) (norm_iteratedGradient_le _ u)
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

/-! ### Smooth multiplication -/

variable {U : Set E} {psi : E → ℝ}

/-- **The Leibniz rule for smooth multiplication.** The derivative of `ψ u` in the direction `v`
is `ψ ∂ᵥu + (∂ᵥψ) u`, where `∂ᵥψ` is the derivative of `ψ` within `U`. -/
theorem lineDerivL_contDiffOnSMulL (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (v : E) (u : Wkp mu Omega p (k + 1)) :
    lineDerivL v k (contDiffOnSMulL hU hΩ hΩU (k + 1) hpsi u) =
      contDiffOnSMulL hU hΩ hΩU k hpsi (lineDerivL v k u) +
        contDiffOnSMulL hU hΩ hΩU k
          ((hpsi.fderivWithin hU (by simp)).clm_apply (contDiffOn_const (c := v)))
          (lowerOrder k u) := by
  apply lineDerivL_eq_of_hasWeakLineDerivOn
  refine ((hasWeakLineDerivOn_lineDerivL v k u).contDiffOn_smul_of_ne_zero
    (hpsi.mono (subset_closure.trans hΩU)) (by simp)).congr_ae ?_ |>.congr_ae_deriv ?_
  · filter_upwards [value_contDiffOnSMulL_ae hU hΩ hΩU (k + 1) hpsi u] with x hx
    rw [hx, smul_eq_mul]
  · filter_upwards [value_add_ae k (contDiffOnSMulL hU hΩ hΩU k hpsi (lineDerivL v k u))
        (contDiffOnSMulL hU hΩ hΩU k
          ((hpsi.fderivWithin hU (by simp)).clm_apply (contDiffOn_const (c := v)))
          (lowerOrder k u)),
      value_contDiffOnSMulL_ae hU hΩ hΩU k hpsi (lineDerivL v k u),
      value_contDiffOnSMulL_ae hU hΩ hΩU k
        ((hpsi.fderivWithin hU (by simp)).clm_apply (contDiffOn_const (c := v))) (lowerOrder k u),
      ae_restrict_mem Omega.isOpen.measurableSet] with x hx h₁ h₂ hxΩ
    rw [hx, Pi.add_apply, h₁, h₂, ← value_succ, smul_eq_mul, smul_eq_mul,
      fderivWithin_of_mem_nhds (Filter.mem_of_superset (Omega.isOpen.mem_nhds hxΩ)
        (subset_closure.trans hΩU))]

variable (E) in
/-- **A `C^k` bound for smooth multiplication on `W^{k,p}(Ω)`.** For every order `k` there is a
constant `C`, depending only on `k` and `E`, such that for every open `Ω` with compact closure in
a set `U` of unique differentiability, every exponent `1 ≤ p ≤ ∞`, and every `ψ` smooth on `U`
whose derivatives within `U` of order at most `k` are bounded by `M` on `Ω`, multiplication by
`ψ` on `W^{k,p}(Ω)` has norm at most `C M`. -/
theorem exists_norm_contDiffOnSMulL_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal}
      [Fact (1 ≤ p)] {U : Set E} {psi : E → ℝ} (hU : UniqueDiffOn ℝ U)
      (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U)
      (hpsi : ContDiffOn ℝ ∞ psi U) {M : ℝ},
      (∀ j ≤ k, ∀ x ∈ (Omega : Set E), ‖iteratedFDerivWithin ℝ j psi U x‖ ≤ M) →
      ∀ u : Wkp mu Omega p k, ‖contDiffOnSMulL hU hΩ hΩU k hpsi u‖ ≤ C * M * ‖u‖ := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, fun hU hΩ hΩU hpsi M hM u => ?_⟩
    have h := norm_value_contDiffOnSMulL_le hU hΩ hΩU 0 hpsi
      (fun x hx => by simpa only [norm_iteratedFDerivWithin_zero] using hM 0 le_rfl x hx) u
    simpa only [value_zero, one_mul] using h
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    set n : ℝ := (finrank ℝ E : ℝ)
    refine ⟨(k + 1) * (1 + n * (C * (k + 2))), by positivity,
      fun {mu} _ {Omega} {p} _ {U} {psi} hU hΩ hΩU hpsi M hM u => ?_⟩
    have hM0 : ∀ x ∈ (Omega : Set E), ‖psi x‖ ≤ M := fun x hx => by
      simpa only [norm_iteratedFDerivWithin_zero] using hM 0 (Nat.zero_le _) x hx
    -- on an empty `Ω` both sides vanish; otherwise `M ≥ 0`
    rcases (Omega : Set E).eq_empty_or_nonempty with hΩe | ⟨x₀, hx₀⟩
    · have := subsingleton_of_eq_empty (mu := mu) (p := p) (k + 1) hΩe
      simp [Subsingleton.elim u 0]
    have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM0 x₀ hx₀)
    set b := stdOrthonormalBasis ℝ E
    set w := contDiffOnSMulL hU hΩ hΩU (k + 1) hpsi u
    -- the derivative `∂ᵢψ` within `U` and its derivatives up to order `k` are bounded by `M`
    have hφ : ∀ i, ∀ j ≤ k, ∀ x ∈ (Omega : Set E), ‖iteratedFDerivWithin ℝ j
        (fun y => fderivWithin ℝ psi U y (b i)) U x‖ ≤ M := fun i j hj x hx => by
      have hxU : x ∈ U := hΩU (subset_closure hx)
      have h := (ContinuousLinearMap.apply ℝ ℝ (b i)).norm_iteratedFDerivWithin_comp_left
        (f := fderivWithin ℝ psi U) (N := ∞) (n := j) ((hpsi.fderivWithin hU (by simp)) x hxU) hU
        hxU (by exact_mod_cast le_top)
      rw [norm_iteratedFDerivWithin_fderivWithin hU hxU] at h
      refine h.trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hM (j + 1) (by omega) x hx))
      exact (ContinuousLinearMap.norm_apply_le (b i)).trans (b.norm_eq_one i).le
    have hval : ‖value (k + 1) w‖ ≤ M * ‖u‖ :=
      (norm_value_contDiffOnSMulL_le hU hΩ hΩU (k + 1) hpsi hM0 u).trans
        (mul_le_mul_of_nonneg_left (norm_value_le _ u) hMnn)
    have hder : ∀ i, ‖lineDerivL (b i) k w‖ ≤ C * (k + 2) * M * ‖u‖ := fun i => by
      rw [lineDerivL_contDiffOnSMulL]
      refine (norm_add_le _ _).trans ?_
      have h₁ := hC hU hΩ hΩU hpsi (fun j hj => hM j (by omega)) (lineDerivL (b i) k u)
      have h₂ := hC hU hΩ hΩU ((hpsi.fderivWithin hU (by simp)).clm_apply
        (contDiffOn_const (c := b i))) (hφ i) (lowerOrder k u)
      have h₃ := norm_lineDerivL_apply_le (b i) k u
      rw [b.norm_eq_one, mul_one] at h₃
      have h₄ := norm_lowerOrder_le k u
      have : 0 ≤ C * M := mul_nonneg hC0 hMnn
      calc _ ≤ C * M * ‖lineDerivL (b i) k u‖ + C * M * ‖lowerOrder k u‖ := add_le_add h₁ h₂
        _ ≤ C * M * ((k + 1) * ‖u‖) + C * M * ‖u‖ := by gcongr
        _ = C * (k + 2) * M * ‖u‖ := by ring
    have hsum : ∑ i, ‖lineDerivL (b i) k w‖ ≤ n * (C * (k + 2) * M * ‖u‖) := by
      refine (Finset.sum_le_sum fun i _ => hder i).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖w‖ ≤ (k + 1) * (‖value (k + 1) w‖ + ∑ i, ‖lineDerivL (b i) k w‖) :=
          norm_le_mul_norm_value_add_sum_norm_lineDerivL b k w
      _ ≤ (k + 1) * (M * ‖u‖ + n * (C * (k + 2) * M * ‖u‖)) := by gcongr
      _ = (k + 1) * (1 + n * (C * (k + 2))) * M * ‖u‖ := by ring

/-! ### Smooth operator coefficients -/

variable {κ F F' : Type*} [Fintype κ] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']

variable (E) in
/-- **A `C^k` bound for smooth operator coefficients on `W^{k,p}(Ω)`.** For every order `k` and
bases `b` of `F` and `b'` of `F'` there is a constant `C`, depending only on `k`, `E` and the
bases, such that for every open `Ω` with compact closure in a set `U` of unique
differentiability, every exponent `1 ≤ p ≤ ∞`, and every `g : E → F →L[ℝ] F'` smooth on `U`
whose derivatives within `U` of order at most `k` are bounded by `M` on `Ω`, multiplication by
the matrix of `g` on tuples in `W^{k,p}(Ω)` has norm at most `C M`. -/
theorem exists_norm_contDiffOnCLMApplyL_le (k : ℕ) (b : Basis ι ℝ F) (b' : Basis κ ℝ F') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal}
      [Fact (1 ≤ p)] {U : Set E} {g : E → F →L[ℝ] F'} (hU : UniqueDiffOn ℝ U)
      (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U)
      (hg : ContDiffOn ℝ ∞ g U) {M : ℝ},
      (∀ j ≤ k, ∀ x ∈ (Omega : Set E), ‖iteratedFDerivWithin ℝ j g U x‖ ≤ M) →
      ∀ u : ι → Wkp mu Omega p k,
        ‖contDiffOnCLMApplyL hU hΩ hΩU k b b' hg u‖ ≤ C * M * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_contDiffOnSMulL_le E k
  -- the entry `(m, l)` of the matrix of `g` is `L m l ∘ g`
  set L : κ → ι → (F →L[ℝ] F') →L[ℝ] ℝ := fun m l =>
    (b'.coord m).toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ F' (b l))
  set K : ℝ := ∑ m, ∑ l, ‖L m l‖
  refine ⟨C * K, by positivity, fun {mu} _ {Omega} {p} _ {U} {g} hU hΩ hΩU hg M hM u => ?_⟩
  -- on an empty `Ω` both sides vanish; otherwise `M ≥ 0`
  rcases (Omega : Set E).eq_empty_or_nonempty with hΩe | ⟨x₀, hx₀⟩
  · have := subsingleton_of_eq_empty (mu := mu) (p := p) k hΩe
    simp [Subsingleton.elim u 0]
  have hMnn : 0 ≤ M := (norm_nonneg _).trans <| by
    simpa only [norm_iteratedFDerivWithin_zero] using hM 0 (Nat.zero_le _) x₀ hx₀
  have hentry : ∀ m l, ‖contDiffOnSMulL hU hΩ hΩU k
      ((hg.clm_apply (contDiffOn_const (c := b l))).continuousLinearMap_comp
        (b'.coord m).toContinuousLinearMap) (u l)‖ ≤ C * (‖L m l‖ * M) * ‖u‖ := fun m l => by
    refine (hC (M := ‖L m l‖ * M) hU hΩ hΩU _ (fun j hj x hx => ?_) (u l)).trans ?_
    · have hxU : x ∈ U := hΩU (subset_closure hx)
      exact ((L m l).norm_iteratedFDerivWithin_comp_left (f := g) (N := ∞) (n := j) (hg x hxU) hU
        hxU (by exact_mod_cast le_top)).trans
        (mul_le_mul_of_nonneg_left (hM j hj x hx) (norm_nonneg _))
    · exact mul_le_mul_of_nonneg_left (norm_le_pi_norm u l) (by positivity)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun m => ?_
  rw [contDiffOnCLMApplyL_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ => hentry m l).trans ?_)
  have hK : ∑ l, ‖L m l‖ ≤ K :=
    Finset.single_le_sum (f := fun m => ∑ l, ‖L m l‖) (fun m _ => by positivity)
      (Finset.mem_univ m)
  calc ∑ l, C * (‖L m l‖ * M) * ‖u‖ = C * (∑ l, ‖L m l‖) * M * ‖u‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ C * K * M * ‖u‖ := by gcongr

end Wkp

end TauCeti
