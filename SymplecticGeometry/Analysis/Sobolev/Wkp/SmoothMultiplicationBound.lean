/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import SymplecticGeometry.Analysis.Sobolev.Wkp.LineDerivNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Norm bounds for smooth multiplication on `W^{k,p}(Ω)`

Let `Ω` be an open set whose closure is compact and contained in a set `U` of unique
differentiability, and let `ψ` be smooth on `U`. Tau Ceti shows that multiplication by `ψ` is a
bounded operator on `W^{k,p}(Ω)` (`TauCeti.Wkp.contDiffOnSMulL`), through the closed graph
theorem, which gives no bound on its norm. This file bounds it: there is a constant `C`,
depending only on `k` and `E`, such that

`‖ψ u‖_{W^{k,p}(Ω)} ≤ C M ‖u‖_{W^{k,p}(Ω)}`

whenever `‖D^j ψ‖ ≤ M` on `Ω` for all `j ≤ k`, the derivatives being taken within `U`
(`TauCeti.Wkp.exists_norm_contDiffOnSMulL_le`). The same holds for multiplication by a smooth
operator-valued coefficient in fixed bases (`TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le`),
with a constant that also depends on the bases.

The proof is by induction on `k`, along the proof of Tau Ceti's
`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`: the directional derivative of `ψ u` is
`ψ ∂ᵥu + (∂ᵥψ) u` (`TauCeti.Wkp.lineDerivL_contDiffOnSMulL`), and both terms are bounded by the
induction hypothesis. The norm of `W^{k+1,p}(Ω)` is then recovered from the directional
derivatives by the estimates of `SymplecticGeometry.Analysis.Sobolev.Wkp.LineDerivNorm`.

## Main declarations

* `TauCeti.Wkp.lineDerivL_contDiffOnSMulL`: the Leibniz rule for smooth multiplication.
* `TauCeti.Wkp.exists_norm_contDiffOnSMulL_le`,
  `TauCeti.Wkp.exists_norm_contDiffOnCLMApplyL_le`: the `C^k` bounds.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §5.2.3, Theorem 1(iv)
-/

public section

noncomputable section

open MeasureTheory Module TopologicalSpace
open scoped ContDiff InnerProductSpace

namespace TauCeti

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

variable {ι : Type*} [Fintype ι]

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
      have h := norm_iteratedFDerivWithin_clm_apply_const (N := ∞) (n := j) (c := b i)
        ((hpsi.fderivWithin hU (by simp)) x hxU) hU hxU (by exact_mod_cast le_top)
      rw [norm_iteratedFDerivWithin_fderivWithin hU hxU, b.norm_eq_one, one_mul] at h
      exact h.trans (hM (j + 1) (by omega) x hx)
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
