/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Complex.Avoidance
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Local quantitative transversality

A function `f` on the ball of radius `11 / 10` in `ℂⁿ` that is bounded in `C¹` by one and whose
`∂̄f` is small in `C¹` can be perturbed by a small affine function `w₀ + Σ_j w_j z_j` so that, on
the closed unit ball, the perturbed function and its Wirtinger derivative `∂` are never both
small. The size of the perturbation is `δ` and the lower bound is `δ / (log (1 / δ)) ^ p`.

## Main results

* `SymplecticGeometry.exists_norm_le_max_ge_of_dbar_le`: the estimate, with an exponent `p`
  depending only on `n` and all `δ` small enough.

## Implementation notes

The estimate is deduced from Auroux's avoidance estimate
`SymplecticGeometry.exists_infDist_image_ge`, applied to `K⁻¹ G` for the map
`G = (f - Σ_j z_j ∂_j f, ∂_1 f, …, ∂_n f) : ℂⁿ → ℂⁿ⁺¹`, where `K = 3 n + 1` bounds `|G|` on the
ball, with the parameter `δ / K`. For `f` of class `C²` the mixed Wirtinger derivatives
commute (`TauCeti.wirtingerDeriv_conjWirtingerDeriv_comm`), so `∂̄(∂_j f)` is `∂_j` of
`∂̄f(·) v`, and the `C¹` bound on `∂̄f` bounds `∂̄G` by `(3 n + 1) ε`.
For a point `w` far from `G` of the unit ball, the identity
`G - w = (f_w - Σ_j z_j ∂_j f_w, ∂_1 f_w, …, ∂_n f_w)` bounds `|G - w|` by `(n + 2)` times
`max |f_w| ‖∂f_w‖`. The exponent is `p = p₀ + 1` for the exponent `p₀` of the avoidance
estimate; the extra power of `log (1 / δ)` absorbs the constants.

Only the first derivatives of `∂̄f` enter, so the hypothesis on `∂̄f` is a `C¹` bound, weaker
than the `C²` bound one might ask for.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Proposition 3.
* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2.
-/

public section

open Metric TauCeti ContinuousLinearMap

namespace SymplecticGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The map `G = (f - Σ_j z_j ∂_j f, ∂_1 f, …, ∂_n f)` to which the avoidance estimate is
applied. -/
private noncomputable def transversalityMap (f : EuclideanSpace ℂ σ → ℂ)
    (z : EuclideanSpace ℂ σ) : EuclideanSpace ℂ (Option σ) :=
  WithLp.toLp 2 fun o ↦ Option.elim o
    (f z - ∑ j, z j * wirtingerDeriv f z (EuclideanSpace.single j 1))
    (fun j ↦ wirtingerDeriv f z (EuclideanSpace.single j 1))

private theorem transversalityMap_none (f : EuclideanSpace ℂ σ → ℂ) (z : EuclideanSpace ℂ σ) :
    transversalityMap f z none =
      f z - ∑ j, z j * wirtingerDeriv f z (EuclideanSpace.single j 1) :=
  (rfl)

private theorem transversalityMap_some (f : EuclideanSpace ℂ σ → ℂ) (z : EuclideanSpace ℂ σ)
    (j : σ) : transversalityMap f z (some j) = wirtingerDeriv f z (EuclideanSpace.single j 1) :=
  (rfl)

private theorem contDiffAt_transversalityMap {f : EuclideanSpace ℂ σ → ℂ}
    {z : EuclideanSpace ℂ σ} (hf : ContDiffAt ℝ 2 f z) :
    ContDiffAt ℝ 1 (transversalityMap f) z := by
  rw [contDiffAt_piLp]
  rintro (_ | j)
  · simp only [transversalityMap_none]
    exact (hf.of_le one_le_two).sub (ContDiffAt.sum fun j _ ↦
      (contDiffAt_piLp_apply (p := 2) (i := j)).mul (hf.wirtingerDeriv_apply (by norm_num) _))
  · simp only [transversalityMap_some]
    exact hf.wirtingerDeriv_apply (by norm_num) _

private theorem norm_wirtingerDeriv_single_le {f : EuclideanSpace ℂ σ → ℂ}
    {z : EuclideanSpace ℂ σ} (hf1 : ‖fderiv ℝ f z‖ ≤ 1) (j : σ) :
    ‖wirtingerDeriv f z (EuclideanSpace.single j 1)‖ ≤ 1 := by
  simpa using (norm_wirtingerDeriv_apply_le f z _).trans
    (mul_le_mul_of_nonneg_right hf1 (norm_nonneg (EuclideanSpace.single j (1 : ℂ))))

private theorem norm_transversalityMap_le {f : EuclideanSpace ℂ σ → ℂ}
    {z : EuclideanSpace ℂ σ} (hf0 : ‖f z‖ ≤ 1) (hf1 : ‖fderiv ℝ f z‖ ≤ 1) (hz : ‖z‖ ≤ 2) :
    ‖transversalityMap f z‖ ≤ 3 * Fintype.card σ + 1 := by
  have hnone : ‖transversalityMap f z none‖ ≤ 1 + 2 * Fintype.card σ := by
    rw [transversalityMap_none]
    calc _ ≤ ‖f z‖ + ∑ j, ‖z j * wirtingerDeriv f z (EuclideanSpace.single j 1)‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ 1 + ∑ _j : σ, (2 : ℝ) := by
          refine add_le_add hf0 (Finset.sum_le_sum fun j _ ↦ ?_)
          rw [norm_mul]
          simpa using mul_le_mul ((PiLp.norm_apply_le z j).trans hz)
            (norm_wirtingerDeriv_single_le hf1 j) (norm_nonneg _) zero_le_two
      _ = 1 + 2 * Fintype.card σ := by simp [mul_comm]
  calc _ ≤ ∑ o, ‖transversalityMap f z o‖ := PiLp.norm_le_sum_norm _
    _ = ‖transversalityMap f z none‖ + ∑ j, ‖transversalityMap f z (some j)‖ :=
        Fintype.sum_option _
    _ ≤ (1 + 2 * Fintype.card σ) + ∑ _j : σ, (1 : ℝ) :=
        add_le_add hnone (Finset.sum_le_sum fun j _ ↦ norm_wirtingerDeriv_single_le hf1 j)
    _ = 3 * Fintype.card σ + 1 := by simp; ring

private theorem norm_conjWirtingerDeriv_transversalityMap_le {f : EuclideanSpace ℂ σ → ℂ}
    {z : EuclideanSpace ℂ σ} {ε : ℝ} (hf : ContDiffAt ℝ 2 f z)
    (hε0 : ‖conjWirtingerDeriv f z‖ ≤ ε)
    (hε1 : ∀ b, ‖fderiv ℝ (fun y ↦ conjWirtingerDeriv f y b) z‖ ≤ ε * ‖b‖) (hz : ‖z‖ ≤ 2)
    (v : EuclideanSpace ℂ σ) :
    ‖conjWirtingerDeriv (transversalityMap f) z v‖ ≤ (3 * Fintype.card σ + 1) * ε * ‖v‖ := by
  have hd : DifferentiableAt ℝ (transversalityMap f) z :=
    (contDiffAt_transversalityMap hf).differentiableAt one_ne_zero
  have hcomp (o : Option σ) : conjWirtingerDeriv (transversalityMap f) z v o =
      conjWirtingerDeriv (fun y ↦ transversalityMap f y o) z v := by
    have := congrArg (· v) ((EuclideanSpace.proj (𝕜 := ℂ) o).conjWirtingerDeriv_comp_left hd)
    simpa using this.symm
  have hdj (j : σ) : DifferentiableAt ℝ
      (fun y ↦ wirtingerDeriv f y (EuclideanSpace.single j 1)) z :=
    (hf.wirtingerDeriv_apply (m := 1) (by norm_num) _).differentiableAt one_ne_zero
  have hcj (j : σ) : DifferentiableAt ℂ (fun y : EuclideanSpace ℂ σ ↦ y j) z :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt
  have hsome (j : σ) : ‖conjWirtingerDeriv
      (fun y ↦ wirtingerDeriv f y (EuclideanSpace.single j 1)) z v‖ ≤ ε * ‖v‖ := by
    -- `∂̄` of `∂_j f` is `∂_j` of `∂̄f(·) v`, which the `C¹` bound on `∂̄f` controls.
    rw [← wirtingerDeriv_conjWirtingerDeriv_comm hf]
    simpa using (norm_wirtingerDeriv_apply_le _ _ (EuclideanSpace.single j (1 : ℂ))).trans
      (mul_le_mul_of_nonneg_right (hε1 v) (norm_nonneg _))
  have hnone : ‖conjWirtingerDeriv (fun y ↦ transversalityMap f y none) z v‖ ≤
      (1 + 2 * Fintype.card σ) * ε * ‖v‖ := by
    have hsum : DifferentiableAt ℝ
        (fun y ↦ ∑ j, y j * wirtingerDeriv f y (EuclideanSpace.single j 1)) z :=
      DifferentiableAt.fun_sum fun j _ ↦ ((hcj j).restrictScalars ℝ).mul (hdj j)
    simp only [transversalityMap_none]
    rw [conjWirtingerDeriv_fun_sub (hf.differentiableAt two_ne_zero) hsum,
      conjWirtingerDeriv_fun_sum
        (g := fun j y ↦ y j * wirtingerDeriv f y (EuclideanSpace.single j 1))
        fun j _ ↦ ((hcj j).restrictScalars ℝ).mul (hdj j)]
    simp only [conjWirtingerDeriv_fun_mul ((hcj _).restrictScalars ℝ) (hdj _),
      (hcj _).conjWirtingerDeriv_eq_zero, smul_zero, add_zero]
    calc _ ≤ ‖conjWirtingerDeriv f z v‖ + ∑ j, ‖z j • conjWirtingerDeriv
          (fun y ↦ wirtingerDeriv f y (EuclideanSpace.single j 1)) z v‖ := by
          simp only [sub_apply, sum_apply, smul_apply]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ε * ‖v‖ + ∑ _j : σ, 2 * (ε * ‖v‖) := by
          refine add_le_add ((ContinuousLinearMap.le_opNorm _ v).trans
            (mul_le_mul_of_nonneg_right hε0 (norm_nonneg _)))
            (Finset.sum_le_sum fun j _ ↦ ?_)
          rw [norm_smul]
          exact mul_le_mul ((PiLp.norm_apply_le z j).trans hz) (hsome j) (norm_nonneg _)
            zero_le_two
      _ = (1 + 2 * Fintype.card σ) * ε * ‖v‖ := by simp; ring
  calc _ ≤ ∑ o, ‖conjWirtingerDeriv (transversalityMap f) z v o‖ := PiLp.norm_le_sum_norm _
    _ = ‖conjWirtingerDeriv (fun y ↦ transversalityMap f y none) z v‖ +
          ∑ j, ‖conjWirtingerDeriv
            (fun y ↦ wirtingerDeriv f y (EuclideanSpace.single j 1)) z v‖ := by
        rw [Fintype.sum_option]
        simp only [hcomp, transversalityMap_some]
    _ ≤ (1 + 2 * Fintype.card σ) * ε * ‖v‖ + ∑ _j : σ, ε * ‖v‖ :=
        add_le_add hnone (Finset.sum_le_sum fun j _ ↦ hsome j)
    _ = (3 * Fintype.card σ + 1) * ε * ‖v‖ := by simp; ring

private theorem norm_transversalityMap_sub_le {f : EuclideanSpace ℂ σ → ℂ}
    {z : EuclideanSpace ℂ σ} (hf : DifferentiableAt ℝ f z) (hz : ‖z‖ ≤ 1)
    (w : EuclideanSpace ℂ (Option σ)) :
    ‖transversalityMap f z - w‖ ≤ (Fintype.card σ + 2) *
      max ‖f z - w none - ∑ j, w (some j) * z j‖
        ‖wirtingerDeriv (fun y ↦ f y - w none - ∑ j, w (some j) * y j) z‖ := by
  set L : EuclideanSpace ℂ σ →L[ℂ] ℂ := ∑ j, w (some j) • EuclideanSpace.proj j
  have hL (y : EuclideanSpace ℂ σ) : L y = ∑ j, w (some j) * y j := by simp [L]
  have hfun : (fun y ↦ f y - w none - ∑ j, w (some j) * y j) =
      f - fun y ↦ w none + L y := by
    funext y; simp [hL, sub_sub]
  set A := wirtingerDeriv (fun y ↦ f y - w none - ∑ j, w (some j) * y j) z
  have hA : A = wirtingerDeriv f z - L := by
    have hh : DifferentiableAt ℂ (fun y ↦ w none + L y) z :=
      (differentiableAt_const _).add L.differentiableAt
    rw [show A = _ from congrArg (wirtingerDeriv · z) hfun,
      wirtingerDeriv_sub hf (hh.restrictScalars ℝ), hh.wirtingerDeriv_eq_fderiv,
      fderiv_const_add, L.fderiv]
  set m := max ‖f z - w none - ∑ j, w (some j) * z j‖ ‖A‖
  have hnone : ‖transversalityMap f z none - w none‖ ≤ 2 * m := by
    have : transversalityMap f z none - w none =
        (f z - w none - ∑ j, w (some j) * z j) - A z := by
      -- A complex-linear form is determined by its values on the coordinate vectors.
      have hB (B : EuclideanSpace ℂ σ →L[ℂ] ℂ) (x : EuclideanSpace ℂ σ) :
          B x = ∑ j, x j * B (EuclideanSpace.single j 1) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun σ ℂ).sum_repr x]
        simp [map_sum]
      rw [transversalityMap_none, hA, sub_apply, ← hB, hL]
      ring
    rw [this]
    calc _ ≤ ‖f z - w none - ∑ j, w (some j) * z j‖ + ‖A‖ * ‖z‖ :=
          (norm_sub_le _ _).trans (add_le_add le_rfl (A.le_opNorm z))
      _ ≤ m + m * 1 := add_le_add (le_max_left _ _)
          (mul_le_mul (le_max_right _ _) hz (norm_nonneg _) ((norm_nonneg _).trans
            (le_max_right _ _)))
      _ = 2 * m := by ring
  have hsome (j : σ) : ‖transversalityMap f z (some j) - w (some j)‖ ≤ m := by
    have : transversalityMap f z (some j) - w (some j) = A (EuclideanSpace.single j 1) := by
      rw [transversalityMap_some, hA, sub_apply, hL]
      simp
    rw [this]
    have := A.le_opNorm (EuclideanSpace.single j 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at this
    exact this.trans (le_max_right _ _)
  calc _ ≤ ∑ o, ‖(transversalityMap f z - w) o‖ := PiLp.norm_le_sum_norm _
    _ = ‖transversalityMap f z none - w none‖ +
          ∑ j, ‖transversalityMap f z (some j) - w (some j)‖ := by
        rw [Fintype.sum_option]; simp
    _ ≤ 2 * m + ∑ _j : σ, m := add_le_add hnone (Finset.sum_le_sum fun j _ ↦ hsome j)
    _ = (Fintype.card σ + 2) * m := by simp; ring

/-- The choice of constants: for small `δ`, the bound `C δ / (log (1 / δ)) ^ (p + 1)` is below the
avoidance width `c (δ / K) / (log (K / δ)) ^ p` at the parameter `δ / K`. -/
private theorem exists_pos_forall_mul_div_log_pow_le {c δ₁ K C : ℝ} (hc : 0 < c) (hδ₁ : 0 < δ₁)
    (hK : 1 ≤ K) (p : ℕ) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → δ / K < δ₁ ∧ 0 < Real.log (1 / δ) ∧
      C * (δ / Real.log (1 / δ) ^ (p + 1)) ≤ c * (δ / K) / Real.log (1 / (δ / K)) ^ p := by
  set M := max (max (Real.log K) (C * K * 2 ^ p / c)) 1
  have hK0 : 0 < K := by linarith
  refine ⟨min (K * δ₁) (Real.exp (-M)), by positivity, fun δ hδ hδ₀ ↦ ?_⟩
  have hL : M < Real.log (1 / δ) := by
    have := Real.log_lt_log hδ (hδ₀.trans_le (min_le_right _ _))
    rw [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  set L := Real.log (1 / δ)
  have hL1 : 1 < L := (le_max_right _ _).trans_lt hL
  have hLK : Real.log K < L := ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hL
  have hLC : C * K * 2 ^ p < c * L := by
    have := ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hL
    rw [div_lt_iff₀ hc] at this
    linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hL' : Real.log (1 / (δ / K)) = Real.log K + L := by
    rw [show 1 / (δ / K) = K * (1 / δ) by field_simp, Real.log_mul hK0.ne' (by positivity)]
  refine ⟨(div_lt_iff₀ hK0).2 (by linarith [min_le_left (K * δ₁) (Real.exp (-M))]),
    by linarith, ?_⟩
  rw [hL']
  calc C * (δ / L ^ (p + 1)) = C * K * 2 ^ p * (δ / (K * 2 ^ p * L ^ p * L)) := by
        field_simp; ring
    _ ≤ c * L * (δ / (K * 2 ^ p * L ^ p * L)) :=
        mul_le_mul_of_nonneg_right hLC.le (by positivity)
    _ = c * (δ / K) / (2 * L) ^ p := by field_simp; ring
    _ ≤ c * (δ / K) / (Real.log K + L) ^ p :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith) p)

omit [DecidableEq σ] in
/-- **Local quantitative transversality.** There are an exponent `p > 0`, depending only on
`n = card σ`, and `δ₀ > 0` such that the following holds for `0 < δ < δ₀`, with
`ε = δ / (log (1 / δ)) ^ p`. Let `f : ℂⁿ → ℂ` be `C²` on the ball `B⁺` of radius `11 / 10`, with
`|f| ≤ 1` and `‖Df‖ ≤ 1` there, and with `‖∂̄f‖ ≤ ε` and `‖D(∂̄f(·) b)‖ ≤ ε ‖b‖` for all `b`
there. Then some `w = (w₀, w₁, …, wₙ) ∈ ℂⁿ⁺¹`, indexed by `Option σ` with `w₀ = w none`, has
`‖w‖ ≤ δ` and, for `f_w = f - w₀ - Σ_j w_j z_j`, satisfies `ε ≤ max |f_w z| ‖∂f_w(z)‖` at every
point `z` of the closed unit ball.

Milestone: *Local quantitative transversality for approximately holomorphic functions*. -/
theorem exists_norm_le_max_ge_of_dbar_le :
    ∃ p : ℕ, 0 < p ∧ ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ →
      ∀ f : EuclideanSpace ℂ σ → ℂ,
        (∀ z ∈ ball 0 (11 / 10), ContDiffAt ℝ 2 f z) →
        (∀ z ∈ ball 0 (11 / 10), ‖f z‖ ≤ 1 ∧ ‖fderiv ℝ f z‖ ≤ 1) →
        (∀ z ∈ ball 0 (11 / 10), ‖conjWirtingerDeriv f z‖ ≤ δ / Real.log (1 / δ) ^ p ∧
          ∀ b, ‖fderiv ℝ (fun y ↦ conjWirtingerDeriv f y b) z‖ ≤
            δ / Real.log (1 / δ) ^ p * ‖b‖) →
        ∃ w : EuclideanSpace ℂ (Option σ), ‖w‖ ≤ δ ∧ ∀ z ∈ closedBall 0 1,
          δ / Real.log (1 / δ) ^ p ≤
            max ‖f z - w none - ∑ j, w (some j) * z j‖
              ‖wirtingerDeriv (fun y ↦ f y - w none - ∑ j, w (some j) * y j) z‖ := by
  classical
  set n := Fintype.card σ
  set p₀ := 2 * n * Fintype.card (Option σ)
  obtain ⟨c, hc, δ₁, hδ₁, havoid⟩ :=
    exists_infDist_image_ge (σ := σ) (ι := Option σ) (Fintype.card_option) (R := 11 / 10)
      (by norm_num)
  set K : ℝ := 3 * n + 1
  have hK : 1 ≤ K := by simp only [K]; linarith [n.cast_nonneg (α := ℝ)]
  have hK0 : 0 < K := by linarith
  obtain ⟨δ₀, hδ₀, hsmall⟩ :=
    exists_pos_forall_mul_div_log_pow_le (C := 3 * n + 2) hc hδ₁ hK p₀
  refine ⟨p₀ + 1, Nat.succ_pos _, δ₀, hδ₀, fun δ hδ hδδ₀ f hf hf01 hdbar ↦ ?_⟩
  obtain ⟨hδK, hL, hε⟩ := hsmall δ hδ hδδ₀
  set ε := δ / Real.log (1 / δ) ^ (p₀ + 1)
  set η := c * (δ / K) / Real.log (1 / (δ / K)) ^ p₀
  have hε0 : 0 ≤ ε := by positivity
  set G : EuclideanSpace ℂ σ → EuclideanSpace ℂ (Option σ) :=
    ((K : ℂ)⁻¹) • transversalityMap f
  have hG (z : EuclideanSpace ℂ σ) : G z = ((K : ℂ)⁻¹) • transversalityMap f z :=
    Pi.smul_apply _ _ _
  have hKn : ‖((K : ℂ)⁻¹)‖ = K⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hK0.le]
  have hz2 {z : EuclideanSpace ℂ σ} (hz : z ∈ ball 0 (11 / 10)) : ‖z‖ ≤ 2 := by
    rw [mem_ball_zero_iff] at hz; linarith
  obtain ⟨w', hw', hdist⟩ := havoid (δ / K) (by positivity) hδK G
    (fun z hz ↦ (contDiffAt_transversalityMap (hf z hz)).const_smul ((K : ℂ)⁻¹))
    (fun z hz ↦ by
      rw [hG, norm_smul, hKn,
        inv_mul_le_iff₀ hK0, mul_one]
      exact norm_transversalityMap_le (hf01 z hz).1 (hf01 z hz).2 (hz2 hz))
    (fun z hz j ↦ by
      rw [conjWirtingerDeriv_const_smul, smul_apply, norm_smul, hKn]
      have h := norm_conjWirtingerDeriv_transversalityMap_le (hf z hz) (hdbar z hz).1
        (hdbar z hz).2 (hz2 hz) (EuclideanSpace.single j 1)
      simp only [PiLp.norm_single, norm_one, mul_one] at h
      calc _ ≤ 1 * ((3 * n + 1) * ε) :=
            mul_le_mul (inv_le_one_of_one_le₀ hK) h (norm_nonneg _) zero_le_one
        _ ≤ η := by nlinarith)
  refine ⟨(K : ℂ) • w', ?_, fun z hz ↦ ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hK0.le]
    calc K * ‖w'‖ ≤ K * (δ / K) := mul_le_mul_of_nonneg_left hw' hK0.le
      _ = δ := by field_simp
  have hzB : z ∈ ball (0 : EuclideanSpace ℂ σ) (11 / 10) :=
    closedBall_subset_ball (by norm_num) hz
  have h1 : η ≤ ‖G z - w'‖ := by
    rw [← dist_eq_norm']
    exact hdist.trans (infDist_le_dist_of_mem (Set.mem_image_of_mem G hz))
  have h2 : ‖G z - w'‖ = K⁻¹ * ‖transversalityMap f z - (K : ℂ) • w'‖ := by
    rw [← hKn, ← norm_smul, smul_sub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hK0.ne'),
      one_smul, hG]
  have h3 := norm_transversalityMap_sub_le ((hf z hzB).differentiableAt two_ne_zero)
    (mem_closedBall_zero_iff.1 hz) ((K : ℂ) • w')
  have h4 : ‖G z - w'‖ ≤ ‖transversalityMap f z - (K : ℂ) • w'‖ := by
    rw [h2]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hK)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  set m := max ‖f z - ((K : ℂ) • w') none - ∑ j, ((K : ℂ) • w') (some j) * z j‖
    ‖wirtingerDeriv (fun y ↦ f y - ((K : ℂ) • w') none -
      ∑ j, ((K : ℂ) • w') (some j) * y j) z‖
  have hm : 0 ≤ m := (norm_nonneg _).trans (le_max_left _ _)
  -- The chain is `(3 n + 2) ε ≤ η ≤ ‖G z - w'‖ ≤ ‖transversalityMap f z - K w'‖ ≤ (n + 2) m`
  -- (`hε`, `h1`, `h4`, `h3`), and `(n + 2) ε ≤ (3 n + 2) ε` since `ε ≥ 0`.
  nlinarith [hn, hm, hε0]

end SymplecticGeometry

end
