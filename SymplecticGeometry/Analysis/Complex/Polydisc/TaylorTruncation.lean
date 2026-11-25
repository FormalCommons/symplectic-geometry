/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
public import TauCeti.Analysis.Complex.PowerSeries.Polydisc
public import TauCeti.Analysis.Complex.PowerSeries.TaylorRemainder
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Taylor truncation on polydiscs

On `ι → ℂ`, for a finite type `ι`, the balls of the sup norm are the polydiscs with equal radii.
This file shows that a function holomorphic on such a polydisc is, on a smaller concentric
polydisc, uniformly close to its Taylor polynomials, with an error that decays geometrically in
the degree.

## Main definitions and results

* `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: a function holomorphic on the polydisc
  `ball c R` has a power series about `c` on `ball c r` for every `0 < r < R`. The power series
  comes from the multivariate Cauchy expansion of Tau Ceti
  (`ContinuousOn.hasSum_torusIntegral_cauchyCoeff`, with the coefficient bound
  `TauCeti.norm_torusIntegral_cauchyCoeff_le`).
* `SymplecticGeometry.taylorPolynomial f c d`: the Taylor polynomial of `f` at `c` with the terms
  of total degree less than `d`, as a multivariate polynomial in the variables `z - c`, whose
  coefficients are Tau Ceti's `TauCeti.mvTaylorCoeff`. It has total degree less than `d`
  (`SymplecticGeometry.totalDegree_taylorPolynomial_lt`), and its value is the partial sum of
  any power series of `f` at `c` (`SymplecticGeometry.eval_taylorPolynomial`).
* `SymplecticGeometry.norm_sub_taylorPolynomial_le_of_mem_ball`: if `‖f‖ ≤ M` on `ball c R`, then
  `‖f z - P (z - c)‖ ≤ (1 + d) * M * (‖z - c‖ / R) ^ d` on `ball c R`, for `P` the Taylor
  polynomial with the terms of degree less than `d`. This is Tau Ceti's remainder bound
  `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` on every smaller polydisc, in the limit.
* `SymplecticGeometry.norm_sub_taylorPolynomial_le`: on the polydisc of half the radius, the error
  is at most `(1 + d) * M / 2 ^ d`.

The proof of `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt` adapts those of Tau Ceti's
`DifferentiableOn.exists_differentiable_norm_sub_lt_of_pi` and of the private lemma
`TauCeti.exists_differentiable_norm_sub_lt_of_fin` behind it
(`TauCeti/Analysis/Complex/PowerSeries/Polydisc.lean`): the same Cauchy expansion on a closed
polydisc of intermediate radius, and the same transport from `Fin n → ℂ` to `ι → ℂ`, here
feeding `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` instead of a uniform limit.

These are the polynomial approximations through which Auroux's avoidance estimate compares the
image of an approximately holomorphic map with that of a polynomial map.

## References

* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Finset Metric MeasureTheory Real Topology
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The case `ι = Fin n` of `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`: the power
series is the multivariate Cauchy expansion on a closed polydisc of intermediate radius. -/
private theorem DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt_of_fin [CompleteSpace E]
    {n : ℕ} {h : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : ℝ} (hh : DifferentiableOn ℂ h (ball c R))
    {r : ℝ≥0} (hr : 0 < r) (hrR : (r : ℝ) < R) :
    ∃ p : FormalMultilinearSeries ℂ (Fin n → ℂ) E, HasFPowerSeriesOnBall h p c r := by
  -- Expand on the closed polydisc of radius `s`, `r < s < R`, which lies in `ball c R`.
  set s : ℝ := (r + R) / 2
  have hrs : (r : ℝ) < s := by simp only [s]; linarith
  have hs : 0 < s := (NNReal.coe_pos.2 hr).trans hrs
  have hsub : (Set.univ.pi fun i ↦ closedBall (c i) s) ⊆ ball c R := fun z hz ↦
    mem_ball.2 <| ((dist_pi_le_iff hs.le).2 fun i ↦ hz i trivial).trans_lt
      (by simp only [s]; linarith)
  have hcont : ContinuousOn h (Set.univ.pi fun i ↦ closedBall (c i) s) :=
    hh.continuousOn.mono hsub
  obtain ⟨M, hM⟩ :=
    (isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) s).exists_bound_of_continuousOn hcont
  have hd : ∀ z ∈ Set.univ.pi (fun i ↦ closedBall (c i) s), ∀ i, z i ∈ ball (c i) s →
      DifferentiableAt ℂ (fun x ↦ h (Function.update z i x)) (z i) := fun z hz i _ ↦ by
    refine DifferentiableAt.comp (z i) ?_ (hasFDerivAt_update z (z i)).differentiableAt
    rw [Function.update_eq_self i z]
    exact hh.differentiableAt (isOpen_ball.mem_nhds (hsub hz))
  have hq : Summable (fun α : Fin n → ℕ ↦ ∏ i, ((r : ℝ) / s) ^ α i) :=
    (TauCeti.hasSum_prod_geometric_of_norm_lt_one (r := fun _ ↦ (r : ℝ) / s) fun _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_lt_one hs).2 hrs).summable
  refine (TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum (f := h) (x := c)
    (c := fun α ↦ (2 * π * I : ℂ)⁻¹ ^ n •
      ∯ z in T(c, fun _ ↦ s), (∏ i, (z i - c i) ^ (α i + 1))⁻¹ • h z) hr ?_
    fun y hy ↦ ?_).imp fun _ hp ↦ hp.1
  · refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun α ↦ ?_) (hq.mul_left M)
    have hb := TauCeti.norm_torusIntegral_cauchyCoeff_le (f := h) (c := c) (M := M)
      (fun _ ↦ hs) (fun z hz ↦ hM z fun i _ ↦ sphere_subset_closedBall (hz i trivial)) α
    calc _ ≤ (M * ∏ i, s⁻¹ ^ α i) * (r : ℝ) ^ ∑ i, α i := by gcongr
      _ = M * ∏ i, ((r : ℝ) / s) ^ α i := by
        rw [mul_assoc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        simp only [← mul_pow, div_eq_mul_inv, mul_comm]
  · exact hcont.hasSum_torusIntegral_cauchyCoeff hd fun i ↦
      (norm_le_pi_norm y i).trans_lt (hy.trans hrs)

/-- A function holomorphic on the polydisc `ball c R` of `ι → ℂ`, a ball for the sup norm, has
a power series about `c` on the polydisc `ball c r` for every `0 < r < R`. -/
theorem DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt [CompleteSpace E] {ι : Type*}
    [Fintype ι] {h : (ι → ℂ) → E} {c : ι → ℂ} {R : ℝ} (hh : DifferentiableOn ℂ h (ball c R))
    {r : ℝ≥0} (hr : 0 < r) (hrR : (r : ℝ) < R) :
    ∃ p : FormalMultilinearSeries ℂ (ι → ℂ) E, HasFPowerSeriesOnBall h p c r := by
  -- Transport to `Fin n → ℂ` along the complex-linear isometry `L x = x ∘ e.symm` given by an
  -- enumeration `e` of `ι`.
  let e := Fintype.equivFin ι
  let L := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (Fintype.card ι) ↦ ℂ) e
  have hL (x y : ι → ℂ) : dist (L x) (L y) = dist x y :=
    (IsometryEquiv.piCongrLeft (Y := fun _ : Fin (Fintype.card ι) ↦ ℂ) e).dist_eq x y
  obtain ⟨p, hp⟩ := DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt_of_fin (c := L c)
    (h := h ∘ L.symm) (hh.comp L.symm.differentiable.differentiableOn fun y hy ↦ by
      rwa [mem_ball, ← hL, L.apply_symm_apply]) hr hrR
  set u : (ι → ℂ) →L[ℂ] Fin (Fintype.card ι) → ℂ := ↑L with hu
  have hLn (x : ι → ℂ) : ‖u x‖ = ‖x‖ := by
    simpa [hu, ContinuousLinearEquiv.coe_coe] using hL x 0
  have hu1 : ‖u‖ₑ ≤ 1 := u.opENorm_le_bound fun x ↦ by
    rw [one_mul, ← ofReal_norm, ← ofReal_norm, hLn]
  have hle : (r : ℝ≥0∞) ≤ r / ‖u‖ₑ :=
    (ENNReal.le_div_iff_mul_le (Or.inr (ENNReal.coe_ne_zero.2 hr.ne'))
      (Or.inr ENNReal.coe_ne_top)).2 (mul_le_of_le_one_right zero_le hu1)
  rw [← L.coe_coe, ← hu] at hp
  refine ⟨_, ((hp.compContinuousLinearMap (x := c)).mono (ENNReal.coe_pos.2 hr) hle).congr
    fun y _ ↦ ?_⟩
  rw [Function.comp_apply, Function.comp_apply, hu, L.coe_coe, L.symm_apply_apply]

namespace SymplecticGeometry

section TaylorPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]

open Classical in
/-- The **Taylor polynomial** of `f : (ι → 𝕜) → 𝕜` at `c` with the terms of total degree less
than `d`: the multivariate polynomial `∑_{|α| < d} a_α X^α` whose coefficients `a_α` are the
Taylor coefficients `TauCeti.mvTaylorCoeff f c α` of `f` at `c`. It is a polynomial in the
variables `z - c`. -/
noncomputable def taylorPolynomial (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) : MvPolynomial ι 𝕜 :=
  ∑ k ∈ range d, ∑ α ∈ univ.piAntidiag k,
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (TauCeti.mvTaylorCoeff f c α)

open Classical in
theorem taylorPolynomial_def (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) :
    taylorPolynomial f c d = ∑ k ∈ range d, ∑ α ∈ univ.piAntidiag k,
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (TauCeti.mvTaylorCoeff f c α) :=
  (rfl)

@[simp]
theorem taylorPolynomial_zero (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) : taylorPolynomial f c 0 = 0 := by
  simp [taylorPolynomial_def]

/-- The coefficient of the monomial of exponent `s` in the Taylor polynomial of degree less than
`d` is the Taylor coefficient of index `s` if `s` has total degree less than `d`, and `0`
otherwise. -/
theorem coeff_taylorPolynomial (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) (s : ι →₀ ℕ) :
    (taylorPolynomial f c d).coeff s =
      if s.degree < d then TauCeti.mvTaylorCoeff f c s else 0 := by
  classical
  conv_lhs => rw [← Finsupp.equivFunOnFinite_symm_coe s]
  simp only [taylorPolynomial_def, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Equiv.apply_eq_iff_eq, Finset.sum_ite_eq', mem_piAntidiag,
    mem_univ, implies_true, and_true, Finsupp.degree_eq_sum, eq_comm (a := ∑ i, s i),
    mem_range]

/-- The Taylor polynomial with the terms of degree less than `d` has total degree less than
`d`. -/
theorem totalDegree_taylorPolynomial_lt (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) {d : ℕ} (hd : 0 < d) :
    (taylorPolynomial f c d).totalDegree < d := by
  classical
  refine Nat.lt_of_le_pred hd (MvPolynomial.totalDegree_finsetSum_le fun k hk ↦
    MvPolynomial.totalDegree_finsetSum_le fun α hα ↦ ?_)
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
  simp only [Finsupp.coe_equivFunOnFinite_symm, id]
  rw [(mem_piAntidiag.1 hα).1]
  exact Nat.le_pred_of_lt (mem_range.1 hk)

/-- The value of the Taylor polynomial of degree less than `d` at `y` is the partial sum of
order `d` at `y` of every power series of `f` at `c`. -/
theorem eval_taylorPolynomial {f : (ι → 𝕜) → 𝕜} {c : ι → 𝕜}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) 𝕜} (hp : HasFPowerSeriesAt f p c) (d : ℕ)
    (y : ι → 𝕜) : MvPolynomial.eval y (taylorPolynomial f c d) = p.partialSum d y := by
  classical
  simp only [taylorPolynomial_def, map_sum, MvPolynomial.eval_monomial,
    p.partialSum_eq_sum_mvCoeff, hp.mvTaylorCoeff_eq, smul_eq_mul, mul_comm,
    Finsupp.prod_pow, Finsupp.coe_equivFunOnFinite_symm]

end TaylorPolynomial

variable {ι : Type*} [Fintype ι]

/-- **Taylor truncation on a polydisc.** If `f` is holomorphic on the polydisc `ball c R` of
`ι → ℂ`, a ball for the sup norm, and `‖f‖ ≤ M` there, then its Taylor polynomial at `c` with
the terms of degree less than `d` approximates it on `ball c R`:
`‖f z - P (z - c)‖ ≤ (1 + d) * M * (‖z - c‖ / R) ^ d`. -/
theorem norm_sub_taylorPolynomial_le_of_mem_ball {f : (ι → ℂ) → ℂ} {c : ι → ℂ} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (d : ℕ)
    {z : ι → ℂ} (hz : z ∈ ball c R) :
    ‖f z - MvPolynomial.eval (z - c) (taylorPolynomial f c d)‖ ≤
      (1 + d) * M * (‖z - c‖ / R) ^ d := by
  rw [mem_ball, dist_eq_norm] at hz
  -- The bound holds with every radius `r` between `‖z - c‖` and `R` in place of `R`.
  have hr : ∀ r : ℝ, ‖z - c‖ < r → r < R →
      ‖f z - MvPolynomial.eval (z - c) (taylorPolynomial f c d)‖ ≤
        (1 + d) * M * (‖z - c‖ / r) ^ d := by
    intro r hzr hrR
    have hr0 : 0 < r := (norm_nonneg _).trans_lt hzr
    obtain ⟨p, hp⟩ := hf.exists_hasFPowerSeriesOnBall_of_lt (r := r.toNNReal)
      (Real.toNNReal_pos.2 hr0) (by rwa [Real.coe_toNNReal _ hr0.le])
    have h := hp.norm_add_sub_partialSum_le (M := M) (fun y hy ↦ hM y <|
        ball_subset_ball (by rw [Real.coe_toNNReal _ hr0.le]; exact hrR.le) hy) d
      (z := z - c) (by rwa [Real.coe_toNNReal _ hr0.le])
    rwa [add_sub_cancel, Real.coe_toNNReal _ hr0.le, ← eval_taylorPolynomial hp.hasFPowerSeriesAt]
      at h
  have hR0 : R ≠ 0 := ((norm_nonneg _).trans_lt hz).ne'
  refine ge_of_tendsto (x := 𝓝[<] R) (f := fun r ↦ (1 + d) * M * (‖z - c‖ / r) ^ d) ?_ ?_
  · exact (tendsto_const_nhds.mul ((tendsto_const_nhds.div tendsto_id hR0).pow d)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT hz] with r hr' using hr r hr'.1 hr'.2

/-- **Taylor truncation on a polydisc**, on the polydisc of half the radius. If `f` is
holomorphic on the polydisc `ball c R` of `ι → ℂ`, a ball for the sup norm, and `‖f‖ ≤ M` there,
then on `closedBall c (R / 2)` it differs from its Taylor polynomial at `c` with the terms of
degree less than `d` (of total degree less than `d` when `0 < d`, by
`totalDegree_taylorPolynomial_lt`), by at most `(1 + d) * M / 2 ^ d`. -/
theorem norm_sub_taylorPolynomial_le {f : (ι → ℂ) → ℂ} {c : ι → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (d : ℕ)
    {z : ι → ℂ} (hz : z ∈ closedBall c (R / 2)) :
    ‖f z - MvPolynomial.eval (z - c) (taylorPolynomial f c d)‖ ≤ (1 + d) * M / 2 ^ d := by
  have hzR : z ∈ ball c R := closedBall_subset_ball (by linarith) hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzR)
  refine (norm_sub_taylorPolynomial_le_of_mem_ball hf hM d hzR).trans ?_
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [div_eq_mul_inv _ ((2 : ℝ) ^ d), ← inv_pow]
  gcongr
  rw [div_le_iff₀ hR]
  linarith

end SymplecticGeometry

end
