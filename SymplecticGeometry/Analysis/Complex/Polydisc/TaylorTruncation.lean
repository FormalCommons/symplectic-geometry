/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
public import TauCeti.Analysis.Complex.PowerSeries.TaylorRemainder
public import Mathlib.RingTheory.MvPowerSeries.Trunc
import SymplecticGeometry.Analysis.Complex.Polydisc.PowerSeries
import SymplecticGeometry.RingTheory.MvPowerSeries.Trunc

/-!
# Taylor truncation on polydiscs

On `ι → ℂ`, for a finite type `ι`, the balls of the sup norm are the polydiscs with equal radii.
This file shows that a function holomorphic on such a polydisc is, on a smaller concentric
polydisc, uniformly close to its Taylor polynomials, with an error that decays geometrically in
the degree.

## Main definitions and results

* `SymplecticGeometry.mvTaylorSeries f c`: the formal multivariate power series whose
  coefficients are Tau Ceti's Taylor coefficients `TauCeti.mvTaylorCoeff f c`.
* `SymplecticGeometry.taylorPolynomial f c d`: its truncation `MvPowerSeries.truncTotal d` to
  the terms of total degree less than `d`, a multivariate polynomial in the variables `z - c`.
  It has total degree at most `d - 1` (`SymplecticGeometry.totalDegree_taylorPolynomial_le`),
  and its value is the partial sum of any power series of `f` at `c`
  (`SymplecticGeometry.eval_taylorPolynomial`).
* `SymplecticGeometry.norm_sub_taylorPolynomial_le_of_mem_ball`: if `‖f‖ ≤ M` on `ball c R`, then
  `‖f z - P (z - c)‖ ≤ (1 + d) * M * (‖z - c‖ / R) ^ d` on `ball c R`, for `P` the Taylor
  polynomial with the terms of degree less than `d`. This is Tau Ceti's remainder bound
  `HasFPowerSeriesOnBall.norm_add_sub_partialSum_le` on every smaller polydisc, with the power
  series of `DifferentiableOn.exists_hasFPowerSeriesOnBall_of_lt`, in the limit.
* `SymplecticGeometry.norm_sub_taylorPolynomial_le`: on the polydisc of half the radius, the error
  is at most `(1 + d) * M / 2 ^ d`.

These are the polynomial approximations through which Auroux's avoidance estimate compares the
image of an approximately holomorphic map with that of a polynomial map.

## References

* [D. Auroux, *Symplectic 4-manifolds as branched coverings of ℂℙ²*][Auroux2000], Proposition 2.
-/

public section

open Filter Metric Topology

namespace SymplecticGeometry

section TaylorPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]

/-- The **multivariate Taylor series** of `f : (ι → 𝕜) → 𝕜` at `c`: the formal power series
`∑_α a_α X^α` whose coefficients `a_α` are the Taylor coefficients `TauCeti.mvTaylorCoeff f c α`
of `f` at `c`. -/
noncomputable def mvTaylorSeries (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) : MvPowerSeries ι 𝕜 :=
  fun s ↦ TauCeti.mvTaylorCoeff f c s

@[simp]
theorem coeff_mvTaylorSeries (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (s : ι →₀ ℕ) :
    (mvTaylorSeries f c).coeff s = TauCeti.mvTaylorCoeff f c s :=
  (rfl)

/-- The **Taylor polynomial** of `f : (ι → 𝕜) → 𝕜` at `c` with the terms of total degree less
than `d`: the truncation of the Taylor series `mvTaylorSeries f c` to those terms. It is a
polynomial in the variables `z - c`. -/
noncomputable def taylorPolynomial (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) : MvPolynomial ι 𝕜 :=
  (mvTaylorSeries f c).truncTotal d

theorem taylorPolynomial_def (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) :
    taylorPolynomial f c d = (mvTaylorSeries f c).truncTotal d :=
  (rfl)

@[simp]
theorem taylorPolynomial_zero (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) : taylorPolynomial f c 0 = 0 := by
  rw [taylorPolynomial_def, MvPowerSeries.truncTotal_zero]

/-- The Taylor polynomial with the terms of total degree less than `d` has total degree at most
`d - 1`. -/
theorem totalDegree_taylorPolynomial_le (f : (ι → 𝕜) → 𝕜) (c : ι → 𝕜) (d : ℕ) :
    (taylorPolynomial f c d).totalDegree ≤ d - 1 := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  · exact Nat.le_sub_one_of_lt (MvPowerSeries.totalDegree_truncTotal_lt _ hd.ne')

/-- The value of the Taylor polynomial of degree less than `d` at `y` is the partial sum of
order `d` at `y` of every power series of `f` at `c`. -/
theorem eval_taylorPolynomial {f : (ι → 𝕜) → 𝕜} {c : ι → 𝕜}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) 𝕜} (hp : HasFPowerSeriesAt f p c) (d : ℕ)
    (y : ι → 𝕜) : MvPolynomial.eval y (taylorPolynomial f c d) = p.partialSum d y := by
  classical
  simp only [taylorPolynomial_def, MvPowerSeries.truncTotal_eq_sum_monomial, coeff_mvTaylorSeries,
    map_sum, MvPolynomial.eval_monomial, p.partialSum_eq_sum_mvCoeff, hp.mvTaylorCoeff_eq,
    smul_eq_mul, mul_comm, Finsupp.prod_pow, Finsupp.coe_equivFunOnFinite_symm]

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
degree less than `d` (of total degree at most `d - 1`, by
`SymplecticGeometry.totalDegree_taylorPolynomial_le`), by at most `(1 + d) * M / 2 ^ d`. -/
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
