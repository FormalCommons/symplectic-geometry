/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Gaussian
import SymplecticGeometry.Analysis.Complex.Euclidean.Space

/-!
# Cut-off Gaussians and their uniform jet bounds

The flat model of the peak sections of Donaldson and Auroux. For `k : ℕ` and a point `z` of a
real normed space, `SymplecticGeometry.peakFunction k z` is the complex number
`χ (‖z‖ / k ^ (1 / 6)) * exp (-‖z‖ ^ 2 / 4)`, a Gaussian cut off by the fixed smooth function
`χ = SymplecticGeometry.peakCutoff`, which is `1` on `(-∞, 1]` and `0` on `[2, ∞)`. On the
standard space `StdSpace ι = ℂⁿ`, `SymplecticGeometry.peakFunction_mul k j` is the `j`-th complex
coordinate `z_j`, read through Tau Ceti's `TauCeti.complexToRealEuclidean` (complex linear for
`stdComplexStructure ι` by `stdComplexStructure_complexToRealEuclidean`), times `peakFunction k`.

The power `k ^ (1 / 6)` is the real power `(k : ℝ) ^ (1 / 6 : ℝ)`.

## Main definitions

* `SymplecticGeometry.peakCutoff`: the cut-off `t ↦ smoothTransition (2 - t)`.
* `SymplecticGeometry.peakFunction`: the cut-off Gaussian.
* `SymplecticGeometry.peakFunction_mul`: a complex coordinate times the cut-off Gaussian.

## Main results

* `SymplecticGeometry.contDiff_peakFunction`, `SymplecticGeometry.contDiff_peakFunction_mul`:
  both are smooth.
* `SymplecticGeometry.tsupport_peakFunction_subset`,
  `SymplecticGeometry.tsupport_peakFunction_mul_subset`: for `k ≠ 0`, their supports lie in the
  closed ball of radius `2 * k ^ (1 / 6)`.
* `SymplecticGeometry.peakFunction_eqOn_ball`: on the ball of radius `k ^ (1 / 6)` the cut-off
  Gaussian is the Gaussian `exp (-‖z‖ ^ 2 / 4)`.
* `SymplecticGeometry.exp_neg_one_div_four_le_norm_peakFunction`: its lower bound `exp (-1 / 4)`
  on the closed unit ball, for `k ≥ 1`.
* `SymplecticGeometry.exists_jetNormAt_peakCutoff_norm_div_le`: the jet norms of the cut-offs
  `z ↦ χ (‖z‖ / s)` are bounded uniformly in `s ≥ 1`.
* `SymplecticGeometry.exists_jetNormAt_peakFunction_le`,
  `SymplecticGeometry.exists_jetNormAt_peakFunction_mul_le`: the **uniform Gaussian jet bounds**,
  `jetNormAt ℝ r (peakFunction k) z ≤ C * (1 + ‖z‖) ^ N * exp (-c * ‖z‖ ^ 2)` with `C`, `N` and
  `c > 0` independent of `k` and `z`, and the same for `peakFunction_mul k j`, uniformly in `j`.

## Implementation notes

The radial cut-off `u ↦ χ ‖u‖` is smooth by `ContDiff.comp_norm_of_eventuallyEq_const`, since
`χ` is constant near `0`. The cut-off part `z ↦ χ (‖z‖ / s)` is that function precomposed with
the scaling `z ↦ s⁻¹ • z`. For `s = 0` or `s ≥ 1` the scalar has norm at most `1`, so
`jetNormAt_comp_const_smul_le` bounds its jet norms by those of `u ↦ χ ‖u‖`, uniformly in `s`.
The jet norms of the Gaussian are bounded by `exists_jetNormAt_exp_neg_mul_norm_sq_le`, and
products by `jetNormAt_fun_smul_le`. The complex coordinates are Tau Ceti's
`complexToRealEuclidean` followed by a projection, `TauCeti.complexToRealEuclideanCoord`.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemmas 1–2
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

open Metric

namespace SymplecticGeometry

/-! ### The cut-off -/

/-- The fixed smooth cut-off `χ t = smoothTransition (2 - t)` of the peak functions: it is `1` for
`t ≤ 1`, `0` for `t ≥ 2`, and takes values in `[0, 1]`. -/
noncomputable def peakCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (2 - t)

theorem peakCutoff_def (t : ℝ) : peakCutoff t = Real.smoothTransition (2 - t) :=
  (rfl)

theorem contDiff_peakCutoff {n : ℕ∞} : ContDiff ℝ n peakCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem peakCutoff_of_le_one {t : ℝ} (ht : t ≤ 1) : peakCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem peakCutoff_of_two_le {t : ℝ} (ht : 2 ≤ t) : peakCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem peakCutoff_nonneg (t : ℝ) : 0 ≤ peakCutoff t :=
  Real.smoothTransition.nonneg _

theorem peakCutoff_le_one (t : ℝ) : peakCutoff t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem peakCutoff_ne_zero_iff {t : ℝ} : peakCutoff t ≠ 0 ↔ t < 2 := by
  rw [peakCutoff_def, Ne, Real.smoothTransition.zero_iff_nonpos, not_le, sub_pos]

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial cut-off `u ↦ χ ‖u‖` is smooth, since `χ` is constant near `0`. -/
theorem contDiff_peakCutoff_norm {n : ℕ∞} : ContDiff ℝ n fun u : E ↦ peakCutoff ‖u‖ :=
  contDiff_peakCutoff.comp_norm_of_eventuallyEq_const <| by
    filter_upwards [Iio_mem_nhds one_pos] with t ht
    rw [peakCutoff_of_le_one ht.le, peakCutoff_of_le_one zero_le_one]

/-- The radial cut-off `u ↦ χ ‖u‖` vanishes outside the closed ball of radius `2`. -/
theorem hasCompactSupport_peakCutoff_norm [FiniteDimensional ℝ E] :
    HasCompactSupport fun u : E ↦ peakCutoff ‖u‖ :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) 2) fun u hu ↦
    peakCutoff_of_two_le (le_of_lt (by simpa using hu))

/-- The scaled cut-off `z ↦ χ (‖z‖ / s)` is the radial cut-off precomposed with `z ↦ s⁻¹ • z`. -/
theorem peakCutoff_norm_div {s : ℝ} (hs : 0 ≤ s) (z : E) :
    peakCutoff (‖z‖ / s) = peakCutoff ‖s⁻¹ • z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hs, div_eq_inv_mul]

/-- The scaled cut-off `z ↦ χ (‖z‖ / s)` is smooth, for `s ≥ 0`. -/
theorem contDiff_peakCutoff_norm_div {n : ℕ∞} {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ n fun z : E ↦ peakCutoff (‖z‖ / s) := by
  simp_rw [peakCutoff_norm_div hs]
  exact contDiff_peakCutoff_norm.comp (contDiff_const_smul _)

/-- The jet norms of the scaled cut-offs `z ↦ χ (‖z‖ / s)` are bounded uniformly in `s`, for `s`
equal to `0` or at least `1`. -/
theorem exists_jetNormAt_peakCutoff_norm_div_le [FiniteDimensional ℝ E] (r : ℕ) :
    ∃ C, ∀ s : ℝ, (s = 0 ∨ 1 ≤ s) → ∀ z : E,
      jetNormAt ℝ r (fun z : E ↦ peakCutoff (‖z‖ / s)) z ≤ C := by
  obtain ⟨C, -, hC⟩ :=
    hasCompactSupport_peakCutoff_norm.exists_bound_iteratedFDeriv
      (contDiff_peakCutoff_norm (E := E)) r
  refine ⟨(r + 1) * C, fun s hs z ↦ ?_⟩
  have hs0 : 0 ≤ s := by rcases hs with rfl | hs <;> linarith
  have hs1 : ‖s⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg hs0]
    rcases hs with rfl | hs
    · simp
    · exact inv_le_one_of_one_le₀ hs
  simp_rw [peakCutoff_norm_div hs0]
  refine (jetNormAt_comp_const_smul_le r (fun u : E ↦ peakCutoff ‖u‖) hs1 z).trans ?_
  rw [jetNormAt_def]
  calc ∑ j ∈ Finset.range (r + 1), ‖iteratedFDeriv ℝ j (fun u : E ↦ peakCutoff ‖u‖) (s⁻¹ • z)‖
      ≤ ∑ _j ∈ Finset.range (r + 1), C :=
        Finset.sum_le_sum fun j hj ↦ hC j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) _
    _ = (r + 1) * C := by simp

end Radial

/-! ### The cut-off Gaussians -/

variable {E : Type*} [NormedAddCommGroup E]

/-- The **cut-off Gaussian** `χ (‖z‖ / k ^ (1 / 6)) * exp (-‖z‖ ^ 2 / 4)`, as a complex number,
with `χ = peakCutoff` and the real power `k ^ (1 / 6)`. -/
noncomputable def peakFunction (k : ℕ) (z : E) : ℂ :=
  (peakCutoff (‖z‖ / (k : ℝ) ^ (1 / 6 : ℝ)) * Real.exp (-‖z‖ ^ 2 / 4) : ℝ)

theorem peakFunction_def (k : ℕ) (z : E) :
    peakFunction k z =
      (peakCutoff (‖z‖ / (k : ℝ) ^ (1 / 6 : ℝ)) * Real.exp (-‖z‖ ^ 2 / 4) : ℝ) :=
  (rfl)

/-- The cut-off Gaussian is the inclusion `ℝ → ℂ` of the product of the real functions
`z ↦ χ (‖z‖ / k ^ (1 / 6))` and `z ↦ exp (-‖z‖ ^ 2 / 4)`. -/
theorem peakFunction_eq_ofRealCLM_comp (k : ℕ) :
    peakFunction (E := E) k = Complex.ofRealCLM ∘
      fun z : E ↦ peakCutoff (‖z‖ / (k : ℝ) ^ (1 / 6 : ℝ)) • Real.exp (-‖z‖ ^ 2 / 4) := by
  ext z
  rw [peakFunction_def, Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]

theorem contDiff_peakFunction [InnerProductSpace ℝ E] {n : ℕ∞} (k : ℕ) :
    ContDiff ℝ n (peakFunction (E := E) k) := by
  rw [peakFunction_eq_ofRealCLM_comp]
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_peakCutoff_norm_div (by positivity)).smul
    (Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 4)))

/-- The cut-off Gaussian is the Gaussian `exp (-‖z‖ ^ 2 / 4)` on the ball of radius
`k ^ (1 / 6)`. -/
theorem peakFunction_eqOn_ball (k : ℕ) :
    Set.EqOn (peakFunction (E := E) k) (fun z ↦ (Real.exp (-‖z‖ ^ 2 / 4) : ℂ))
      (ball 0 ((k : ℝ) ^ (1 / 6 : ℝ))) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz
  have hs : 0 < (k : ℝ) ^ (1 / 6 : ℝ) := (norm_nonneg z).trans_lt hz
  rw [peakFunction_def, peakCutoff_of_le_one ((div_le_one hs).2 hz.le), one_mul]

/-- For `k ≥ 1`, the cut-off Gaussian has modulus at least `exp (-1 / 4)` on the closed unit
ball. -/
theorem exp_neg_one_div_four_le_norm_peakFunction {k : ℕ} (hk : 1 ≤ k) {z : E} (hz : ‖z‖ ≤ 1) :
    Real.exp (-1 / 4) ≤ ‖peakFunction k z‖ := by
  have hs : 1 ≤ (k : ℝ) ^ (1 / 6 : ℝ) := Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hs0 : 0 < (k : ℝ) ^ (1 / 6 : ℝ) := zero_lt_one.trans_le hs
  rw [peakFunction_def, peakCutoff_of_le_one ((div_le_one hs0).2 (hz.trans hs)), one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  gcongr
  nlinarith [norm_nonneg z]

/-- The support of the cut-off Gaussian lies in the closed ball of radius `2 * k ^ (1 / 6)`, for
`k ≠ 0`. -/
theorem tsupport_peakFunction_subset {k : ℕ} (hk : k ≠ 0) :
    tsupport (peakFunction (E := E) k) ⊆ closedBall 0 (2 * (k : ℝ) ^ (1 / 6 : ℝ)) := by
  refine closure_minimal (fun z hz ↦ ?_) isClosed_closedBall
  have hs : 0 < (k : ℝ) ^ (1 / 6 : ℝ) := by positivity
  rw [Function.mem_support, peakFunction_def, Complex.ofReal_ne_zero] at hz
  have h := peakCutoff_ne_zero_iff.1 (left_ne_zero_of_mul hz)
  rw [mem_closedBall_zero_iff]
  exact ((div_lt_iff₀ hs).1 h).le

/-- The **uniform Gaussian jet bound** for the cut-off Gaussians: for every order `r` there are
`C`, `N` and `c > 0` such that `jetNormAt ℝ r (peakFunction k) z ≤ C * (1 + ‖z‖) ^ N *
exp (-c * ‖z‖ ^ 2)` for all `k` and `z`. -/
theorem exists_jetNormAt_peakFunction_le [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℕ) :
    ∃ C N, ∃ c > 0, ∀ (k : ℕ) (z : E),
      jetNormAt ℝ r (peakFunction k) z ≤ C * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2) := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_peakCutoff_norm_div_le (E := E) r
  obtain ⟨B, hB⟩ := exists_jetNormAt_exp_neg_mul_norm_sq_le (E := E) r (a := 1 / 4) (by norm_num)
  have hG : (fun z : E ↦ Real.exp (-(1 / 4 * ‖z‖ ^ 2))) = fun z ↦ Real.exp (-‖z‖ ^ 2 / 4) := by
    ext z
    ring_nf
  have hG' (z : E) : Real.exp (-(1 / 4 * ‖z‖ ^ 2) / 2) = Real.exp (-‖z‖ ^ 2 / 8) := by
    ring_nf
  simp_rw [hG, hG'] at hB
  refine ⟨2 ^ r * A * B, 0, 1 / 8, by norm_num, fun k z ↦ ?_⟩
  set s := (k : ℝ) ^ (1 / 6 : ℝ)
  have hs : s = 0 ∨ 1 ≤ s := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · left; simp [s]
    · right; exact Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hχ : ContDiff ℝ r fun z : E ↦ peakCutoff (‖z‖ / s) :=
    contDiff_peakCutoff_norm_div (by positivity)
  have hg : ContDiff ℝ r fun z : E ↦ Real.exp (-‖z‖ ^ 2 / 4) :=
    Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 4)
  rw [peakFunction_eq_ofRealCLM_comp]
  refine (jetNormAt_comp_left_le _ (hχ.smul hg).contDiffAt).trans ?_
  rw [Complex.ofRealCLM_norm, one_mul]
  refine (jetNormAt_fun_smul_le hχ.contDiffAt hg.contDiffAt).trans ?_
  calc (2 : ℝ) ^ r * jetNormAt ℝ r (fun z : E ↦ peakCutoff (‖z‖ / s)) z *
        jetNormAt ℝ r (fun z : E ↦ Real.exp (-‖z‖ ^ 2 / 4)) z
      ≤ 2 ^ r * A * (B * Real.exp (-‖z‖ ^ 2 / 8)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hA s hs z) (by positivity)) (hB z)
          (jetNormAt_nonneg _ _ _)
          (mul_nonneg (by positivity) ((jetNormAt_nonneg _ _ _).trans (hA s hs z)))
    _ = _ := by ring_nf

/-! ### A complex coordinate times the cut-off Gaussian -/

variable {ι : Type*} [Fintype ι]

/-- The cut-off Gaussian times the `j`-th complex coordinate `z_j` of `StdSpace ι`, the
coordinate `j` of `(complexToRealEuclidean ι).symm z`, which is complex linear for
`stdComplexStructure ι`. -/
noncomputable def peakFunction_mul (k : ℕ) (j : ι) (z : StdSpace ι) : ℂ :=
  (TauCeti.complexToRealEuclidean ι).symm z j * peakFunction k z

theorem peakFunction_mul_def (k : ℕ) (j : ι) (z : StdSpace ι) :
    peakFunction_mul k j z = (TauCeti.complexToRealEuclidean ι).symm z j * peakFunction k z :=
  (rfl)

private theorem peakFunction_mul_eq (k : ℕ) (j : ι) :
    peakFunction_mul k j =
      fun z ↦ TauCeti.complexToRealEuclideanCoord ι j z • peakFunction k z := by
  ext z
  rw [peakFunction_mul_def, TauCeti.complexToRealEuclideanCoord_apply, smul_eq_mul]

theorem contDiff_peakFunction_mul {n : ℕ∞} (k : ℕ) (j : ι) :
    ContDiff ℝ n (peakFunction_mul k j) := by
  rw [peakFunction_mul_eq]
  exact (TauCeti.complexToRealEuclideanCoord ι j).contDiff.smul (contDiff_peakFunction k)

/-- The support of `peakFunction_mul k j` lies in the closed ball of radius `2 * k ^ (1 / 6)`, for
`k ≠ 0`. -/
theorem tsupport_peakFunction_mul_subset {k : ℕ} (hk : k ≠ 0) (j : ι) :
    tsupport (peakFunction_mul k j) ⊆ closedBall 0 (2 * (k : ℝ) ^ (1 / 6 : ℝ)) := by
  have : peakFunction_mul k j =
      (fun z ↦ (TauCeti.complexToRealEuclidean ι).symm z j) * peakFunction k := by
    ext z
    rw [peakFunction_mul_def, Pi.mul_apply]
  rw [this]
  exact tsupport_mul_subset_right.trans (tsupport_peakFunction_subset hk)

/-- The **uniform Gaussian jet bound** for the coordinates times the cut-off Gaussians: for every
order `r` there are `C`, `N` and `c > 0` such that
`jetNormAt ℝ r (peakFunction_mul k j) z ≤ C * (1 + ‖z‖) ^ N * exp (-c * ‖z‖ ^ 2)` for all `k`,
`j` and `z`. -/
theorem exists_jetNormAt_peakFunction_mul_le (r : ℕ) :
    ∃ C N, ∃ c > 0, ∀ (k : ℕ) (j : ι) (z : StdSpace ι),
      jetNormAt ℝ r (peakFunction_mul k j) z ≤ C * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2) := by
  obtain ⟨C, N, c, hc, h⟩ := exists_jetNormAt_peakFunction_le (E := StdSpace ι) r
  refine ⟨2 ^ r * C, N + 1, c, hc, fun k j z ↦ ?_⟩
  set L := TauCeti.complexToRealEuclideanCoord ι j
  have hL : jetNormAt ℝ r L z ≤ 1 + ‖z‖ := by
    refine (jetNormAt_continuousLinearMap_le _ r z).trans ?_
    have := TauCeti.norm_complexToRealEuclidean_symm_apply_le z j
    have := TauCeti.norm_complexToRealEuclideanCoord_le (ι := ι) j
    simp only [L, TauCeti.complexToRealEuclideanCoord_apply]
    linarith
  rw [peakFunction_mul_eq]
  refine (jetNormAt_fun_smul_le L.contDiff.contDiffAt
    (contDiff_peakFunction k).contDiffAt).trans ?_
  calc (2 : ℝ) ^ r * jetNormAt ℝ r L z * jetNormAt ℝ r (peakFunction k) z
      ≤ 2 ^ r * (1 + ‖z‖) * (C * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) (h k z)
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = _ := by ring

end SymplecticGeometry

end
