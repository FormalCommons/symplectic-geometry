/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ModelDbar
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Analysis.Complex.OperatorNorm
import SymplecticGeometry.Analysis.Calculus.FDeriv.Radial
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Gaussian
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# Cut-off Gaussians, their uniform jet bounds and their model `∂̄`

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
* `SymplecticGeometry.flatDbar`: the flat `∂̄` of a complex function on `StdSpace ι`, the
  complex-antilinear part for `J₀` of `df_z`, through
  `TauCeti.complexAntilinearPartContinuousLinearMap`.
* `SymplecticGeometry.modelDbar`: the model `∂̄` of a complex function on `StdSpace ι`, the
  complex-antilinear part for `J₀` of `v ↦ df_z v - (ω₀(z, v) / 2) • (i f(z))`.

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
* `SymplecticGeometry.contDiffAt_flatDbar`, `SymplecticGeometry.contDiffAt_modelDbar`: both `∂̄`
  of a `C^(n + 1)` function are `C^n`; `SymplecticGeometry.modelDbar_add`,
  `SymplecticGeometry.modelDbar_smul`: the model `∂̄` is additive and commutes with complex
  scalars; `SymplecticGeometry.flatDbar_complexToRealEuclideanCoord`: the flat `∂̄` of a complex
  coordinate vanishes.
* `SymplecticGeometry.modelDbar_mul`, `SymplecticGeometry.modelDbar_coord_mul`: the Leibniz rule
  for the model `∂̄`, and its form for a product with a complex coordinate.
* `SymplecticGeometry.modelDbar_gaussian`, `SymplecticGeometry.modelDbar_coord_mul_gaussian`: the
  Gaussian `exp (-‖z‖ ^ 2 / 4)` and `z_j` times it have model `∂̄` zero.
* `SymplecticGeometry.exists_jetNormAt_modelDbar_peakFunction_le`,
  `SymplecticGeometry.exists_jetNormAt_modelDbar_peakFunction_mul_le`: the **model `∂̄` bounds**,
  `jetNormAt ℝ r (modelDbar (peakFunction k)) z ≤ C * k ^ (-1 / 2) * (1 + ‖z‖) ^ N *
  exp (-c * ‖z‖ ^ 2)` for `k ≥ 1`, and the same for `peakFunction_mul k j`, uniformly in `j`.

## Implementation notes

The radial cut-off `u ↦ χ ‖u‖` is smooth by `ContDiff.comp_norm_of_eventuallyEq_const`, since
`χ` is constant near `0`. The cut-off part `z ↦ χ (‖z‖ / s)` is that function precomposed with
the scaling `z ↦ s⁻¹ • z`. For `s = 0` or `s ≥ 1` the scalar has norm at most `1`, so
`jetNormAt_comp_const_smul_le` bounds its jet norms by those of `u ↦ χ ‖u‖`, uniformly in `s`.
The jet norms of the Gaussian are bounded by `exists_jetNormAt_exp_neg_mul_norm_sq_le`, and
products by `jetNormAt_fun_smul_le`. The complex coordinates are Tau Ceti's
`complexToRealEuclidean` followed by a projection, `TauCeti.complexToRealEuclideanCoord`.

That the Gaussian has model `∂̄` zero rests on the sign convention `ω₀(z, v) = ⟪J₀ z, v⟫`
(`stdForm_apply_eq_inner`): the derivative `-½ ⟪z, ·⟫ g` of the Gaussian `g`, from Tau Ceti's
`hasFDerivAt_exp_neg_mul_norm_sub_sq`, and the connection
term `-½ i ω₀(z, ·) g` add up to a complex-linear form. By the Leibniz rule the model `∂̄` of the
cut-off Gaussian is the Gaussian times the flat `∂̄` of the cut-off, whose jets vanish off the
annulus `k ^ (1 / 6) ≤ ‖z‖ ≤ 2 * k ^ (1 / 6)`. On that annulus `k ^ (1 / 2) ≤ ‖z‖ ^ 3`, which
gives the factor `k ^ (-1 / 2)` at the cost of the power `(1 + ‖z‖) ^ 3`.

## References

* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002],
  Lemmas 1–2
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
-/

public section

open Metric TauCeti

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

/-- The Gaussian `exp (-‖z‖ ^ 2 / 4)` of the cut-off Gaussians is smooth. -/
private theorem contDiff_gaussian [InnerProductSpace ℝ E] {n : ℕ∞} :
    ContDiff ℝ n fun z : E ↦ Real.exp (-‖z‖ ^ 2 / 4) :=
  Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).neg.div_const 4)

/-- The jet norms of the Gaussian `exp (-‖z‖ ^ 2 / 4)` are at most a constant times
`exp (-‖z‖ ^ 2 / 8)`: `exists_jetNormAt_exp_neg_mul_norm_sq_le` for `a = 1 / 4`. -/
private theorem exists_jetNormAt_gaussian_le [InnerProductSpace ℝ E] (r : ℕ) :
    ∃ B, ∀ z : E,
      jetNormAt ℝ r (fun z : E ↦ Real.exp (-‖z‖ ^ 2 / 4)) z ≤ B * Real.exp (-‖z‖ ^ 2 / 8) := by
  obtain ⟨B, hB⟩ := exists_jetNormAt_exp_neg_mul_norm_sq_le (E := E) r (a := 1 / 4) (by norm_num)
  have hG : (fun z : E ↦ Real.exp (-(1 / 4 * ‖z‖ ^ 2))) = fun z ↦ Real.exp (-‖z‖ ^ 2 / 4) := by
    ext z
    ring_nf
  have hG' (z : E) : Real.exp (-(1 / 4 * ‖z‖ ^ 2) / 2) = Real.exp (-‖z‖ ^ 2 / 8) := by
    ring_nf
  simp_rw [hG, hG'] at hB
  exact ⟨B, hB⟩

theorem contDiff_peakFunction [InnerProductSpace ℝ E] {n : ℕ∞} (k : ℕ) :
    ContDiff ℝ n (peakFunction (E := E) k) := by
  rw [peakFunction_eq_ofRealCLM_comp]
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_peakCutoff_norm_div (by positivity)).smul
    contDiff_gaussian)

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
  obtain ⟨B, hB⟩ := exists_jetNormAt_gaussian_le (E := E) r
  refine ⟨2 ^ r * A * B, 0, 1 / 8, by norm_num, fun k z ↦ ?_⟩
  set s := (k : ℝ) ^ (1 / 6 : ℝ)
  have hs : s = 0 ∨ 1 ≤ s := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · left; simp [s]
    · right; exact Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hχ : ContDiff ℝ r fun z : E ↦ peakCutoff (‖z‖ / s) :=
    contDiff_peakCutoff_norm_div (by positivity)
  have hg : ContDiff ℝ r fun z : E ↦ Real.exp (-‖z‖ ^ 2 / 4) := contDiff_gaussian
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
  have hL : jetNormAt ℝ r L z ≤ 1 + ‖z‖ :=
    jetNormAt_continuousLinearMap_le_one_add_norm (norm_complexToRealEuclideanCoord_le j) r z
  rw [peakFunction_mul_eq]
  refine (jetNormAt_fun_smul_le L.contDiff.contDiffAt
    (contDiff_peakFunction k).contDiffAt).trans ?_
  calc (2 : ℝ) ^ r * jetNormAt ℝ r L z * jetNormAt ℝ r (peakFunction k) z
      ≤ 2 ^ r * (1 + ‖z‖) * (C * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) (h k z)
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = _ := by ring

/-! ### The flat and the model `∂̄` -/

/-- The **flat `∂̄`** of a complex function `f` on `StdSpace ι` at `z`: the flat `∂̄`
`SymplecticGeometry.flatDbarWith` for the constant structure `J₀ = stdComplexStructure ι`, that
is the complex-antilinear part of `df_z` for `J₀` and multiplication by `i` on `ℂ`,
`v ↦ ½ (df_z v + i df_z (J₀ v))`. -/
noncomputable def flatDbar (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  flatDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) f z

theorem flatDbar_def (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar f z =
      flatDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
        f z :=
  (rfl)

/-- The flat `∂̄` of `f` at `z` is the operator `TauCeti.complexAntilinearPartContinuousLinearMap`
for `J₀` and multiplication by `i`, applied to `df_z`. -/
theorem flatDbar_eq (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar f z = complexAntilinearPartContinuousLinearMap (stdComplexStructure ι).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ f z) := by
  rw [flatDbar_def, flatDbarWith_def, LinearMap.coe_toContinuousLinearMap]

theorem flatDbar_apply (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    flatDbar f z v =
      (2⁻¹ : ℝ) • (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (stdComplexStructure ι v)) := by
  rw [flatDbar_def, flatDbarWith_apply, LinearMap.coe_toContinuousLinearMap']

/-- The flat `∂̄` of `f` is `C^n` at a point where `f` is `C^(n + 1)`. -/
theorem contDiffAt_flatDbar {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hf : ContDiffAt ℝ (n + 1) f z) : ContDiffAt ℝ n (flatDbar f) z := by
  rw [show flatDbar f = _ from funext (flatDbar_def f)]
  exact contDiffAt_flatDbarWith contDiffAt_const hf

/-- The flat `∂̄` of a `C^(n + 1)` function is `C^n`. -/
theorem contDiff_flatDbar {n : ℕ∞} {f : StdSpace ι → ℂ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (flatDbar f) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_flatDbar hf.contDiffAt

/-- The flat `∂̄` is additive on functions differentiable at `z`. -/
theorem flatDbar_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : flatDbar (f + g) z = flatDbar f z + flatDbar g z := by
  simp only [flatDbar_def, flatDbarWith_add hf hg]

/-- The flat `∂̄` commutes with complex scalars. -/
@[simp]
theorem flatDbar_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar (c • f) z = c • flatDbar f z := by
  simp only [flatDbar_def, flatDbarWith_smul]

@[simp]
theorem flatDbar_zero (z : StdSpace ι) : flatDbar (0 : StdSpace ι → ℂ) z = 0 := by
  simp only [flatDbar_def, flatDbarWith_zero]

/-- The **Leibniz rule** for the flat `∂̄`: for `f` and `g` differentiable at `z`, the flat `∂̄`
of `f * g` at `z` is `f z` times the flat `∂̄` of `g` plus `g z` times the flat `∂̄` of `f`. -/
theorem flatDbar_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDbar (fun y ↦ f y * g y) z = f z • flatDbar g z + g z • flatDbar f z := by
  simp only [flatDbar_def, flatDbarWith_mul hf hg]

/-- The flat `∂̄` of the complex coordinate `z_j` vanishes: it is complex linear for `J₀`. -/
@[simp]
theorem flatDbar_complexToRealEuclideanCoord (j : ι) :
    flatDbar (complexToRealEuclideanCoord ι j) = 0 := by
  ext z v : 2
  rw [flatDbar_eq, (complexToRealEuclideanCoord ι j).fderiv,
    complexAntilinearPartContinuousLinearMap_apply_apply,
    (isComplexLinear_complexToRealEuclideanCoord j).complexAntilinearPart_eq_zero
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg]
  simp

/-- The **model `∂̄`** of a complex function `f` on `StdSpace ι` at `z`: the model `∂̄`
`SymplecticGeometry.modelDbarWith` for the constant structure `J₀ = stdComplexStructure ι`, that
is Tau Ceti's complex-antilinear part `TauCeti.complexAntilinearPart`, for `J₀` and
multiplication by `i` on `ℂ`, of the model connection `SymplecticGeometry.modelConnection f z`,
`v ↦ df_z v - (ω₀(z, v) / 2) • (i f(z))`, with `ω₀ = stdForm ι`. The `∂̄` reading
`RescaledUnitaryCharts.dbarReading` is `SymplecticGeometry.modelDbarWith` for the structure of
the chart instead. -/
noncomputable def modelDbar (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  modelDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) f z

theorem modelDbar_def (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelDbar f z =
      modelDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
        f z :=
  (rfl)

/-- The model `∂̄` of `f` at `z`, applied to `v`, is the flat `∂̄` of `f` at `z`, applied to `v`,
plus `¼ (⟪z, v⟫ - i ω₀(z, v)) f(z)`. -/
theorem modelDbar_apply (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    modelDbar f z v =
      flatDbar f z v +
        (4⁻¹ : ℝ) • ((inner ℝ z v : ℝ) - Complex.I * (stdForm ι z v : ℝ)) * f z := by
  rw [modelDbar_def, modelDbarWith_apply, flatDbar_apply, modelConnection_apply,
    modelConnection_apply, LinearMap.coe_toContinuousLinearMap']
  simp only [stdForm_apply_stdComplexStructure,
    Complex.real_smul]
  push_cast
  linear_combination (-(4⁻¹ : ℂ) * f z * (inner ℝ z v : ℂ)) * Complex.I_sq

/-- The model `∂̄` is additive on functions differentiable at `z`. -/
theorem modelDbar_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : modelDbar (f + g) z = modelDbar f z + modelDbar g z := by
  simp only [modelDbar_def, modelDbarWith_add hf hg]

/-- The model `∂̄` commutes with complex scalars. -/
@[simp]
theorem modelDbar_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    modelDbar (c • f) z = c • modelDbar f z := by
  simp only [modelDbar_def, modelDbarWith_smul]

@[simp]
theorem modelDbar_zero (z : StdSpace ι) : modelDbar (0 : StdSpace ι → ℂ) z = 0 := by
  simp only [modelDbar_def, modelDbarWith_zero]

/-- The model `∂̄` of `f` is `C^n` at a point where `f` is `C^(n + 1)`. -/
theorem contDiffAt_modelDbar {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hf : ContDiffAt ℝ (n + 1) f z) : ContDiffAt ℝ n (modelDbar f) z := by
  rw [show modelDbar f = _ from funext (modelDbar_def f)]
  exact contDiffAt_modelDbarWith contDiffAt_const hf

/-- The model `∂̄` of a `C^(n + 1)` function is `C^n`. -/
theorem contDiff_modelDbar {n : ℕ∞} {f : StdSpace ι → ℂ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (modelDbar f) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_modelDbar hf.contDiffAt

/-- The **Leibniz rule** for the model `∂̄`: for `f` and `g` differentiable at `z`, the model
`∂̄` of `f * g` at `z` is `f z` times the model `∂̄` of `g` plus `g z` times the flat `∂̄` of
`f`. -/
theorem modelDbar_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    modelDbar (fun y ↦ f y * g y) z = f z • modelDbar g z + g z • flatDbar f z := by
  simp only [modelDbar_def, flatDbar_def, modelDbarWith_mul hf hg]

/-- The derivative of the Gaussian `exp (-‖z‖ ^ 2 / 4)`, as a complex function. -/
private theorem fderiv_gaussian_apply (z v : StdSpace ι) :
    fderiv ℝ (fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ)) z v =
      (-(2⁻¹ * inner ℝ z v) : ℝ) * Real.exp (-‖z‖ ^ 2 / 4) := by
  have he (y : StdSpace ι) : -(1 / 4 : ℝ) * ‖y - 0‖ ^ 2 = -‖y‖ ^ 2 / 4 := by
    rw [sub_zero]
    ring
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    (hasFDerivAt_exp_neg_mul_norm_sub_sq (1 / 4) (0 : StdSpace ι) z)
  simp only [he, Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply, sub_zero,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

/-- **The Gaussian is model-holomorphic**: the model `∂̄` of `z ↦ exp (-‖z‖ ^ 2 / 4)` vanishes. -/
theorem modelDbar_gaussian :
    modelDbar (fun z : StdSpace ι ↦ (Real.exp (-‖z‖ ^ 2 / 4) : ℂ)) = 0 := by
  ext z v
  have h : inner ℝ z (stdComplexStructure ι v) = -inner ℝ (stdComplexStructure ι z) v := by
    rw [← inner_stdComplexStructure_stdComplexStructure z, AlmostComplexStructure.apply_apply,
      inner_neg_right]
  rw [modelDbar_apply, flatDbar_apply, fderiv_gaussian_apply, fderiv_gaussian_apply,
    stdForm_apply_eq_inner, h]
  simp only [Complex.real_smul, zero_apply, Pi.zero_apply]
  push_cast
  ring

/-- The model `∂̄` of `z_j` times `f` is `z_j` times the model `∂̄` of `f`. -/
theorem modelDbar_coord_mul {f : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (j : ι) :
    modelDbar (fun y ↦ (complexToRealEuclidean ι).symm y j * f y) z =
      (complexToRealEuclidean ι).symm z j • modelDbar f z := by
  simp only [← complexToRealEuclideanCoord_apply]
  rw [modelDbar_mul (complexToRealEuclideanCoord ι j).differentiableAt hf,
    flatDbar_complexToRealEuclideanCoord]
  ext v
  simp

/-- **`z_j` times the Gaussian is model-holomorphic**: the model `∂̄` of
`z ↦ z_j * exp (-‖z‖ ^ 2 / 4)` vanishes. -/
theorem modelDbar_coord_mul_gaussian (j : ι) :
    modelDbar (fun z : StdSpace ι ↦
      (complexToRealEuclidean ι).symm z j * (Real.exp (-‖z‖ ^ 2 / 4) : ℂ)) = 0 := by
  ext z : 1
  have hG : ContDiff ℝ 1 fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_gaussian
  rw [modelDbar_coord_mul (hG.differentiable one_ne_zero z) j, modelDbar_gaussian]
  ext v
  simp

/-! ### The model `∂̄` of the cut-off Gaussians -/

/-- The flat `∂̄` of the scaled cut-off `z ↦ χ (‖z‖ / s)`, as a function of the point. -/
private noncomputable def cutoffDbar (s : ℝ) : StdSpace ι → StdSpace ι →L[ℝ] ℂ :=
  flatDbar fun y ↦ ((peakCutoff (‖y‖ / s) : ℝ) : ℂ)

private theorem contDiff_cutoffDbar {n : ℕ∞} {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ n (cutoffDbar (ι := ι) s) :=
  contDiff_flatDbar (Complex.ofRealCLM.contDiff.comp (contDiff_peakCutoff_norm_div hs))

/-- The jet norms of the flat `∂̄` of the scaled cut-offs are bounded uniformly in `s ≥ 1`. -/
private theorem exists_jetNormAt_cutoffDbar_le (r : ℕ) :
    ∃ A, ∀ s : ℝ, 1 ≤ s → ∀ z : StdSpace ι, jetNormAt ℝ r (cutoffDbar s) z ≤ A := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_peakCutoff_norm_div_le (E := StdSpace ι) (r + 1)
  set P := complexAntilinearPartContinuousLinearMap (stdComplexStructure ι).toLinearMap
    (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
  refine ⟨‖P‖ * A, fun s hs z ↦ ?_⟩
  have hχ : ContDiff ℝ (r + 1) fun y : StdSpace ι ↦ peakCutoff (‖y‖ / s) :=
    contDiff_peakCutoff_norm_div (by linarith)
  have hχC : ContDiff ℝ (r + 1) (Complex.ofRealCLM ∘ fun y : StdSpace ι ↦ peakCutoff (‖y‖ / s)) :=
    Complex.ofRealCLM.contDiff.comp hχ
  have h1 : jetNormAt ℝ r (cutoffDbar (ι := ι) s) z ≤
      ‖P‖ * jetNormAt ℝ r (fderiv ℝ (Complex.ofRealCLM ∘ fun y : StdSpace ι ↦
        peakCutoff (‖y‖ / s))) z := by
    rw [show cutoffDbar (ι := ι) s = P ∘ fderiv ℝ (Complex.ofRealCLM ∘ fun y : StdSpace ι ↦
      peakCutoff (‖y‖ / s)) from funext fun y ↦ flatDbar_eq _ y]
    exact jetNormAt_comp_left_le P (hχC.fderiv_right le_rfl).contDiffAt
  have h2 : jetNormAt ℝ r (fderiv ℝ (Complex.ofRealCLM ∘ fun y : StdSpace ι ↦
      peakCutoff (‖y‖ / s))) z ≤ A := by
    have h := jetNormAt_comp_left_le Complex.ofRealCLM hχ.contDiffAt (z := z)
    rw [Complex.ofRealCLM_norm, one_mul, jetNormAt_succ] at h
    linarith [hA s (.inr hs) z, norm_nonneg ((Complex.ofRealCLM ∘ fun y : StdSpace ι ↦
      peakCutoff (‖y‖ / s)) z)]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- The flat `∂̄` of the scaled cut-off has vanishing jets off the annulus `s ≤ ‖z‖ ≤ 2 s`. -/
private theorem jetNormAt_cutoffDbar_eq_zero (r : ℕ) {s : ℝ} (hs : 0 < s) {z : StdSpace ι}
    (hz : ‖z‖ < s ∨ 2 * s < ‖z‖) : jetNormAt ℝ r (cutoffDbar s) z = 0 := by
  -- On each of the two open sets, the cut-off is constant, so its derivative vanishes.
  have key : ∀ U : Set (StdSpace ι), IsOpen U → z ∈ U → (∃ c : ℝ, ∀ y ∈ U,
      peakCutoff (‖y‖ / s) = c) → jetNormAt ℝ r (cutoffDbar s) z = 0 := by
    rintro U hU hzU ⟨c, hc⟩
    have h : cutoffDbar (ι := ι) s =ᶠ[nhds z] fun _ ↦ 0 := by
      filter_upwards [hU.mem_nhds hzU] with y hy
      have hconst : (fun y : StdSpace ι ↦ ((peakCutoff (‖y‖ / s) : ℝ) : ℂ)) =ᶠ[nhds y]
          fun _ ↦ (c : ℂ) := by
        filter_upwards [hU.mem_nhds hy] with w hw
        rw [hc w hw]
      rw [cutoffDbar, flatDbar_eq, hconst.fderiv_eq, fderiv_const_apply, map_zero]
    rw [jetNormAt_congr_of_eventuallyEq r h, jetNormAt_const, norm_zero]
  rcases hz with hz | hz
  · refine key {y | ‖y‖ < s} (isOpen_lt continuous_norm continuous_const) hz ⟨1, fun y hy ↦ ?_⟩
    exact peakCutoff_of_le_one ((div_le_one hs).2 (le_of_lt hy))
  · refine key {y | 2 * s < ‖y‖} (isOpen_lt continuous_const continuous_norm) hz
      ⟨0, fun y hy ↦ ?_⟩
    exact peakCutoff_of_two_le ((le_div_iff₀ hs).2 (le_of_lt hy))

/-- The jets of the flat `∂̄` of the cut-off of `peakFunction k` are `O(k ^ (-1 / 2))`, at the
cost of a factor `(1 + ‖z‖) ^ 3`: they vanish off the annulus `k ^ (1 / 6) ≤ ‖z‖ ≤ 2 k ^ (1 / 6)`,
and on it `k ^ (1 / 2) ≤ ‖z‖ ^ 3`. -/
private theorem exists_jetNormAt_cutoffDbar_le_rpow (r : ℕ) :
    ∃ A, ∀ k : ℕ, 1 ≤ k → ∀ z : StdSpace ι,
      jetNormAt ℝ r (cutoffDbar ((k : ℝ) ^ (1 / 6 : ℝ))) z ≤
        A * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ 3 := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_cutoffDbar_le (ι := ι) r
  refine ⟨A, fun k hk z ↦ ?_⟩
  set s := (k : ℝ) ^ (1 / 6 : ℝ)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs1 : 1 ≤ s := Real.one_le_rpow (by exact_mod_cast hk) (by norm_num)
  have hA0 : 0 ≤ A := (jetNormAt_nonneg (𝕜 := ℝ) r (cutoffDbar (ι := ι) s) z).trans (hA s hs1 z)
  by_cases hz : ‖z‖ < s ∨ 2 * s < ‖z‖
  · rw [jetNormAt_cutoffDbar_eq_zero r (zero_lt_one.trans_le hs1) hz]
    positivity
  have hsz : s ≤ ‖z‖ := le_of_not_gt fun h ↦ hz (.inl h)
  have hs3 : (k : ℝ) ^ (1 / 2 : ℝ) = s ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    norm_num
  have h1 : 1 ≤ (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ 3 := by
    calc (1 : ℝ) = (k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hk0]
          norm_num
      _ ≤ (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ 3 := by
          rw [hs3]
          gcongr
          linarith
  calc jetNormAt ℝ r (cutoffDbar (ι := ι) s) z ≤ A * 1 := by
        rw [mul_one]
        exact hA s hs1 z
    _ ≤ A * ((k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ 3) := by gcongr
    _ = _ := by ring

/-- On the standard space, the model `∂̄` of the cut-off Gaussian is the Gaussian times the flat
`∂̄` of the cut-off. -/
private theorem modelDbar_peakFunction_eq (k : ℕ) :
    modelDbar (peakFunction (E := StdSpace ι) k) =
      fun z ↦ Real.exp (-‖z‖ ^ 2 / 4) • cutoffDbar ((k : ℝ) ^ (1 / 6 : ℝ)) z := by
  have hχ : ContDiff ℝ 1 fun y : StdSpace ι ↦
      ((peakCutoff (‖y‖ / (k : ℝ) ^ (1 / 6 : ℝ)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_peakCutoff_norm_div (by positivity))
  have hG : ContDiff ℝ 1 fun y : StdSpace ι ↦ (Real.exp (-‖y‖ ^ 2 / 4) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_gaussian
  have hP : peakFunction (E := StdSpace ι) k = fun y ↦
      ((peakCutoff (‖y‖ / (k : ℝ) ^ (1 / 6 : ℝ)) : ℝ) : ℂ) * (Real.exp (-‖y‖ ^ 2 / 4) : ℂ) := by
    ext y
    rw [peakFunction_def, Complex.ofReal_mul]
  ext z : 1
  rw [hP, modelDbar_mul (hχ.differentiable one_ne_zero z) (hG.differentiable one_ne_zero z),
    modelDbar_gaussian, cutoffDbar]
  ext v
  simp [Complex.real_smul]

/-- The model `∂̄` of the cut-off Gaussian is smooth. -/
theorem contDiff_modelDbar_peakFunction {n : ℕ∞} (k : ℕ) :
    ContDiff ℝ n (modelDbar (peakFunction (E := StdSpace ι) k)) :=
  contDiff_modelDbar (contDiff_peakFunction k)

/-- The model `∂̄` of `z_j` times the cut-off Gaussian is smooth. -/
theorem contDiff_modelDbar_peakFunction_mul {n : ℕ∞} (k : ℕ) (j : ι) :
    ContDiff ℝ n (modelDbar (peakFunction_mul k j)) :=
  contDiff_modelDbar (contDiff_peakFunction_mul k j)

/-- The **model `∂̄` bound** for the cut-off Gaussians: for every order `r` there are `C`, `N` and
`c > 0` such that `jetNormAt ℝ r (modelDbar (peakFunction k)) z` is at most
`C * k ^ (-1 / 2) * (1 + ‖z‖) ^ N * exp (-c * ‖z‖ ^ 2)` for all `k ≥ 1` and all `z`. -/
theorem exists_jetNormAt_modelDbar_peakFunction_le (r : ℕ) :
    ∃ C N, ∃ c > 0, ∀ k : ℕ, 1 ≤ k → ∀ z : StdSpace ι,
      jetNormAt ℝ r (modelDbar (peakFunction k)) z ≤
        C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2) := by
  obtain ⟨A, hA⟩ := exists_jetNormAt_cutoffDbar_le_rpow (ι := ι) r
  obtain ⟨B, hB⟩ := exists_jetNormAt_gaussian_le (E := StdSpace ι) r
  refine ⟨2 ^ r * B * A, 3, 1 / 8, by norm_num, fun k hk z ↦ ?_⟩
  rw [modelDbar_peakFunction_eq]
  refine (jetNormAt_fun_smul_le contDiff_gaussian.contDiffAt
    (contDiff_cutoffDbar (ι := ι) (n := r) (by positivity)).contDiffAt).trans ?_
  calc (2 : ℝ) ^ r * jetNormAt ℝ r (fun z : StdSpace ι ↦ Real.exp (-‖z‖ ^ 2 / 4)) z *
        jetNormAt ℝ r (cutoffDbar ((k : ℝ) ^ (1 / 6 : ℝ))) z
      ≤ 2 ^ r * (B * Real.exp (-‖z‖ ^ 2 / 8)) * (A * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hB z) (by positivity)) (hA k hk z)
          (jetNormAt_nonneg _ _ _)
          (mul_nonneg (by positivity) ((jetNormAt_nonneg _ _ _).trans (hB z)))
    _ = _ := by ring_nf

/-- The **model `∂̄` bound** for the coordinates times the cut-off Gaussians: for every order `r`
there are `C`, `N` and `c > 0` such that `jetNormAt ℝ r (modelDbar (peakFunction_mul k j)) z` is
at most `C * k ^ (-1 / 2) * (1 + ‖z‖) ^ N * exp (-c * ‖z‖ ^ 2)` for all `k ≥ 1`, `j` and `z`. -/
theorem exists_jetNormAt_modelDbar_peakFunction_mul_le (r : ℕ) :
    ∃ C N, ∃ c > 0, ∀ k : ℕ, 1 ≤ k → ∀ (j : ι) (z : StdSpace ι),
      jetNormAt ℝ r (modelDbar (peakFunction_mul k j)) z ≤
        C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2) := by
  obtain ⟨C, N, c, hc, h⟩ := exists_jetNormAt_modelDbar_peakFunction_le (ι := ι) r
  refine ⟨2 ^ r * C, N + 1, c, hc, fun k hk j z ↦ ?_⟩
  set L := complexToRealEuclideanCoord ι j
  have hEq : modelDbar (peakFunction_mul k j) = fun z ↦ L z • modelDbar (peakFunction k) z := by
    ext z : 1
    rw [show peakFunction_mul k j = fun y ↦ (complexToRealEuclidean ι).symm y j * peakFunction k y
      from funext (peakFunction_mul_def k j),
      modelDbar_coord_mul ((contDiff_peakFunction (n := 1) k).differentiable one_ne_zero z),
      complexToRealEuclideanCoord_apply]
  rw [hEq]
  refine (jetNormAt_fun_smul_le L.contDiff.contDiffAt
    (contDiff_modelDbar_peakFunction (n := r) k).contDiffAt).trans ?_
  calc (2 : ℝ) ^ r * jetNormAt ℝ r L z * jetNormAt ℝ r (modelDbar (peakFunction k)) z
      ≤ 2 ^ r * (1 + ‖z‖) *
          (C * (k : ℝ) ^ (-1 / 2 : ℝ) * (1 + ‖z‖) ^ N * Real.exp (-c * ‖z‖ ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (jetNormAt_continuousLinearMap_le_one_add_norm
          (norm_complexToRealEuclideanCoord_le j) r z)
          (by positivity)) (h k hk z) (jetNormAt_nonneg _ _ _) (by positivity)
    _ = _ := by ring

end SymplecticGeometry

end
