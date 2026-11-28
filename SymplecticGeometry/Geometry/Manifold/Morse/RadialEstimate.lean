/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.BirthDeath
import Mathlib.Analysis.Normed.Module.FiniteDimension
import SymplecticGeometry.Analysis.Calculus.MeanValue

/-!
# Radial estimates for the normal forms of Morse–Bott and birth–death charts

In the normal form of a Morse–Bott chart (`TauCeti.MorseBottChart.quadratic`, in particular of a
Morse chart `TauCeti.MorseChart`) or of a birth–death chart
(`TauCeti.BirthDeathChart.normalForm`), the derivative does not grow when one moves towards the
origin along a ray: `‖D F (s z)‖ ≤ K ‖D F (z)‖` for `s ∈ [0, 1]`. In the coordinates of the chart
the components of `D F (z)` are `wᵢ zᵢ` and `z_{i₀}²`, which only shrink when `z` is replaced by
`s z`. For the quadratic normal form `D F (s z) = s D F (z)`, so `K = 1`; for the birth–death
normal form `K` compares the norm of `E` with the coordinates of the chart.

With the mean value inequality along the segment from `0` to `z`
(`SymplecticGeometry.norm_le_mul_norm_mul_norm_fderiv_of_norm_fderiv_le`), a function `H`
vanishing at the origin with `‖D H‖ ≤ C ‖D F‖` on a ball around it then satisfies
`|H z| ≤ C K ‖z‖ ‖D F (z)‖` there. This is the estimate `|H| ≤ α r |df|` in the proof of
Lemma 12.9 of [CieliebakEliashberg2012], where it lets a cut-off of `t H` keep the Liouville
fields gradient-like.

## Main results

* `TauCeti.MorseBottChart.fderiv_quadratic_smul` and
  `TauCeti.MorseBottChart.norm_fderiv_quadratic_smul_le`: the derivative of the quadratic normal
  form is linear along rays.
* `TauCeti.MorseBottChart.norm_le_mul_norm_mul_norm_fderiv_quadratic`: the estimate for the
  quadratic normal form, with `K = 1`.
* `TauCeti.BirthDeathChart.exists_norm_fderiv_normalForm_smul_le`: the derivative of the
  birth–death normal form grows at most by a constant factor away from the origin.
* `TauCeti.BirthDeathChart.exists_norm_le_mul_norm_mul_norm_fderiv_normalForm`: the estimate for
  the birth–death normal form.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set Metric

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace MorseBottChart

variable (φ : MorseBottChart E f x)

/-- The derivative of the quadratic normal form of a Morse–Bott chart is linear in the point:
`D Q (s z) = s D Q (z)`. -/
theorem fderiv_quadratic_smul (s : ℝ) (z : E) :
    fderiv ℝ φ.quadratic (s • z) = s • fderiv ℝ φ.quadratic z := by
  ext v
  simp only [fderiv_quadratic_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [smul_apply, smul_eq_mul, fderiv_quadratic_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The derivative of the quadratic normal form of a Morse–Bott chart does not grow towards the
origin: `‖D Q (s z)‖ ≤ ‖D Q (z)‖` for `s ∈ [0, 1]`. -/
theorem norm_fderiv_quadratic_smul_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : E) :
    ‖fderiv ℝ φ.quadratic (s • z)‖ ≤ ‖fderiv ℝ φ.quadratic z‖ := by
  rw [fderiv_quadratic_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

/-- **The primitive estimate in a Morse–Bott chart.** If `H : E → F` is differentiable on the
ball `B(0, r)`, vanishes at `0`, and has `‖D H‖ ≤ C ‖D Q‖` on the ball for the quadratic normal
form `Q` and some `C ≥ 0`, then `‖H z‖ ≤ C ‖z‖ ‖D Q (z)‖` on the ball. -/
theorem norm_le_mul_norm_mul_norm_fderiv_quadratic {r C : ℝ} {H : E → F} (hC : 0 ≤ C)
    (hH : DifferentiableOn ℝ H (ball 0 r)) (hH0 : H 0 = 0)
    (hHQ : ∀ z ∈ ball (0 : E) r, ‖fderiv ℝ H z‖ ≤ C * ‖fderiv ℝ φ.quadratic z‖)
    {z : E} (hz : z ∈ ball 0 r) :
    ‖H z‖ ≤ C * ‖z‖ * ‖fderiv ℝ φ.quadratic z‖ := by
  simpa using SymplecticGeometry.norm_le_mul_norm_mul_norm_fderiv_of_norm_fderiv_le (K := 1) hC
    (fun z _ s hs ↦ by simpa using φ.norm_fderiv_quadratic_smul_le hs z) hH hH0 hHQ hz

end MorseBottChart

namespace BirthDeathChart

variable (φ : BirthDeathChart E f x)

/-- The derivative of the birth–death normal form along the `i`-th coordinate vector:
`wᵢ (L z)ᵢ`, plus `(L z)_{i₀}²` when `i` is the cubic coordinate `i₀`. -/
private theorem fderiv_normalForm_apply_coord_symm_single (z : E)
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ φ.normalForm z (φ.toMorseBottChart.coord.symm (Pi.single i 1)) =
      φ.toMorseBottChart.weight i * φ.toMorseBottChart.coord z i +
        if i = φ.cubicIndex then φ.toMorseBottChart.coord z φ.cubicIndex ^ 2 else 0 := by
  rw [fderiv_normalForm_apply, LinearEquiv.apply_symm_apply,
    Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  by_cases hi : i = φ.cubicIndex
  · subst hi
    simp
  · simp [hi, Ne.symm hi]

/-- The components of the derivative of the birth–death normal form do not grow towards the
origin. -/
private theorem abs_fderiv_normalForm_smul_apply_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (z : E)
    (i : Fin (Module.finrank ℝ E)) :
    |fderiv ℝ φ.normalForm (s • z) (φ.toMorseBottChart.coord.symm (Pi.single i 1))| ≤
      |fderiv ℝ φ.normalForm z (φ.toMorseBottChart.coord.symm (Pi.single i 1))| := by
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  rw [fderiv_normalForm_apply_coord_symm_single, fderiv_normalForm_apply_coord_symm_single,
    map_smul]
  by_cases hi : i = φ.cubicIndex
  · subst hi
    simp only [φ.weight_cubicIndex, zero_mul, zero_add, ite_true, Pi.smul_apply, smul_eq_mul,
      mul_pow, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs1)
  · simp only [hi, ite_false, add_zero, Pi.smul_apply, smul_eq_mul,
      mul_left_comm _ s, abs_mul s]
    exact mul_le_of_le_one_left (abs_nonneg _) hs1

/-- The derivative of the normal form of a birth–death chart grows at most by a constant factor
away from the origin: there is `K` with `‖D N (s z)‖ ≤ K ‖D N (z)‖` for all `z` and `s ∈ [0, 1]`.
In the coordinates of the chart the components of `D N (z)` are `wᵢ (L z)ᵢ` and `(L z)_{i₀}²`;
`K` compares the norm of `E` with the sup norm of these coordinates. -/
theorem exists_norm_fderiv_normalForm_smul_le :
    ∃ K, ∀ z : E, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ φ.normalForm (s • z)‖ ≤ K * ‖fderiv ℝ φ.normalForm z‖ := by
  let v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    (Pi.basisFun ℝ (Fin (Module.finrank ℝ E))).map φ.toMorseBottChart.coord.symm
  have hv (i) : v i = φ.toMorseBottChart.coord.symm (Pi.single i 1) := by
    simp [v]
  obtain ⟨K₀, -, hK₀⟩ := v.exists_opNorm_le (F := ℝ)
  set S := ∑ i, ‖v i‖
  refine ⟨K₀ * S, fun z s hs ↦ ?_⟩
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  rw [mul_assoc, mul_comm S]
  refine hK₀ (mul_nonneg (norm_nonneg _) hS) fun i ↦ ?_
  calc ‖fderiv ℝ φ.normalForm (s • z) (v i)‖ ≤ ‖fderiv ℝ φ.normalForm z (v i)‖ := by
        simpa only [Real.norm_eq_abs, hv] using φ.abs_fderiv_normalForm_smul_apply_le hs z i
    _ ≤ ‖fderiv ℝ φ.normalForm z‖ * ‖v i‖ := (fderiv ℝ φ.normalForm z).le_opNorm _
    _ ≤ ‖fderiv ℝ φ.normalForm z‖ * S := by
        gcongr
        exact Finset.single_le_sum (f := fun i ↦ ‖v i‖) (fun i _ ↦ norm_nonneg _)
          (Finset.mem_univ i)

/-- **The primitive estimate in a birth–death chart.** There is `K` such that for every ball
`B(0, r)`, every `C ≥ 0`, and every `H : E → F` that is differentiable on the ball, vanishes at
`0`, and has `‖D H‖ ≤ C ‖D N‖` on the ball for the normal form `N`, we have
`‖H z‖ ≤ C K ‖z‖ ‖D N (z)‖` on the ball. -/
theorem exists_norm_le_mul_norm_mul_norm_fderiv_normalForm :
    ∃ K, ∀ {r C : ℝ} {H : E → F}, 0 ≤ C → DifferentiableOn ℝ H (ball 0 r) → H 0 = 0 →
      (∀ z ∈ ball (0 : E) r, ‖fderiv ℝ H z‖ ≤ C * ‖fderiv ℝ φ.normalForm z‖) →
        ∀ z ∈ ball (0 : E) r, ‖H z‖ ≤ C * K * ‖z‖ * ‖fderiv ℝ φ.normalForm z‖ := by
  obtain ⟨K, hK⟩ := φ.exists_norm_fderiv_normalForm_smul_le
  exact ⟨K, fun hC hH hH0 hHN z hz ↦
    SymplecticGeometry.norm_le_mul_norm_mul_norm_fderiv_of_norm_fderiv_le hC
      (fun z _ ↦ hK z) hH hH0 hHN hz⟩

end BirthDeathChart

end TauCeti

end
