/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import SymplecticGeometry.Analysis.Calculus.FDeriv.LogNormSq

/-!
# The Hessian of `log |F|²` in a chart, in the directions `v` and `J₀ v`

Let `F : StdSpace ι → ℂ` be `C²` at `0` with `F 0 ≠ 0`, let `Jf` be a field of real-linear
endomorphisms of `StdSpace ι`, differentiable at `0` with `Jf 0 = J₀` the standard complex
structure, and let `G z` be the complex-antilinear part, for `Jf z` and multiplication by `i`,
of the covariant derivative `dF_z + i A₀(z) F z` of the model connection form
`A₀(z) w = -ω₀(z, w) / 2`. This is the shape of
`SymplecticGeometry.RescaledUnitaryCharts.dbarReading`, with `Jf` in place of the pushed-forward
almost complex structure.

The main result, `fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le`, says that the second
derivative `H` of `g = log ‖F‖²` at `0` satisfies
`H(v, v) + H(J₀ v, J₀ v) ≤ (-2 + 8 ε) ‖v‖²`, with
`ε = ‖dG₀‖ / ‖F 0‖ + ‖dJf₀‖ ‖dF₀‖ / ‖F 0‖ + ‖G 0‖ ‖dF₀‖ / ‖F 0‖²`.

The sum over `v` and `J₀ v` kills the parts of type `(2,0)` and `(0,2)` of the second
derivative of `F`; what is left is read off the derivative of `G` at `0`, up to the derivative of
`Jf` applied to `dF` and the curvature of `A₀`, which contributes `-ω₀(v, J₀ v) = -‖v‖²` and
gives the constant `-2`. The square terms of the Hessian of the logarithm are controlled by
`dF₀ v ^ 2 + dF₀ (J₀ v) ^ 2 = 2 G 0 v (dF₀ v - i dF₀ (J₀ v))`.

## References

* [D. Auroux, *Asymptotically holomorphic families of symplectic submanifolds*][Auroux1997],
  Proposition 2 and §5.1
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4
-/

public section

open Filter TauCeti
open scoped Topology

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι] {F : StdSpace ι → ℂ}
  {Jf : StdSpace ι → StdSpace ι →L[ℝ] StdSpace ι} {G : StdSpace ι → StdSpace ι →L[ℝ] ℂ}

/-- The values of `G` written out: `2 G z w = L z w + i L z (Jf z w)` for
`L z w = dF_z w - (ω₀(z, w) / 2) • (i F z)`. -/
private theorem eventually_apply_eq_of_eventually_eq
    (hG : ∀ᶠ z in 𝓝 0, G z = LinearMap.toContinuousLinearMap (complexAntilinearPart
      (Jf z : StdSpace ι →ₗ[ℝ] StdSpace ι) (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      ((fderiv ℝ F z - ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap
        ((stdForm ι).toBilinForm z)).smulRight (Complex.I * F z) : StdSpace ι →L[ℝ] ℂ) :
          StdSpace ι →ₗ[ℝ] ℂ))) :
    ∀ᶠ z in 𝓝 0, ∀ w, G z w = (2⁻¹ : ℝ) • (fderiv ℝ F z w -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z w) • (Complex.I * F z) +
      Complex.I * (fderiv ℝ F z (Jf z w) -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z (Jf z w)) •
        (Complex.I * F z))) := by
  filter_upwards [hG] with z hz w
  rw [hz]
  simp [complexAntilinearPart_apply, -stdForm_apply]
  ring

/-- The derivative of `G` at `0`, in terms of the first two derivatives of `F` and the
derivative of `Jf`. -/
private theorem fderiv_apply_apply_eq (hF2 : DifferentiableAt ℝ (fderiv ℝ F) 0)
    (hF1 : DifferentiableAt ℝ F 0) (hJ : DifferentiableAt ℝ Jf 0)
    (hJ0 : ∀ w, Jf 0 w = stdComplexStructure ι w) (hG : DifferentiableAt ℝ G 0)
    (hGw : ∀ᶠ z in 𝓝 0, ∀ w, G z w = (2⁻¹ : ℝ) • (fderiv ℝ F z w -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z w) • (Complex.I * F z) +
      Complex.I * (fderiv ℝ F z (Jf z w) -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z (Jf z w)) •
        (Complex.I * F z))))
    (u w : StdSpace ι) :
    fderiv ℝ G 0 u w = (2⁻¹ : ℝ) • (fderiv ℝ (fderiv ℝ F) 0 u w -
      (2⁻¹ * stdForm ι u w) • (Complex.I * F 0) +
      Complex.I * (fderiv ℝ (fderiv ℝ F) 0 u (stdComplexStructure ι w) +
        fderiv ℝ F 0 (fderiv ℝ Jf 0 u w) -
        (2⁻¹ * stdForm ι u (stdComplexStructure ι w)) • (Complex.I * F 0))) := by
  set B := (stdForm ι).toBilinForm.toContinuousBilinearMap
  rw [show fderiv ℝ G 0 u w = fderiv ℝ (fun z ↦ G z w) 0 u by
    rw [fderiv_clm_apply hG (differentiableAt_const w)]; simp,
    Filter.EventuallyEq.fderiv_eq (f₁ := fun z ↦ G z w) (hGw.mono fun z hz ↦ hz w)]
  have hJw := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)
  have hB₁ := B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : StdSpace ι))
    (hasFDerivAt_const w 0)
  have hB₂ := B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : StdSpace ι)) hJw
  have hIF := hF1.hasFDerivAt.const_mul Complex.I
  have hΦ : HasFDerivAt (fun z ↦ (2⁻¹ : ℝ) • (fderiv ℝ F z w - (2⁻¹ * B z w) • (Complex.I * F z) +
      Complex.I * (fderiv ℝ F z (Jf z w) - (2⁻¹ * B z (Jf z w)) • (Complex.I * F z)))) _ 0 :=
    (((hF2.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)).sub
      ((hB₁.const_mul 2⁻¹).smul hIF)).add (((hF2.hasFDerivAt.clm_apply hJw).sub
        ((hB₂.const_mul 2⁻¹).smul hIF)).const_mul Complex.I)).const_smul (2⁻¹ : ℝ)
  rw [hΦ.fderiv]
  simp [B, hJ0, -stdForm_apply]
  ring

/-- **The Hessian of `log |F|²` in the directions `v` and `J₀ v`, in a chart.** Let
`F : StdSpace ι → ℂ` be `C²` at `0` with `F 0 ≠ 0`, let `Jf` be differentiable at `0` with
`Jf 0 = J₀`, and let `G` agree near `0` with the complex-antilinear part, for `Jf z` and
multiplication by `i`, of `dF_z - (ω₀(z, ·) / 2) • (i F z)`; let `G` be differentiable at `0`.
Then the second derivative `H` of `z ↦ log (‖F z‖ ^ 2)` at `0` satisfies
`H(v, v) + H(J₀ v, J₀ v) ≤ (-2 + 8 ε) ‖v‖²` for every `v`, where
`ε = ‖dG₀‖ / ‖F 0‖ + ‖dJf₀‖ ‖dF₀‖ / ‖F 0‖ + ‖G 0‖ ‖dF₀‖ / ‖F 0‖²`. -/
theorem fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le (hF : ContDiffAt ℝ 2 F 0)
    (hF0 : F 0 ≠ 0) (hJ : DifferentiableAt ℝ Jf 0)
    (hJ0 : ∀ w, Jf 0 w = stdComplexStructure ι w) (hGd : DifferentiableAt ℝ G 0)
    (hG : ∀ᶠ z in 𝓝 0, G z = LinearMap.toContinuousLinearMap (complexAntilinearPart
      (Jf z : StdSpace ι →ₗ[ℝ] StdSpace ι) (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
      ((fderiv ℝ F z - ((2⁻¹ : ℝ) • LinearMap.toContinuousLinearMap
        ((stdForm ι).toBilinForm z)).smulRight (Complex.I * F z) : StdSpace ι →L[ℝ] ℂ) :
          StdSpace ι →ₗ[ℝ] ℂ)))
    (v : StdSpace ι) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) 0 v v +
        fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) 0 (stdComplexStructure ι v)
          (stdComplexStructure ι v) ≤
      (-2 + 8 * (‖fderiv ℝ G 0‖ / ‖F 0‖ + ‖fderiv ℝ Jf 0‖ * ‖fderiv ℝ F 0‖ / ‖F 0‖ +
        ‖G 0‖ * ‖fderiv ℝ F 0‖ / ‖F 0‖ ^ 2)) * ‖v‖ ^ 2 := by
  have hGw := eventually_apply_eq_of_eventually_eq hG
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDG := fderiv_apply_apply_eq hF2 (hF.differentiableAt (by norm_num)) hJ hJ0 hGd hGw
  set J := stdComplexStructure ι
  set p := F 0
  set dF := fderiv ℝ F 0
  set h := fderiv ℝ (fderiv ℝ F) 0
  set DG := fderiv ℝ G 0
  set DJ := fderiv ℝ Jf 0
  set a := dF v
  set b := dF (J v)
  set E₁ : ℂ := (2 : ℝ) • DG v v + (2 : ℝ) • DG (J v) (J v) -
    Complex.I * (dF (DJ v v) + dF (DJ (J v) (J v)))
  have hsym : h (J v) v = h v (J v) := (hF.isSymmSndFDerivAt (by simp)) _ _
  have hω : stdForm ι v (J v) = ‖v‖ ^ 2 := by
    rw [stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq]
  have hω' : stdForm ι (J v) (J (J v)) = ‖v‖ ^ 2 := by
    rw [stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq, norm_stdComplexStructure]
  -- The `J₀`-symmetrized second derivative of `F`, read off the derivative of `G`.
  have hkey : h v v + h (J v) (J v) = E₁ - (‖v‖ ^ 2 : ℝ) • p := by
    rw [show E₁ = (2 : ℝ) • DG v v + (2 : ℝ) • DG (J v) (J v) -
      Complex.I * (dF (DJ v v) + dF (DJ (J v) (J v))) from rfl, hDG v v, hDG (J v) (J v)]
    rw [hω, hω', (stdForm ι).self_eq_zero, (stdForm ι).self_eq_zero, J.apply_apply, map_neg]
    simp only [Complex.real_smul]
    push_cast
    linear_combination Complex.I * hsym + p * (‖v‖ : ℂ) ^ 2 * Complex.I_sq
  -- The value of `G` at `0` and the square terms.
  have hG0 : (2 : ℂ) * G 0 v = a + Complex.I * b := by
    rw [hGw.self_of_nhds v]
    simp [hJ0, a, b, dF, -stdForm_apply]
    ring
  have hab : a ^ 2 + b ^ 2 = 2 * G 0 v * (a - Complex.I * b) := by
    linear_combination b ^ 2 * Complex.I_sq - (a - Complex.I * b) * hG0
  have hp : 0 < ‖p‖ := norm_pos_iff.2 hF0
  have hJv : ‖J v‖ = ‖v‖ := norm_stdComplexStructure v
  have ha : ‖a‖ ≤ ‖dF‖ * ‖v‖ := dF.le_opNorm v
  have hb : ‖b‖ ≤ ‖dF‖ * ‖v‖ := hJv ▸ dF.le_opNorm (J v)
  have hsq : ‖a ^ 2 + b ^ 2‖ ≤ 4 * (‖G 0‖ * ‖dF‖) * ‖v‖ ^ 2 := by
    have hamb : ‖a - Complex.I * b‖ ≤ 2 * (‖dF‖ * ‖v‖) := by
      calc ‖a - Complex.I * b‖ ≤ ‖a‖ + ‖b‖ := by
            simpa using norm_sub_le a (Complex.I * b)
        _ ≤ 2 * (‖dF‖ * ‖v‖) := by linarith
    rw [hab, norm_mul, norm_mul, Complex.norm_two]
    have := (G 0).le_opNorm v
    calc 2 * ‖G 0 v‖ * ‖a - Complex.I * b‖ ≤ 2 * (‖G 0‖ * ‖v‖) * (2 * (‖dF‖ * ‖v‖)) := by
          gcongr
      _ = 4 * (‖G 0‖ * ‖dF‖) * ‖v‖ ^ 2 := by ring
  -- The error term coming from the derivatives of `G` and of `Jf`.
  have hE₁ : ‖E₁‖ ≤ (4 * ‖DG‖ + 2 * (‖DJ‖ * ‖dF‖)) * ‖v‖ ^ 2 := by
    have h₁ := DG.le_opNorm₂ v v
    have h₂ := DG.le_opNorm₂ (J v) (J v)
    have h₃ := dF.le_opNorm (DJ v v)
    have h₄ := dF.le_opNorm (DJ (J v) (J v))
    have h₅ := DJ.le_opNorm₂ v v
    have h₆ := DJ.le_opNorm₂ (J v) (J v)
    rw [hJv] at h₂ h₆
    have h₃' : ‖dF (DJ v v)‖ ≤ ‖dF‖ * (‖DJ‖ * ‖v‖ * ‖v‖) :=
      h₃.trans (mul_le_mul_of_nonneg_left h₅ (norm_nonneg _))
    have h₄' : ‖dF (DJ (J v) (J v))‖ ≤ ‖dF‖ * (‖DJ‖ * ‖v‖ * ‖v‖) :=
      h₄.trans (mul_le_mul_of_nonneg_left h₆ (norm_nonneg _))
    calc ‖E₁‖ ≤ ‖(2 : ℝ) • DG v v‖ + ‖(2 : ℝ) • DG (J v) (J v)‖ +
          ‖Complex.I * (dF (DJ v v) + dF (DJ (J v) (J v)))‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 2 * ‖DG v v‖ + 2 * ‖DG (J v) (J v)‖ +
          (‖dF (DJ v v)‖ + ‖dF (DJ (J v) (J v))‖) := by
          rw [norm_smul, norm_smul, norm_mul, Complex.norm_I, one_mul, Real.norm_two]
          gcongr
          exact norm_add_le _ _
      _ ≤ (4 * ‖DG‖ + 2 * (‖DJ‖ * ‖dF‖)) * ‖v‖ ^ 2 := by nlinarith
  -- Assemble the two Hessian terms.
  have hinner : inner ℝ p (h v v) + inner ℝ p (h (J v) (J v)) =
      inner ℝ p E₁ - ‖v‖ ^ 2 * ‖p‖ ^ 2 := by
    rw [← inner_add_right, hkey, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have halg := Complex.norm_sq_mul_add_sub_inner_sq_le p a b
  have hX : inner ℝ p E₁ ≤ ‖p‖ * ‖E₁‖ := real_inner_le_norm _ _
  rw [fderiv_fderiv_log_norm_sq_apply hF hF0, fderiv_fderiv_log_norm_sq_apply hF hF0,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hsplit : 2 * (‖a‖ ^ 2 + inner ℝ p (h v v)) / ‖p‖ ^ 2 - 4 * inner ℝ p a * inner ℝ p a /
        ‖p‖ ^ 4 + (2 * (‖b‖ ^ 2 + inner ℝ p (h (J v) (J v))) / ‖p‖ ^ 2 -
        4 * inner ℝ p b * inner ℝ p b / ‖p‖ ^ 4) =
      2 * (‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2)) /
          ‖p‖ ^ 4 + 2 * inner ℝ p E₁ / ‖p‖ ^ 2 - 2 * ‖v‖ ^ 2 := by
    have hadd : inner ℝ p (h (J v) (J v)) = inner ℝ p E₁ - ‖v‖ ^ 2 * ‖p‖ ^ 2 -
        inner ℝ p (h v v) := by linarith
    rw [hadd]
    field_simp
    ring
  rw [hsplit]
  have hT₁ : 2 * (‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2)) /
      ‖p‖ ^ 4 ≤ 8 * (‖G 0‖ * ‖dF‖ / ‖p‖ ^ 2) * ‖v‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc 2 * (‖p‖ ^ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) - 2 * (inner ℝ p a ^ 2 + inner ℝ p b ^ 2))
        ≤ 2 * (‖p‖ ^ 2 * (4 * (‖G 0‖ * ‖dF‖) * ‖v‖ ^ 2)) := by
          gcongr
          exact halg.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
      _ = 8 * (‖G 0‖ * ‖dF‖ / ‖p‖ ^ 2) * ‖v‖ ^ 2 * ‖p‖ ^ 4 := by
          field_simp
          ring
  have hT₂ : 2 * inner ℝ p E₁ / ‖p‖ ^ 2 ≤
      8 * (‖DG‖ / ‖p‖ + ‖DJ‖ * ‖dF‖ / ‖p‖) * ‖v‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h4 : 0 ≤ ‖DJ‖ * ‖dF‖ * ‖v‖ ^ 2 := by positivity
    calc 2 * inner ℝ p E₁ ≤ 2 * (‖p‖ * ((4 * ‖DG‖ + 2 * (‖DJ‖ * ‖dF‖)) * ‖v‖ ^ 2)) := by
          gcongr
          exact hX.trans (mul_le_mul_of_nonneg_left hE₁ hp.le)
      _ ≤ 8 * (‖DG‖ / ‖p‖ + ‖DJ‖ * ‖dF‖ / ‖p‖) * ‖v‖ ^ 2 * ‖p‖ ^ 2 := by
          field_simp
          nlinarith
  linarith

end SymplecticGeometry

end
