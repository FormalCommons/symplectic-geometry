/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ModelDbar
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import SymplecticGeometry.Analysis.Calculus.FDeriv.LogNormSq

/-!
# The Hessian of `log |F|²` in a chart, in the directions `v` and `J₀ v`

Let `F : StdSpace ι → ℂ` be `C²` at `0` with `F 0 ≠ 0`, let `Jf` be a field of real-linear
endomorphisms of `StdSpace ι`, differentiable at `0` with `Jf 0 = J₀` the standard complex
structure, and let `G z` be the complex-antilinear part, for `Jf z` and multiplication by `i`,
of the covariant derivative `dF_z + i A₀(z) F z` of the model connection form
`A₀(z) w = -ω₀(z, w) / 2`: the model `∂̄` `SymplecticGeometry.modelDbarWith Jf F z`. This is
the shape of `SymplecticGeometry.RescaledUnitaryCharts.dbarReading`, with `Jf` in place of the
pushed-forward almost complex structure.

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

/-- The bound on the square terms: `‖2 g v (L v - i L (J₀ v))‖ ≤ 4 ‖g‖ ‖L‖ ‖v‖²`. -/
private theorem norm_two_mul_mul_sub_I_mul_le (g L : StdSpace ι →L[ℝ] ℂ) (v : StdSpace ι) :
    ‖2 * g v * (L v - Complex.I * L (stdComplexStructure ι v))‖ ≤
      4 * (‖g‖ * ‖L‖) * ‖v‖ ^ 2 := by
  have hb : ‖L (stdComplexStructure ι v)‖ ≤ ‖L‖ * ‖v‖ :=
    norm_stdComplexStructure v ▸ L.le_opNorm _
  have hamb : ‖L v - Complex.I * L (stdComplexStructure ι v)‖ ≤ 2 * (‖L‖ * ‖v‖) :=
    (norm_sub_le _ _).trans (by rw [norm_mul, Complex.norm_I, one_mul]; linarith [L.le_opNorm v])
  rw [norm_mul, norm_mul, Complex.norm_two]
  calc 2 * ‖g v‖ * ‖L v - Complex.I * L (stdComplexStructure ι v)‖ ≤
        2 * (‖g‖ * ‖v‖) * (2 * (‖L‖ * ‖v‖)) := by
        gcongr
        exact g.le_opNorm v
    _ = 4 * (‖g‖ * ‖L‖) * ‖v‖ ^ 2 := by ring

/-- The bound on the error term coming from the derivatives `DG` of `G` and `DJ` of `Jf`:
`‖2 DG(v, v) + 2 DG(J₀ v, J₀ v) - i (L (DJ(v, v)) + L (DJ(J₀ v, J₀ v)))‖` is at most
`(4 ‖DG‖ + 2 ‖DJ‖ ‖L‖) ‖v‖²`. -/
private theorem norm_two_smul_add_two_smul_sub_le (DG : StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℂ)
    (DJ : StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) (L : StdSpace ι →L[ℝ] ℂ)
    (v : StdSpace ι) :
    ‖(2 : ℝ) • DG v v + (2 : ℝ) • DG (stdComplexStructure ι v) (stdComplexStructure ι v) -
        Complex.I * (L (DJ v v) + L (DJ (stdComplexStructure ι v) (stdComplexStructure ι v)))‖ ≤
      (4 * ‖DG‖ + 2 * (‖DJ‖ * ‖L‖)) * ‖v‖ ^ 2 := by
  set J := stdComplexStructure ι
  have hJv : ‖J v‖ = ‖v‖ := norm_stdComplexStructure v
  have h₁ := DG.le_opNorm₂ v v
  have h₂ := DG.le_opNorm₂ (J v) (J v)
  have h₃ := (L.le_opNorm (DJ v v)).trans
    (mul_le_mul_of_nonneg_left (DJ.le_opNorm₂ v v) (norm_nonneg _))
  have h₄ := (L.le_opNorm (DJ (J v) (J v))).trans
    (mul_le_mul_of_nonneg_left (DJ.le_opNorm₂ (J v) (J v)) (norm_nonneg _))
  rw [hJv] at h₂ h₄
  calc _ ≤ 2 * ‖DG v v‖ + 2 * ‖DG (J v) (J v)‖ + (‖L (DJ v v)‖ + ‖L (DJ (J v) (J v))‖) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
        gcongr
        · exact (norm_add_le _ _).trans (by rw [norm_smul, norm_smul, Real.norm_two])
        · exact norm_add_le _ _
    _ ≤ (4 * ‖DG‖ + 2 * (‖DJ‖ * ‖L‖)) * ‖v‖ ^ 2 := by nlinarith

section

variable (hF : ContDiffAt ℝ 2 F 0) (hJ : DifferentiableAt ℝ Jf 0)
  (hJ0 : ∀ w, Jf 0 w = stdComplexStructure ι w) (hGd : DifferentiableAt ℝ G 0)
  (hG : ∀ᶠ z in 𝓝 0, G z = modelDbarWith Jf F z)

include hG

/-- The values of `G` written out: `2 G z w = L z w + i L z (Jf z w)` for
`L z w = dF_z w - (ω₀(z, w) / 2) • (i F z)`. -/
private theorem eventually_apply_eq :
    ∀ᶠ z in 𝓝 0, ∀ w, G z w = (2⁻¹ : ℝ) • (fderiv ℝ F z w -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z w) • (Complex.I * F z) +
      Complex.I * (fderiv ℝ F z (Jf z w) -
      (2⁻¹ * (stdForm ι).toBilinForm.toContinuousBilinearMap z (Jf z w)) •
        (Complex.I * F z))) := by
  filter_upwards [hG] with z hz w
  rw [hz, modelDbarWith_apply, modelConnection_apply, modelConnection_apply]
  simp [-stdForm_apply]

include hJ0

/-- `dF₀ v ^ 2 + dF₀ (J₀ v) ^ 2 = 2 G 0 v (dF₀ v - i dF₀ (J₀ v))`. -/
private theorem fderiv_apply_sq_add_sq_eq (v : StdSpace ι) :
    fderiv ℝ F 0 v ^ 2 + fderiv ℝ F 0 (stdComplexStructure ι v) ^ 2 =
      2 * G 0 v * (fderiv ℝ F 0 v - Complex.I * fderiv ℝ F 0 (stdComplexStructure ι v)) := by
  have hG0 : (2 : ℂ) * G 0 v =
      fderiv ℝ F 0 v + Complex.I * fderiv ℝ F 0 (stdComplexStructure ι v) := by
    rw [(eventually_apply_eq hG).self_of_nhds v]
    simp [hJ0, -stdForm_apply]
    ring
  linear_combination fderiv ℝ F 0 (stdComplexStructure ι v) ^ 2 * Complex.I_sq -
    (fderiv ℝ F 0 v - Complex.I * fderiv ℝ F 0 (stdComplexStructure ι v)) * hG0

include hF hJ hGd

/-- The derivative of `G` at `0`, in terms of the first two derivatives of `F` and the
derivative of `Jf`. -/
private theorem fderiv_apply_apply_eq (u w : StdSpace ι) :
    fderiv ℝ G 0 u w = (2⁻¹ : ℝ) • (fderiv ℝ (fderiv ℝ F) 0 u w -
      (2⁻¹ * stdForm ι u w) • (Complex.I * F 0) +
      Complex.I * (fderiv ℝ (fderiv ℝ F) 0 u (stdComplexStructure ι w) +
        fderiv ℝ F 0 (fderiv ℝ Jf 0 u w) -
        (2⁻¹ * stdForm ι u (stdComplexStructure ι w)) • (Complex.I * F 0))) := by
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set B := (stdForm ι).toBilinForm.toContinuousBilinearMap
  rw [← fderiv_clm_apply_const_apply hGd w u,
    Filter.EventuallyEq.fderiv_eq (f₁ := fun z ↦ G z w)
      ((eventually_apply_eq hG).mono fun z hz ↦ hz w)]
  have hJw := hJ.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)
  have hB₁ := B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : StdSpace ι))
    (hasFDerivAt_const w 0)
  have hB₂ := B.hasFDerivAt_of_bilinear (hasFDerivAt_id (0 : StdSpace ι)) hJw
  have hIF := (hF.differentiableAt (by norm_num)).hasFDerivAt.const_mul Complex.I
  have hΦ : HasFDerivAt (fun z ↦ (2⁻¹ : ℝ) • (fderiv ℝ F z w - (2⁻¹ * B z w) • (Complex.I * F z) +
      Complex.I * (fderiv ℝ F z (Jf z w) - (2⁻¹ * B z (Jf z w)) • (Complex.I * F z)))) _ 0 :=
    (((hF2.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)).sub
      ((hB₁.const_mul 2⁻¹).smul hIF)).add (((hF2.hasFDerivAt.clm_apply hJw).sub
        ((hB₂.const_mul 2⁻¹).smul hIF)).const_mul Complex.I)).const_smul (2⁻¹ : ℝ)
  rw [hΦ.fderiv]
  simp [B, hJ0, -stdForm_apply]
  ring

/-- The `J₀`-symmetrized second derivative of `F` at `0`, read off the derivative of `G`: it is
`2 dG₀(v, v) + 2 dG₀(J₀ v, J₀ v) - i (dF₀ (dJf₀(v, v)) + dF₀ (dJf₀(J₀ v, J₀ v))) - ‖v‖² F 0`. -/
private theorem fderiv_fderiv_apply_add_stdComplexStructure_eq (v : StdSpace ι) :
    fderiv ℝ (fderiv ℝ F) 0 v v +
        fderiv ℝ (fderiv ℝ F) 0 (stdComplexStructure ι v) (stdComplexStructure ι v) =
      (2 : ℝ) • fderiv ℝ G 0 v v +
          (2 : ℝ) • fderiv ℝ G 0 (stdComplexStructure ι v) (stdComplexStructure ι v) -
        Complex.I * (fderiv ℝ F 0 (fderiv ℝ Jf 0 v v) +
          fderiv ℝ F 0 (fderiv ℝ Jf 0 (stdComplexStructure ι v) (stdComplexStructure ι v))) -
        (‖v‖ ^ 2 : ℝ) • F 0 := by
  set J := stdComplexStructure ι
  have hsym : fderiv ℝ (fderiv ℝ F) 0 (J v) v = fderiv ℝ (fderiv ℝ F) 0 v (J v) :=
    (hF.isSymmSndFDerivAt (by simp)) _ _
  have hω : stdForm ι v (J v) = ‖v‖ ^ 2 := by
    rw [stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq]
  have hω' : stdForm ι (J v) (J (J v)) = ‖v‖ ^ 2 := by
    rw [stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq, norm_stdComplexStructure]
  rw [fderiv_apply_apply_eq hF hJ hJ0 hGd hG v v,
    fderiv_apply_apply_eq hF hJ hJ0 hGd hG (J v) (J v), hω, hω', (stdForm ι).self_eq_zero,
    (stdForm ι).self_eq_zero, J.apply_apply, map_neg]
  simp only [Complex.real_smul]
  push_cast
  linear_combination Complex.I * hsym + F 0 * (‖v‖ : ℂ) ^ 2 * Complex.I_sq

/-- **The Hessian of `log |F|²` in the directions `v` and `J₀ v`, in a chart.** Let
`F : StdSpace ι → ℂ` be `C²` at `0` with `F 0 ≠ 0`, let `Jf` be differentiable at `0` with
`Jf 0 = J₀`, and let `G` agree near `0` with `SymplecticGeometry.modelDbarWith Jf F`, the
complex-antilinear part, for `Jf z` and multiplication by `i`, of
`dF_z - (ω₀(z, ·) / 2) • (i F z)`; let `G` be differentiable at `0`. Then the second
derivative `H` of `z ↦ log (‖F z‖ ^ 2)` at `0` satisfies
`H(v, v) + H(J₀ v, J₀ v) ≤ (-2 + 8 ε) ‖v‖²` for every `v`, where
`ε = ‖dG₀‖ / ‖F 0‖ + ‖dJf₀‖ ‖dF₀‖ / ‖F 0‖ + ‖G 0‖ ‖dF₀‖ / ‖F 0‖²`. -/
theorem fderiv_fderiv_log_norm_sq_add_stdComplexStructure_le (hF0 : F 0 ≠ 0)
    (v : StdSpace ι) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) 0 v v +
        fderiv ℝ (fderiv ℝ fun z ↦ Real.log (‖F z‖ ^ 2)) 0 (stdComplexStructure ι v)
          (stdComplexStructure ι v) ≤
      (-2 + 8 * (‖fderiv ℝ G 0‖ / ‖F 0‖ + ‖fderiv ℝ Jf 0‖ * ‖fderiv ℝ F 0‖ / ‖F 0‖ +
        ‖G 0‖ * ‖fderiv ℝ F 0‖ / ‖F 0‖ ^ 2)) * ‖v‖ ^ 2 := by
  have hkey := fderiv_fderiv_apply_add_stdComplexStructure_eq hF hJ hJ0 hGd hG v
  have hab := fderiv_apply_sq_add_sq_eq hJ0 hG v
  refine (fderiv_fderiv_log_norm_sq_add_le hF hF0 v _).trans ?_
  rw [hkey, hab]
  have hp : 0 < ‖F 0‖ := norm_pos_iff.2 hF0
  have hsq := norm_two_mul_mul_sub_I_mul_le (G 0) (fderiv ℝ F 0) v
  have hX := (real_inner_le_norm (F 0) _).trans (mul_le_mul_of_nonneg_left
    (norm_two_smul_add_two_smul_sub_le (fderiv ℝ G 0) (fderiv ℝ Jf 0) (fderiv ℝ F 0) v) hp.le)
  set p := F 0
  set dF := fderiv ℝ F 0
  set DG := fderiv ℝ G 0
  set DJ := fderiv ℝ Jf 0
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    ← add_div, div_le_iff₀ (by positivity)]
  have h4 : 0 ≤ ‖DJ‖ * ‖dF‖ * ‖v‖ ^ 2 := by positivity
  have key : (-2 + 8 * (‖DG‖ / ‖p‖ + ‖DJ‖ * ‖dF‖ / ‖p‖ + ‖G 0‖ * ‖dF‖ / ‖p‖ ^ 2)) * ‖v‖ ^ 2 *
      ‖p‖ ^ 2 = -2 * ‖v‖ ^ 2 * ‖p‖ ^ 2 + 8 * ‖p‖ * (‖DG‖ + ‖DJ‖ * ‖dF‖) * ‖v‖ ^ 2 +
        8 * (‖G 0‖ * ‖dF‖) * ‖v‖ ^ 2 := by
    field_simp
    ring
  rw [key]
  nlinarith

end

end SymplecticGeometry

end
