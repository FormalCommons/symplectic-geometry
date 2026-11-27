/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import SymplecticGeometry.Analysis.Calculus.IteratedDeriv.Support
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic

/-!
# Improper integrals of iterated derivatives on a half-line

For `F : ℝ → ℝ` of class `C^(k+1)` with compact support,
`∫₀^∞ s ^ k / k! * F⁽ᵏ⁺¹⁾ (-s) ds = F 0`
(`MeasureTheory.integral_Ioi_pow_div_factorial_mul_iteratedDeriv_neg`).

The proof is by induction on `k`. The case `k = 0` is the fundamental theorem of calculus on a
half-line, Mathlib's `HasCompactSupport.integral_Ioi_deriv_eq`, and each further step is an
integration by parts, Mathlib's `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`. The identity
is Taylor's formula with integral remainder (Mathlib's `taylor_integral_remainder`) expanded at a
point to the left of the support of `F`.
-/

public section

open Set Filter Topology

namespace MeasureTheory

variable {F : ℝ → ℝ}

/-- For `F` of class `C^(k+1)` with compact support,
`∫₀^∞ s ^ k / k! * F⁽ᵏ⁺¹⁾ (-s) ds = F 0`. -/
theorem integral_Ioi_pow_div_factorial_mul_iteratedDeriv_neg {k : ℕ} (hF : ContDiff ℝ (k + 1) F)
    (hFc : HasCompactSupport F) :
    ∫ s in Ioi 0, s ^ k / k.factorial * iteratedDeriv (k + 1) F (-s) = F 0 := by
  induction k with
  | zero =>
    have hG : ContDiff ℝ 1 fun s ↦ F (-s) := (hF.comp contDiff_neg).of_le (by simp)
    have hGc : HasCompactSupport fun s ↦ F (-s) :=
      hFc.comp_isClosedEmbedding (Homeomorph.neg ℝ).isClosedEmbedding
    have := hGc.integral_Ioi_deriv_eq hG 0
    simp only [deriv_comp_neg, integral_neg, neg_zero, neg_inj] at this
    simpa using this
  | succ k ih =>
    have hc : Continuous (iteratedDeriv (k + 1) F) :=
      hF.continuous_iteratedDeriv _ (by norm_cast; omega)
    have hc' : Continuous (iteratedDeriv (k + 2) F) :=
      hF.continuous_iteratedDeriv _ (by norm_cast)
    have hd (s : ℝ) : HasDerivAt (iteratedDeriv (k + 1) F) (iteratedDeriv (k + 2) F s) s :=
      hF.hasDerivAt_iteratedDeriv (by norm_cast; omega) s
    let u : ℝ → ℝ := fun s ↦ s ^ (k + 1) / (k + 1).factorial
    let v : ℝ → ℝ := fun s ↦ -iteratedDeriv (k + 1) F (-s)
    have hu : ∀ s, HasDerivAt u (s ^ k / k.factorial) s := by
      intro s
      convert (hasDerivAt_pow (k + 1) s).div_const ((k + 1).factorial : ℝ) using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have hv : ∀ s, HasDerivAt v (iteratedDeriv (k + 2) F (-s)) s := by
      intro s
      convert ((hd (-s)).comp s (hasDerivAt_neg s)).neg using 1
      · -- `v` is `-(F⁽ᵏ⁺¹⁾ ∘ Neg.neg)` by its definition.
        rfl
      · ring
    have hcpt (m : ℕ) : HasCompactSupport fun s ↦ iteratedDeriv m F (-s) :=
      (hFc.iteratedDeriv m).comp_isClosedEmbedding (Homeomorph.neg ℝ).isClosedEmbedding
    have huc : Continuous u := by fun_prop
    have hu'c : Continuous fun s : ℝ ↦ s ^ k / k.factorial := by fun_prop
    have huv' : IntegrableOn (u * fun s ↦ iteratedDeriv (k + 2) F (-s)) (Ioi 0) :=
      ((huc.mul (hc'.comp continuous_neg)).integrable_of_hasCompactSupport
        (hcpt _).mul_left).integrableOn
    have hu'v : IntegrableOn ((fun s : ℝ ↦ s ^ k / k.factorial) * v) (Ioi 0) :=
      ((hu'c.mul (hc.comp continuous_neg).neg).integrable_of_hasCompactSupport
        (hcpt _).neg.mul_left).integrableOn
    have huvc : Continuous (u * v) := huc.mul (hc.comp continuous_neg).neg
    have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
      have := (huvc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [u, v] using this
    have hinf : Tendsto (u * v) atTop (𝓝 0) :=
      ((hcpt (k + 1)).neg.mul_left (f := u)).is_zero_at_infty.mono_left atTop_le_cocompact
    have := integral_Ioi_mul_deriv_eq_deriv_mul (fun s _ ↦ hu s) (fun s _ ↦ hv s) huv' hu'v h0
      hinf
    simp only [sub_self, zero_sub, u, v, mul_neg, integral_neg, neg_neg] at this
    rw [this, ih (hF.of_le (by norm_cast; omega))]

end MeasureTheory

end
