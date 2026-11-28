/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Surjectivity of real-linear maps with dominant complex-linear part

Let `W` be a complex normed space of dimension one and let `A, B : V →L[ℝ] W` be real-linear maps
from a real normed space, such that `A` commutes and `B` anticommutes with a map `J` on `V` and
multiplication by `i` on `W`. If `‖B‖ < ‖A‖`, then `A + B` is surjective. No symplectic form
or inner product is involved, the norm on `V` is arbitrary, and the file imports only Mathlib.

The same statement for Tau Ceti's almost complex structures is in
`SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart.AlmostComplex`, and the kernel and
orientation statements, which need a symplectic form and a compatible inner product, are in
`SymplecticGeometry.LinearAlgebra.Complex.DominantLinearPart.Symplectic`.

## Main results

* `ContinuousLinearMap.surjective_add_of_norm_lt`: for any norm on `V`, any map
  `J : V → V`, and `A, B : V →L[ℝ] W` to a complex line `W` with `A (J v) = i • A v`,
  `B (J v) = -(i • B v)` and `‖B‖ < ‖A‖`, the sum `A + B` is surjective. Pick `v` with
  `‖B v‖ < ‖A v‖`; then `z ↦ (A + B) (re z • v + im z • J v)` is `z ↦ z • A v + conj z • B v`,
  which is injective, hence bijective from `ℂ` onto `W`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §7.4.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

noncomputable section

open Module Complex

namespace ContinuousLinearMap

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W]

/-- **A real-linear map to a complex line with dominant complex-linear part is surjective, for
any norm.** Let `V` be a real normed space with a map `J : V → V`, let `W` be a complex normed
space of dimension one, and let `A, B : V →L[ℝ] W` satisfy `A (J v) = i • A v` and
`B (J v) = -(i • B v)`, with `‖B‖ < ‖A‖`. Then `A + B` is surjective. -/
theorem surjective_add_of_norm_lt (hW : finrank ℂ W = 1) {J : V → V} {A B : V →L[ℝ] W}
    (hA : ∀ v, A (J v) = I • A v) (hB : ∀ v, B (J v) = -(I • B v)) (h : ‖B‖ < ‖A‖) :
    Function.Surjective (A + B) := by
  obtain ⟨v, hv1, hv⟩ := A.exists_lt_apply_of_lt_opNorm h
  have hb : ‖B v‖ < ‖A v‖ :=
    (B.le_opNorm v).trans_lt ((mul_le_of_le_one_right (norm_nonneg _) hv1.le).trans_lt hv)
  -- The real-linear map `z ↦ re z • v + im z • J v` from `ℂ` to `V`.
  set g : ℂ →ₗ[ℝ] V := reLm.smulRight v + imLm.smulRight (J v)
  have hφ (z : ℂ) : (A + B) (g z) = z • A v + (starRingEnd ℂ z) • B v := by
    conv_rhs => rw [← re_add_im z]
    simp only [g, LinearMap.add_apply, LinearMap.smulRight_apply, reLm_coe, imLm_coe, add_apply,
      map_add, map_smul, hA, hB, map_mul, conj_ofReal, conj_I]
    module
  have hinj : Function.Injective ((A + B : V →L[ℝ] W).toLinearMap ∘ₗ g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [LinearMap.comp_apply, coe_coe, hφ, add_eq_zero_iff_eq_neg] at hz
    have hn := congrArg norm hz
    rw [norm_neg, norm_smul, norm_smul, Complex.norm_conj] at hn
    by_contra hz0
    exact hb.ne' (mul_left_cancel₀ (norm_ne_zero_iff.2 hz0) hn)
  have : FiniteDimensional ℂ W := Module.finite_of_finrank_eq_succ hW
  have : FiniteDimensional ℝ W := .trans ℝ ℂ W
  have hdim : finrank ℝ ℂ = finrank ℝ W := by
    rw [← Module.finrank_mul_finrank ℝ ℂ W, hW, mul_one]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  rw [LinearMap.coe_comp] at hsurj
  exact hsurj.of_comp

end ContinuousLinearMap
