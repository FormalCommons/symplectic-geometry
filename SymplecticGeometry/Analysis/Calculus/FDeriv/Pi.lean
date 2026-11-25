/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# Rescaling the coordinates of `ι → ℝ`

For functions `bᵢ` on `ι → ℝ`, this file studies the map `z ↦ (zᵢ bᵢ(z))ᵢ`, which multiplies each
coordinate by a function of the point. When `bᵢ = a ^ pᵢ` for a smooth function `a` positive at
the origin, this map is a local diffeomorphism at the origin that fixes it.

## Main results

* `SymplecticGeometry.hasFDerivAt_pi_mul_zero`: at the origin, the derivative of
  `z ↦ (zᵢ bᵢ(z))ᵢ` is the diagonal map `v ↦ (bᵢ(0) vᵢ)ᵢ`.
* `SymplecticGeometry.contDiffOn_pi_mul_rpow`: the map `z ↦ (zᵢ a(z) ^ pᵢ)ᵢ` is as smooth as `a`
  where `a > 0`.
* `SymplecticGeometry.exists_openPartialHomeomorph_pi_mul_rpow`: if `a` is smooth and
  `a(0) > 0`, the map `z ↦ (zᵢ a(z) ^ pᵢ)ᵢ` is a local diffeomorphism at the origin, by Tau Ceti's
  inverse function theorem `TauCeti.ContDiffOn.exists_openPartialHomeomorph`.
-/

public section

open Set
open scoped ContDiff

namespace SymplecticGeometry


/-- At the origin, the map `z ↦ (zᵢ bᵢ(z))ᵢ` has as derivative the diagonal map
`v ↦ (bᵢ(0) vᵢ)ᵢ`, when each `bᵢ` is differentiable at `0`. -/
theorem hasFDerivAt_pi_mul_zero {ι : Type*} [Finite ι] {b : ι → (ι → ℝ) → ℝ}
    (hb : ∀ i, DifferentiableAt ℝ (b i) 0) :
    HasFDerivAt (fun z i ↦ z i * b i z)
      (ContinuousLinearMap.pi fun i ↦
        b i 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) 0 := by
  have := Fintype.ofFinite ι
  refine hasFDerivAt_pi'.2 fun i ↦ ?_
  refine (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt
    (x := 0)).mul (hb i).hasFDerivAt).congr_fderiv ?_
  ext v
  simp [mul_comm]

/-- For `a` of class `C^n`, the map `z ↦ (zᵢ a(z) ^ pᵢ)ᵢ` is of class `C^n` where `a > 0`. -/
theorem contDiffOn_pi_mul_rpow {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {a : (ι → ℝ) → ℝ}
    (ha : ContDiff ℝ n a) (p : ι → ℝ) :
    ContDiffOn ℝ n (fun z i ↦ z i * a z ^ p i) {z | 0 < a z} :=
  contDiffOn_pi.2 fun i ↦ (contDiff_apply ℝ (fun _ ↦ ℝ) i).contDiffOn.mul
    (ha.contDiffOn.rpow_const_of_ne fun _ hz ↦ hz.ne')

/-- If `a` is of class `C^n`, `n ≥ 1`, and `a(0) > 0`, then the map `z ↦ (zᵢ a(z) ^ pᵢ)ᵢ` is a
`C^n` diffeomorphism from an open neighbourhood of `0`, on which `a > 0`, onto an open set. -/
theorem exists_openPartialHomeomorph_pi_mul_rpow {ι : Type*} [Fintype ι] {n : WithTop ℕ∞}
    {a : (ι → ℝ) → ℝ} (ha : ContDiff ℝ n a) (hn : 1 ≤ n) (ha0 : 0 < a 0) (p : ι → ℝ) :
    ∃ Θ : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ), (Θ : (ι → ℝ) → ι → ℝ) =
      (fun z i ↦ z i * a z ^ p i) ∧ 0 ∈ Θ.source ∧ Θ.source ⊆ {z | 0 < a z} ∧
      ContDiffOn ℝ n Θ Θ.source ∧ ContDiffOn ℝ n Θ.symm Θ.target := by
  have hp0 : ∀ i, a 0 ^ p i ≠ 0 := fun i ↦ (Real.rpow_pos_of_pos ha0 _).ne'
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hD := hasFDerivAt_pi_mul_zero (b := fun i z ↦ a z ^ p i) fun i ↦
    (ha.differentiable hn0 0).rpow_const (.inl ha0.ne')
  have hW := contDiffOn_pi_mul_rpow ha p
  obtain ⟨Θ, hΘ, h0Θ, hΘS, hΘsymm⟩ := TauCeti.ContDiffOn.exists_openPartialHomeomorph hW
    (isOpen_lt continuous_const ha.continuous) ha0 hn
    (e := ContinuousLinearEquiv.piCongrRight fun i ↦
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (hp0 i)))
    (by rw [hD.fderiv]; ext v i; simp [mul_comm])
  exact ⟨Θ, hΘ, h0Θ, hΘS, hΘ ▸ hW.mono hΘS, hΘsymm⟩

end SymplecticGeometry

end
