/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Manifold.Instances.AddCircle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Polar coordinates on the circle `AddCircle p`

For a positive period `p`, the map `AddCircle p × ℝ → ℂ`, `(θ, r) ↦ r · toCircle θ`, writes a
complex number in polar coordinates, with angle `θ` and signed radius `r`. It is a smooth local
diffeomorphism at every point with `r ≠ 0`
(`AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`). The proof lifts it along the quotient map
`ℝ × ℝ → AddCircle p × ℝ`, a local diffeomorphism by Tau Ceti's `AddCircle.isLocalDiffeomorph_coe`,
to `(u, r) ↦ r · exp (2π u / p · i)`, whose derivative is injective for `r ≠ 0`, and descends it
with Tau Ceti's inverse function theorem `TauCeti.isLocalDiffeomorphAt_of_eqOn_comp`.

## Main results

* `AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`: polar coordinates are a local
  diffeomorphism away from the radius `0`.
* `AddCircle.contMDiff_toCircle`: the map `toCircle : AddCircle p → ℂ` is smooth.
-/

public section

open Set Function Complex Real
open scoped Manifold ContDiff

namespace AddCircle

variable {p : ℝ} [hp : Fact (0 < p)] {n : WithTop ℕ∞}

/-- The lift of polar coordinates to `ℝ × ℝ` has injective derivative away from the radius `0`. -/
private theorem injective_fderiv_polarLift {x : ℝ × ℝ} (hx : x.2 ≠ 0) :
    Injective (fderiv ℝ
      (fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I)) x) := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ ↦ (q.2 : ℂ))
      (ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    ofRealCLM.hasFDerivAt.comp x hasFDerivAt_snd
  have h2 : HasFDerivAt (fun q : ℝ × ℝ ↦ ((2 * π / p * q.1 : ℝ) : ℂ) * I)
      (I • ofRealCLM.comp ((2 * π / p) • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_fst.const_mul (2 * π / p))).mul_const I
  have h3 : HasFDerivAt
      (fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I)) _ x :=
    h1.mul h2.cexp
  rw [h3.fderiv, injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hv
  have he := Complex.exp_ne_zero ((2 * π / p * x.1 : ℝ) * I)
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ofRealCLM_apply,
    smul_eq_mul] at hv
  have hv' : (b : ℂ) + (x.2 : ℂ) * ((2 * π / p * a : ℝ) * I) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left he
    rw [← hv]
    push_cast
    ring
  have hre : b = 0 := by simpa using congrArg Complex.re hv'
  have him : x.2 * (2 * π / p * a) = 0 := by simpa using congrArg Complex.im hv'
  have ha : a = 0 := by simpa [hx, Real.pi_ne_zero, hp.out.ne'] using him
  simp [ha, hre]

/-- **Polar coordinates.** For a positive period `p`, the map `(θ, r) ↦ r · toCircle θ` from
`AddCircle p × ℝ` to `ℂ` is a `C^n` local diffeomorphism at every point with `r ≠ 0`. -/
theorem isLocalDiffeomorphAt_ofReal_mul_toCircle {θ : AddCircle p} {r : ℝ} (hr : r ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) n
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) := by
  refine IsLocalDiffeomorphAt.of_le ?_ (le_top : n ≤ ω)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hΨ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ω
      (Prod.map ((↑) : ℝ → AddCircle p) id) (u, r) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (isLocalDiffeomorph_coe p ω u).prodMap
      (isLocalDiffeomorph_id r)
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn_comp (s := univ) (x := (u, r)) isOpen_univ trivial
    BoundarylessManifold.isInteriorPoint le_top
    (κ := fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I)) ?_ ?_ ?_ ?_ hΨ
  · intro q _
    simp [toCircle_apply_mk, Circle.coe_exp]
  · refine ContMDiff.contMDiffOn ?_
    rw [contMDiff_iff_contDiff]
    exact (ofRealCLM.contDiff.comp contDiff_snd).mul
      ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const).cexp
  · rw [mfderiv_eq_fderiv]
    exact injective_fderiv_polarLift hr
  · simp [finrank_real_complex]

/-- The map `AddCircle p → ℂ`, `[t] ↦ exp (2π i t / p)`, given by `AddCircle.toCircle`, is smooth
of every order. -/
theorem contMDiff_toCircle (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) r fun x : AddCircle p ↦ (toCircle x : ℂ) := by
  rw [← (isLocalDiffeomorph_coe p r).contMDiff_comp_iff QuotientAddGroup.mk_surjective le_rfl]
  have h : (fun x : AddCircle p ↦ (toCircle x : ℂ)) ∘ ((↑) : ℝ → AddCircle p) =
      fun t ↦ Complex.exp (((2 * π / p * t : ℝ) : ℂ) * Complex.I) :=
    funext fun t ↦ by rw [comp_apply, toCircle_apply_mk, Circle.coe_exp]
  rw [h]
  exact ContDiff.contMDiff (Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const))

end AddCircle
