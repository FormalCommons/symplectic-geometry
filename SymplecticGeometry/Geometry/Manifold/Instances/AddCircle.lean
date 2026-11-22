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
import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

/-!
# Polar coordinates on the circle `AddCircle p`

For a positive period `p`, the map `AddCircle p × ℝ → ℂ`, `(θ, r) ↦ r · toCircle θ`, writes a
complex number in polar coordinates, with angle `θ` and signed radius `r`. It is a smooth local
diffeomorphism at every point with `r ≠ 0`
(`AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`). The proof lifts it along the quotient map
`ℝ × ℝ → AddCircle p × ℝ`, a local diffeomorphism by Tau Ceti's
`AddCircle.isLocalDiffeomorph_prodMap_coe_id` with derivative the identity
(`AddCircle.mfderiv_prodMap_coe_id`),
to `(u, r) ↦ r · exp (2π u / p · i)`, whose derivative is injective for `r ≠ 0`, and descends it
with Tau Ceti's inverse function theorem `TauCeti.isLocalDiffeomorphAt_of_eqOn_comp`. The same
lift gives the smoothness of polar coordinates and, by the chain rule, their derivative: at
`(θ, r)` it sends `(a, b)` to `(2π r a / p · i + b) · toCircle θ`.

## Main results

* `AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`: polar coordinates are a local
  diffeomorphism away from the radius `0`.
* `AddCircle.contMDiff_ofReal_mul_toCircle`: polar coordinates are smooth.
* `AddCircle.mfderiv_ofReal_mul_toCircle_apply`: the derivative of polar coordinates.
-/

public section

open Set Function Complex Real
open scoped Manifold ContDiff

namespace AddCircle

variable {p : ℝ} [hp : Fact (0 < p)] {n : WithTop ℕ∞}

omit hp in
variable (p) in
/-- Polar coordinates on `AddCircle p × ℝ`, lifted along the quotient map `ℝ × ℝ → AddCircle p × ℝ`,
are `(u, r) ↦ r · exp (2π u / p · i)`. -/
theorem ofReal_mul_toCircle_comp_prodMap_coe_id :
    (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ∘
        Prod.map ((↑) : ℝ → AddCircle p) (id : ℝ → ℝ) =
      fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I) :=
  funext fun q ↦ by simp [toCircle_apply_mk, Circle.coe_exp]

omit hp in
variable (p) in
/-- The derivative of `(u, r) ↦ r · exp (2π u / p · i)` at `x` sends `(a, b)` to
`a · (2π x.2 / p · i) · exp (2π x.1 / p · i) + b · exp (2π x.1 / p · i)`. -/
theorem hasFDerivAt_ofReal_mul_exp (x : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (((2 * π / p * x.2 : ℝ) : ℂ) * I * exp ((2 * π / p * x.1 : ℝ) * I)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (exp ((2 * π / p * x.1 : ℝ) * I))) x := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ ↦ (q.2 : ℂ))
      (ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    ofRealCLM.hasFDerivAt.comp x hasFDerivAt_snd
  have h2 : HasFDerivAt (fun q : ℝ × ℝ ↦ ((2 * π / p * q.1 : ℝ) : ℂ) * I)
      (I • ofRealCLM.comp ((2 * π / p) • ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
    (ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_fst.const_mul (2 * π / p))).mul_const I
  refine (h1.mul h2.cexp).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun ⟨a, b⟩ ↦ ?_
  simp
  ring

/-- The lift of polar coordinates to `ℝ × ℝ` has injective derivative away from the radius `0`. -/
private theorem injective_fderiv_polarLift {x : ℝ × ℝ} (hx : x.2 ≠ 0) :
    Injective (fderiv ℝ
      (fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I)) x) := by
  rw [(hasFDerivAt_ofReal_mul_exp p x).fderiv, injective_iff_map_eq_zero]
  rintro ⟨a, b⟩ hv
  have he := Complex.exp_ne_zero ((2 * π / p * x.1 : ℝ) * I)
  have hv' : (b : ℂ) + (x.2 : ℂ) * ((2 * π / p * a : ℝ) * I) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left he
    rw [← hv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', real_smul]
    push_cast
    ring
  have hre : b = 0 := by simpa using congrArg Complex.re hv'
  have him : x.2 * (2 * π / p * a) = 0 := by simpa using congrArg Complex.im hv'
  have ha : a = 0 := by simpa [hx, Real.pi_ne_zero, hp.out.ne'] using him
  simp [ha, hre]

variable (p n) in
/-- Polar coordinates `(θ, r) ↦ r · toCircle θ` on `AddCircle p × ℝ` are `C^n`. -/
theorem contMDiff_ofReal_mul_toCircle :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) n
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) := by
  refine ContMDiff.of_le ?_ (le_top : n ≤ ω)
  rw [← (isLocalDiffeomorph_prodMap_coe_id p ω).contMDiff_comp_iff
    (QuotientAddGroup.mk_surjective.prodMap surjective_id) le_rfl,
    ofReal_mul_toCircle_comp_prodMap_coe_id, contMDiff_iff_contDiff]
  exact (ofRealCLM.contDiff.comp contDiff_snd).mul
    ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const).cexp

/-- **The derivative of polar coordinates.** At `(θ, r)`, the derivative of
`(θ, r) ↦ r · toCircle θ` sends `(a, b)` to `(2π r a / p · i + b) · toCircle θ`. -/
theorem mfderiv_ofReal_mul_toCircle_apply (θ : AddCircle p) (r a b : ℝ) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ))
        (θ, r) (a, b) =
      (((2 * π / p * r * a : ℝ) : ℂ) * I + (b : ℂ)) * (toCircle θ : ℂ) := by
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have h := (isLocalDiffeomorph_prodMap_coe_id p 1 (u, r)).mfderiv_comp one_ne_zero (I' := 𝓘(ℝ, ℂ))
    (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ))
  rw [ofReal_mul_toCircle_comp_prodMap_coe_id,
    (hasMFDerivAt_iff_hasFDerivAt.2 (hasFDerivAt_ofReal_mul_exp p (u, r))).mfderiv,
    mfderiv_prodMap_coe_id] at h
  have h' := DFunLike.congr_fun h (a, b)
  -- The tangent space of `ℂ` is `ℂ` itself, so both sides are complex numbers.
  refine h'.symm.trans (α := ℂ) ?_
  -- Read the derivative of the lift as a map `ℝ × ℝ →L[ℝ] ℂ`.
  change (_ : ℝ × ℝ →L[ℝ] ℂ) (a, b) = _
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', real_smul, toCircle_apply_mk, Circle.coe_exp]
  push_cast
  ring

/-- **Polar coordinates.** For a positive period `p`, the map `(θ, r) ↦ r · toCircle θ` from
`AddCircle p × ℝ` to `ℂ` is a `C^n` local diffeomorphism at every point with `r ≠ 0`. -/
theorem isLocalDiffeomorphAt_ofReal_mul_toCircle {θ : AddCircle p} {r : ℝ} (hr : r ≠ 0) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) n
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, r) := by
  refine IsLocalDiffeomorphAt.of_le ?_ (le_top : n ≤ ω)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hΨ := isLocalDiffeomorph_prodMap_coe_id p ω (u, r)
  refine TauCeti.isLocalDiffeomorphAt_of_eqOn_comp (s := univ) (x := (u, r)) isOpen_univ trivial
    BoundarylessManifold.isInteriorPoint le_top
    (κ := fun q : ℝ × ℝ ↦ (q.2 : ℂ) * exp ((2 * π / p * q.1 : ℝ) * I)) ?_ ?_ ?_ ?_ hΨ
  · intro q _
    exact (congrFun (ofReal_mul_toCircle_comp_prodMap_coe_id p) q).symm
  · rw [← ofReal_mul_toCircle_comp_prodMap_coe_id]
    exact ((contMDiff_ofReal_mul_toCircle p ω).comp
      (isLocalDiffeomorph_prodMap_coe_id p ω).contMDiff).contMDiffOn
  · rw [mfderiv_eq_fderiv]
    exact injective_fderiv_polarLift hr
  · simp [finrank_real_complex]

end AddCircle
