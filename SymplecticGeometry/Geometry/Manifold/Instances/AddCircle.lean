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
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# Polar coordinates on the circle `AddCircle p`

For a positive period `p`, the map `AddCircle p × ℝ → ℂ`, `(θ, r) ↦ r · toCircle θ`, writes a
complex number in polar coordinates, with angle `θ` and signed radius `r`. It is a smooth local
diffeomorphism at every point with `r ≠ 0`
(`AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`). The proof lifts it along the quotient map
`ℝ × ℝ → AddCircle p × ℝ`, a local diffeomorphism by Tau Ceti's
`AddCircle.isLocalDiffeomorph_prodMap_coe_id` with derivative the identity
(`AddCircle.mfderiv_prodMap_coe_id`),
to `(u, r) ↦ exp (2π u / p · i) · r`, whose derivative, by Tau Ceti's
`TauCeti.hasFDerivAt_circleExp_mul_ofReal`, is injective for `r ≠ 0`, and descends it
with Tau Ceti's inverse function theorem `TauCeti.isLocalDiffeomorphAt_of_eqOn_comp`. The same
lift gives, by the chain rule, the derivative of polar coordinates: at `(θ, r)` it sends `(a, b)`
to `(2π r a / p · i + b) · toCircle θ`. Their smoothness follows from that of `toCircle`
(`AddCircle.contMDiff_coe_toCircle`), Tau Ceti's `AddCircle.contMDiff_toCircle` read in `ℂ`.

## Main results

* `AddCircle.isLocalDiffeomorphAt_ofReal_mul_toCircle`: polar coordinates are a local
  diffeomorphism away from the radius `0`.
* `AddCircle.contMDiff_ofReal_mul_toCircle`: polar coordinates are smooth.
* `AddCircle.mfderiv_ofReal_mul_toCircle_apply`: the derivative of polar coordinates.
* `AddCircle.not_isInvertible_mfderiv_ofReal_mul_toCircle_zero`: that derivative is not invertible
  at the radius `0`.
* `AddCircle.contMDiff_coe_toCircle`: the map `toCircle : AddCircle p → ℂ` is smooth.
-/

public section

open Set Function Complex Real
open scoped Manifold ContDiff

namespace AddCircle

variable {p : ℝ} [hp : Fact (0 < p)] {n : WithTop ℕ∞}

omit hp in
variable (p) in
/-- Polar coordinates on `AddCircle p × ℝ`, lifted along the quotient map `ℝ × ℝ → AddCircle p × ℝ`,
are `(u, r) ↦ exp (2π u / p · i) · r`. -/
theorem ofReal_mul_toCircle_comp_prodMap_coe_id :
    (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) ∘
        Prod.map ((↑) : ℝ → AddCircle p) (id : ℝ → ℝ) =
      fun q : ℝ × ℝ ↦ (Circle.exp (2 * π / p * q.1) : ℂ) * (q.2 : ℂ) :=
  funext fun q ↦ by simp [toCircle_apply_mk, mul_comm]

/-- The lift of polar coordinates to `ℝ × ℝ` has injective derivative away from the radius `0`. -/
private theorem injective_fderiv_polarLift {x : ℝ × ℝ} (hx : x.2 ≠ 0) :
    Injective (fderiv ℝ
      (fun q : ℝ × ℝ ↦ (Circle.exp (2 * π / p * q.1) : ℂ) * (q.2 : ℂ)) x) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨a, b⟩ hv ↦ ?_
  rw [TauCeti.fderiv_circleExp_mul_ofReal_apply (hasFDerivAt_fst.const_mul (2 * π / p))
    hasFDerivAt_snd] at hv
  have hv' := (mul_eq_zero.1 hv).resolve_left (Circle.coe_ne_zero _)
  have hre : b = 0 := by simpa using congrArg Complex.re hv'
  have him : x.2 * (2 * π / p * a) = 0 := by simpa using congrArg Complex.im hv'
  have ha : a = 0 := by simpa [hx, Real.pi_ne_zero, hp.out.ne'] using him
  simp [ha, hre]

/-- The map `AddCircle p → ℂ`, `[t] ↦ exp (2π i t / p)`, given by `AddCircle.toCircle`, is smooth
of every order. -/
theorem contMDiff_coe_toCircle (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℂ) r fun x : AddCircle p ↦ (toCircle x : ℂ) := by
  have := finrank_real_complex_fact'
  exact contMDiff_coe_sphere.comp (contMDiff_toCircle p r)

variable (p n) in
/-- Polar coordinates `(θ, r) ↦ r · toCircle θ` on `AddCircle p × ℝ` are `C^n`. -/
theorem contMDiff_ofReal_mul_toCircle :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ) n
      (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) :=
  contDiff_mul.comp_contMDiff ((ofRealCLM.contMDiff.comp contMDiff_snd).prodMk_space
    ((contMDiff_coe_toCircle n).comp contMDiff_fst))

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
    (hasMFDerivAt_iff_hasFDerivAt.2 (TauCeti.hasFDerivAt_circleExp_mul_ofReal
      (hasFDerivAt_fst.const_mul (2 * π / p)) (hasFDerivAt_snd (p := (u, r))))).mfderiv,
    mfderiv_prodMap_coe_id] at h
  have h' := DFunLike.congr_fun h (a, b)
  -- The tangent space of `ℂ` is `ℂ` itself, so both sides are complex numbers.
  refine h'.symm.trans (α := ℂ) ?_
  -- Read the derivative of the lift as a map `ℝ × ℝ →L[ℝ] ℂ`.
  change (_ : ℝ × ℝ →L[ℝ] ℂ) (a, b) = _
  simp [toCircle_apply_mk, Circle.coe_exp]
  ring

/-- At the radius `0`, the derivative of polar coordinates is not invertible: it sends the angular
direction `(1, 0)` to `0`. -/
theorem not_isInvertible_mfderiv_ofReal_mul_toCircle_zero (θ : AddCircle p) :
    ¬ (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℂ)
        (fun q : AddCircle p × ℝ ↦ (q.2 : ℂ) * (toCircle q.1 : ℂ)) (θ, 0)).IsInvertible := by
  rintro ⟨e, he⟩
  have h := (DFunLike.congr_fun he (1, 0)).trans (mfderiv_ofReal_mul_toCircle_apply θ 0 1 0)
  simp only [mul_zero, zero_mul, ofReal_zero, add_zero] at h
  exact one_ne_zero (congrArg Prod.fst (e.map_eq_zero_iff.1 h))

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
    (κ := fun q : ℝ × ℝ ↦ (Circle.exp (2 * π / p * q.1) : ℂ) * (q.2 : ℂ)) ?_ ?_ ?_ ?_ hΨ
  · intro q _
    exact congrFun (ofReal_mul_toCircle_comp_prodMap_coe_id p) q
  · rw [← ofReal_mul_toCircle_comp_prodMap_coe_id]
    exact ((contMDiff_ofReal_mul_toCircle p ω).comp
      (isLocalDiffeomorph_prodMap_coe_id p ω).contMDiff).contMDiffOn
  · rw [mfderiv_eq_fderiv]
    exact injective_fderiv_polarLift hr
  · simp [finrank_real_complex]

end AddCircle
