/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Products of continuous linear endomorphisms

Two continuous linear endomorphisms `f` of `M` and `g` of `N` give the endomorphism
`f.prodMap g` of `M × N`. This map from the product algebra is an algebra homomorphism,
`ContinuousLinearMap.prodMapAlgHom`, the continuous analogue of Mathlib's
`LinearMap.prodMapAlgHom`. On normed spaces it is Mathlib's `ContinuousLinearMap.prodMapL`, so
it is continuous and commutes with the exponential.

## Main results

* `ContinuousLinearMap.prodMapAlgHom`: `p ↦ p.1.prodMap p.2` as an algebra homomorphism
  `(M →L[R] M) × (N →L[R] N) →ₐ[R] (M × N →L[R] M × N)`.
* `ContinuousLinearMap.coe_prodMapAlgHom`: on normed spaces it is `prodMapL` as a function.
* `ContinuousLinearMap.continuous_prodMapAlgHom`: it is continuous on normed spaces.
* `ContinuousLinearMap.exp_prodMap`: `exp (A.prodMap B) = (exp A).prodMap (exp B)`.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

section Algebra

variable (R M N : Type*) [CommSemiring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [TopologicalSpace N] [AddCommGroup N]
  [Module R N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N]

/-- `ContinuousLinearMap.prodMap` as an algebra homomorphism from the product of the algebras of
endomorphisms of `M` and `N` to the algebra of endomorphisms of `M × N`. This is the continuous
analogue of `LinearMap.prodMapAlgHom`. -/
def prodMapAlgHom : (M →L[R] M) × (N →L[R] N) →ₐ[R] (M × N →L[R] M × N) where
  toFun p := p.1.prodMap p.2
  map_one' := ext fun _ ↦ rfl
  map_mul' _ _ := ext fun _ ↦ rfl
  map_zero' := ext fun _ ↦ rfl
  map_add' _ _ := ext fun _ ↦ rfl
  commutes' _ := ext fun _ ↦ rfl

variable {R M N}

/-- `ContinuousLinearMap.prodMapAlgHom` sends `(f, g)` to `f.prodMap g`. -/
@[simp]
theorem prodMapAlgHom_apply (p : (M →L[R] M) × (N →L[R] N)) :
    prodMapAlgHom R M N p = p.1.prodMap p.2 :=
  (rfl)

end Algebra

section Normed

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup X]
  [NormedSpace 𝕜 X] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- On normed spaces, `ContinuousLinearMap.prodMapAlgHom` is, as a function, Mathlib's
continuous bilinear map `ContinuousLinearMap.prodMapL`. -/
theorem coe_prodMapAlgHom : ⇑(prodMapAlgHom 𝕜 X Y) = ⇑(prodMapL 𝕜 X X Y Y) :=
  (rfl)

/-- On normed spaces, `ContinuousLinearMap.prodMapAlgHom` is continuous. -/
theorem continuous_prodMapAlgHom : Continuous (prodMapAlgHom 𝕜 X Y) := by
  rw [coe_prodMapAlgHom]
  exact (prodMapL 𝕜 X X Y Y).continuous

end Normed

section Exp

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- The exponential of a product of continuous linear endomorphisms of Banach spaces over `ℝ` or
`ℂ` is the product of their exponentials: `exp (A.prodMap B) = (exp A).prodMap (exp B)`. -/
theorem exp_prodMap (A : X →L[𝕜] X) (B : Y →L[𝕜] Y) :
    exp (A.prodMap B) = (exp A).prodMap (exp B) := by
  have hr : (A, B) ∈ Metric.eball 0 (expSeries 𝕜 ((X →L[𝕜] X) × (Y →L[𝕜] Y))).radius := by
    rw [expSeries_radius_eq_top 𝕜 ((X →L[𝕜] X) × (Y →L[𝕜] Y))]
    exact edist_lt_top _ _
  have h₁ : (exp (A, B)).1 = exp A :=
    map_exp_of_mem_ball (𝕂 := 𝕜) (RingHom.fst (X →L[𝕜] X) (Y →L[𝕜] Y)) continuous_fst _ hr
  have h₂ : (exp (A, B)).2 = exp B :=
    map_exp_of_mem_ball (𝕂 := 𝕜) (RingHom.snd (X →L[𝕜] X) (Y →L[𝕜] Y)) continuous_snd _ hr
  simpa [h₁, h₂] using
    (map_exp_of_mem_ball (𝕂 := 𝕜) (prodMapAlgHom 𝕜 X Y) continuous_prodMapAlgHom _ hr).symm

end Exp

end ContinuousLinearMap

end
