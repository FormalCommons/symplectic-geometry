/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Pullback of forms: its value at a point, negation and constant maps

At a point `x`, the pullback of a form `φ` along `f` is the value of `φ` at `f x` composed with
the differential of `f` at `x` (`TauCeti.mpullback_apply_eq_compContinuousLinearMap`). The
statement is on the tangent spaces, so that Mathlib's bound
`ContinuousAlternatingMap.norm_compContinuousLinearMap_le` applies with their norms, such as
Riemannian ones. Tau Ceti's `TauCeti.mpullback_apply_eq_compContinuousLinearMapCLM` states the
same equality on the model spaces.
So two maps with the same value and the same differential at `x` pull every form back to the
same value at `x` (`TauCeti.mpullback_apply_eq_of_mfderiv_eq`).

Pulling a form back commutes with negation (`TauCeti.mpullback_neg`), as Tau Ceti's
`TauCeti.mpullback_sub` says for subtraction.

The differential of a constant map is zero, so pulling a smooth form of positive degree back
along a constant map gives the zero form (`TauCeti.SmoothForm.mpullback_const`).

For a map `f : M × M₂ → M'`, the slice `z ↦ f (s, z)` is `f` composed with the inclusion
`z ↦ (s, z)`, whose differential is `w ↦ (0, w)` (Mathlib's `mfderiv_prod_right`). By the chain
rule `TauCeti.mpullback_comp_at`, the pullback along the slice at `z` is the pullback along `f` at
`(s, z)` on the vectors `(0, m i)` (`TauCeti.mpullback_comp_prodMk_apply`). When both factors are
normed spaces with their own models, `𝓘(ℝ, E₁ × E₂)` is not syntactically the product model, so
`TauCeti.mpullback_comp_prodMk_apply_modelSpace` states the same identity for that model.

## Main results

* `TauCeti.mpullback_apply_eq_compContinuousLinearMap`: the pullback at `x` is
  `(φ (f x)).compContinuousLinearMap (mfderiv I I' f x)`.
* `TauCeti.mpullback_apply_eq_of_mfderiv_eq`: the pullback at `x` depends only on the value and
  the differential of the map at `x`.
* `TauCeti.mpullback_neg`: the pullback of `-φ` is minus the pullback of `φ`.
* `TauCeti.SmoothForm.mpullback_const`: the pullback of a smooth `(k + 1)`-form along a constant
  map is `0`.
* `TauCeti.mpullback_comp_prodMk_apply`: the pullback along a slice `z ↦ f (s, z)` of a map on a
  product, as the pullback along `f` on the vectors `(0, m i)`.
* `TauCeti.mpullback_comp_prodMk_apply_modelSpace`: the same, for a map on a product of normed
  spaces with the model `𝓘(ℝ, E₁ × E₂)`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- At a point `x`, the pullback of `φ` along `f` is `φ (f x)` composed with the differential of
`f` at `x`, as an alternating map on the tangent space at `x`. -/
theorem mpullback_apply_eq_compContinuousLinearMap (f : M → M') (φ : RoughForm I' M' F k)
    (x : M) :
    mpullback I I' f φ x = (φ (f x)).compContinuousLinearMap (mfderiv I I' f x) :=
  ContinuousAlternatingMap.ext fun v ↦ mpullback_apply f φ x v

/-- Two maps with the same value and the same differential at `x` pull a form back to the same
value at `x`. -/
theorem mpullback_apply_eq_of_mfderiv_eq {f g : M → M'} {x : M} (h : f x = g x)
    (hd : mfderiv I I' f x = mfderiv I I' g x) (φ : RoughForm I' M' F k) :
    mpullback I I' f φ x = mpullback I I' g φ x := by
  rw [mpullback_apply_eq_compContinuousLinearMap, mpullback_apply_eq_compContinuousLinearMap, hd,
    h]

/-- Pullback commutes with negation. -/
@[simp]
theorem mpullback_neg (f : M → M') (φ : RoughForm I' M' F k) :
    mpullback I I' f (-φ) = -mpullback I I' f φ := by
  funext x
  ext v
  simp [mpullback_apply]

/-- Let `f : M × M₂ → M'` be differentiable at `(s, z)`. The pullback of `φ` along the slice
`z ↦ f (s, z)`, at `z` on vectors `m i`, is the pullback of `φ` along `f`, at `(s, z)` on the
vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply {E₂ H₂ M₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} {f : M × M₂ → M'} {s : M} {z : M₂}
    (hf : MDifferentiableAt (I.prod I₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → TangentSpace I₂ z) :
    mpullback I₂ I' (fun z ↦ f (s, z)) φ z m =
      mpullback (I.prod I₂) I' f φ (s, z) fun i ↦ ((0 : E), m i) := by
  -- The slice is `f ∘ Prod.mk s` by definition.
  refine (DFunLike.congr_fun (mpullback_comp_at (f := Prod.mk s) (g := f)
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) hf φ) m).trans ?_
  rw [mpullback_apply, mfderiv_prod_right]
  -- `inr w` is `(0, w)`; `simp` does not rewrite with `inr_apply` here, since the tangent spaces
  -- are only definitionally the model spaces.
  exact congrArg _ (funext fun i ↦ ContinuousLinearMap.inr_apply ..)

/-- Let `f : E₁ × E₂ → M'`, on a product of normed spaces, be differentiable at `(s, z)` for the
model `𝓘(ℝ, E₁ × E₂)`. The pullback of `φ` along the slice `z ↦ f (s, z)`, at `z` on vectors
`m i`, is the pullback of `φ` along `f`, at `(s, z)` on the vectors `(0, m i)`. -/
theorem mpullback_comp_prodMk_apply_modelSpace {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {f : E₁ × E₂ → M'} {s : E₁}
    {z : E₂} (hf : MDifferentiableAt 𝓘(ℝ, E₁ × E₂) I' f (s, z)) (φ : RoughForm I' M' F k)
    (m : Fin k → E₂) :
    mpullback 𝓘(ℝ, E₂) I' (fun z ↦ f (s, z)) φ z m =
      mpullback 𝓘(ℝ, E₁ × E₂) I' f φ (s, z) fun i ↦ ((0 : E₁), m i) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hf ⊢
  exact mpullback_comp_prodMk_apply hf φ m

namespace SmoothForm

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a smooth form of positive degree along a constant map is zero. -/
@[simp]
theorem mpullback_const (c : M') (hc : ContMDiff I I' ∞ fun _ : M ↦ c)
    (φ : SmoothForm I' M' F (k + 1)) : mpullback (fun _ : M ↦ c) hc φ = 0 := by
  refine Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
  rw [mpullback_apply, mfderiv_const]
  exact (φ.val c).map_coord_zero 0 rfl

end SmoothForm

end TauCeti
