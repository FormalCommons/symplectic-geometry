/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
public import TauCeti.Topology.Algebra.Module.BilinearForm
public import TauCeti.Topology.Algebra.Module.SymmetricBilinear.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Continuous bilinear forms

This file collects facts about continuous bilinear maps `V →L[𝕜] V →L[𝕜] G`, about the
bilinear forms of continuous alternating maps `E [⋀^Fin 2]→L[𝕜] 𝕜` of two vectors, about the
continuous inverse of a nondegenerate bilinear form, and about the sublevel sets of a positive
definite form.

On a finite-dimensional Hausdorff topological vector space over a complete field, every bilinear
form is continuous. Tau Ceti shows that making a bilinear form continuous and then forgetting
continuity gives the form back (`LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap`). This
file gives the other round trip: forgetting the continuity of a continuous bilinear form and
making it continuous again gives the same continuous bilinear form.

A continuous bilinear map can be carried along a continuous linear equivalence `e` in both
arguments (`ContinuousLinearEquiv.bilinearCongr`). For a form, this is, once continuity is
forgotten, `LinearMap.BilinForm.congr` along `e`; in particular it does not change whether
`b - bᵀ` is nondegenerate.

On normed spaces, Tau Ceti's `ContinuousLinearMap.symmetrizeBilinear` is the symmetric part
`b ↦ ½ (b + bᵀ)` of a continuous bilinear map. This file adds its complement, the skew part
`b ↦ ½ (b - bᵀ)`, as a continuous linear endomorphism of the space of continuous bilinear
maps. When `2` is invertible, it is a projection, it fixes the maps that are antisymmetric, and
together with the symmetric part it decomposes every continuous bilinear map. For forms, its
value is alternating, and it is nondegenerate exactly when `b - bᵀ` is, an open condition in
finite dimension.

For continuous bilinear forms `β₀` on `V₀` and `β₁` on `V₁` and a continuous linear map
`T : V₁ →L V₀`, the adjoint `ContinuousLinearMap.bilinAdjoint β₀ β₁ T : V₀ →L V₁` is
`u ↦ β₁⁻¹ (β₀ u ∘ T)`. When `β₁` is invertible it is the unique map `A` with
`β₁ (A u) y = β₀ u (T y)`, so `A` and `T` form an adjoint pair. In finite dimensions, for `β₁`
nondegenerate, it is the linear map `(β₁.toDual)⁻¹ ∘ T.dualMap ∘ β₀`.

A continuous alternating map `A` of two vectors gives the bilinear form
`(v, w) ↦ A ![v, w]`. On a finite-dimensional normed space, the maps whose form is
nondegenerate are an open set, by Tau Ceti's `TauCeti.isOpen_setOf_nondegenerate`.

For a nondegenerate bilinear form `B` on a finite-dimensional space, the map
`B.toContinuousBilinearMap` to the continuous dual is invertible, by Tau Ceti's
`TauCeti.isInvertible_toContinuousBilinearMap_iff_separatingLeft`, and its inverse is that of
`B.toDual hB`, applied to continuous linear forms.

On a finite-dimensional real normed space, a positive definite form `B` controls the norm,
`c ‖x‖² ≤ B x x` for some `c > 0`, by Tau Ceti's `IsCompact.exists_pos_forall_mul_norm_sq_le`
applied to a single form, so its sublevel sets `{x | B x x ≤ c}` are compact.

## Main definitions

* `ContinuousLinearEquiv.bilinearCongr`: a continuous bilinear map carried along a continuous
  linear equivalence in both arguments.
* `ContinuousLinearMap.skewSymmetrizeBilinear`: the skew part `b ↦ 2⁻¹ • (b - b.flip)`.
* `ContinuousLinearMap.bilinAdjoint`: the adjoint `u ↦ β₁⁻¹ (β₀ u ∘ T)` of `T` for the forms
  `β₀` and `β₁`.

## Main results

* `ContinuousLinearMap.toContinuousBilinearMap_toBilinForm`:
  `L.toBilinForm.toContinuousBilinearMap = L`.
* `ContinuousLinearEquiv.toBilinForm_bilinearCongr`: carrying a form along `e` is
  `LinearMap.BilinForm.congr` along `e`.
* `ContinuousLinearEquiv.nondegenerate_bilinearCongr_sub_flip_iff`: it preserves the
  nondegeneracy of `b - bᵀ`.
* `ContinuousLinearMap.skewSymmetrizeBilinear_skewSymmetrizeBilinear`: the skew part is
  idempotent.
* `ContinuousLinearMap.skewSymmetrizeBilinear_bilinearComp`: it commutes with simultaneous
  pullback of both arguments.
* `ContinuousLinearMap.skewSymmetrizeBilinear_eq_self_iff`,
  `ContinuousLinearMap.skewSymmetrizeBilinear_eq_zero_iff`: the skew part fixes exactly the
  antisymmetric maps and kills exactly the symmetric ones.
* `ContinuousLinearMap.symmetrizeBilinear_add_skewSymmetrizeBilinear`: a continuous bilinear
  map is the sum of its symmetric and skew parts.
* `ContinuousLinearMap.isAlt_toBilinForm_skewSymmetrizeBilinear`: the skew part of a form is
  alternating.
* `ContinuousLinearMap.nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff`: it is
  nondegenerate if and only if `b - b.flip` is.
* `ContinuousLinearMap.isOpen_setOfPred_nondegenerate_toBilinForm_sub_flip`: in finite dimension,
  the forms `b` with `b - b.flip` nondegenerate form an open set.
* `ContinuousLinearMap.apply_bilinAdjoint_apply`, `ContinuousLinearMap.eq_bilinAdjoint_iff`:
  for invertible `β₁`, the adjoint is the unique map `A` with `β₁ (A u) y = β₀ u (T y)`.
* `ContinuousLinearMap.isAdjointPair_bilinAdjoint`: for invertible `β₁`, the adjoint and `T`
  are an adjoint pair in the sense of `LinearMap.IsAdjointPair`.
* `ContinuousLinearMap.toLinearMap_bilinAdjoint`: in finite dimensions, its linear map is
  `(β₁.toDual)⁻¹ ∘ T.dualMap ∘ β₀`.
* `ContinuousAlternatingMap.isOpen_setOfPred_nondegenerate_toBilinMap`: in finite dimension, the
  continuous alternating maps of two vectors with nondegenerate bilinear form are an open set.
* `LinearMap.BilinForm.toContinuousBilinearMap_inverse_apply`: for nondegenerate `B` in finite
  dimension, `B.toContinuousBilinearMap.inverse f = (B.toDual hB).symm f`.
* `ContinuousLinearMap.ker_eq_ker_of_mul_norm_sq_add_norm_sq_le`: a form `B` and an operator `A`
  with `c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` have the same kernel.
* `ContinuousLinearMap.exists_apply_eq_of_ker_eq_span_singleton`: in finite dimension, a
  symmetric form whose kernel is a line `ℝ ∙ e` takes every value that vanishes on `e`.
* `LinearMap.BilinForm.isCompact_setOfPred_apply_self_le`: on a finite-dimensional real normed
  space, the sublevel sets of a positive definite form are compact.
-/

public section

namespace ContinuousLinearMap

/-- Forgetting the continuity of a continuous bilinear form on a finite-dimensional space, and
then making it continuous again, returns the original form. -/
@[simp]
theorem toContinuousBilinearMap_toBilinForm
    {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul 𝕜 V] [FiniteDimensional 𝕜 V] [T2Space V]
    (L : V →L[𝕜] V →L[𝕜] 𝕜) : L.toBilinForm.toContinuousBilinearMap = L :=
  (rfl)

section BilinearCongr

variable {𝕜 X W Y G : Type*} [NormedField 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- The continuous linear equivalence of the spaces of continuous bilinear maps `X × X → G` and
`W × W → G` induced by a continuous linear equivalence `e : X ≃L[𝕜] W`: it carries a map `σ`
along `e` in both arguments, to `(v, w) ↦ σ (e.symm v) (e.symm w)`. -/
def _root_.ContinuousLinearEquiv.bilinearCongr (e : X ≃L[𝕜] W) :
    (X →L[𝕜] X →L[𝕜] G) ≃L[𝕜] (W →L[𝕜] W →L[𝕜] G) :=
  e.arrowCongr (e.arrowCongr (.refl 𝕜 G))

theorem _root_.ContinuousLinearEquiv.bilinearCongr_def (e : X ≃L[𝕜] W) :
    e.bilinearCongr (G := G) = e.arrowCongr (e.arrowCongr (.refl 𝕜 G)) :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearEquiv.bilinearCongr_apply (e : X ≃L[𝕜] W)
    (σ : X →L[𝕜] X →L[𝕜] G) (v w : W) :
    e.bilinearCongr σ v w = σ (e.symm v) (e.symm w) :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearEquiv.symm_bilinearCongr (e : X ≃L[𝕜] W) :
    (e.bilinearCongr (G := G)).symm = e.symm.bilinearCongr :=
  (rfl)

@[simp]
theorem _root_.ContinuousLinearEquiv.bilinearCongr_refl :
    (ContinuousLinearEquiv.refl 𝕜 X).bilinearCongr (G := G) = .refl 𝕜 _ :=
  (rfl)

theorem _root_.ContinuousLinearEquiv.bilinearCongr_trans (e : X ≃L[𝕜] W) (f : W ≃L[𝕜] Y) :
    (e.trans f).bilinearCongr (G := G) = e.bilinearCongr.trans f.bilinearCongr :=
  (rfl)

/-- Carrying a continuous bilinear form along a continuous linear equivalence `e` in both
arguments is, as a bilinear form, `LinearMap.BilinForm.congr` along `e`. -/
theorem _root_.ContinuousLinearEquiv.toBilinForm_bilinearCongr (e : X ≃L[𝕜] W)
    (σ : X →L[𝕜] X →L[𝕜] 𝕜) :
    (e.bilinearCongr σ).toBilinForm = LinearMap.BilinForm.congr e.toLinearEquiv σ.toBilinForm := by
  ext v w
  simp

end BilinearCongr

section NontriviallyNormed

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]

/-- Carrying a bilinear map along `e` is precomposing it with `e.symm` in both arguments. -/
theorem _root_.ContinuousLinearEquiv.bilinearCongr_apply_eq_bilinearComp {X W G : Type*}
    [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (e : X ≃L[𝕜] W) (σ : X →L[𝕜] X →L[𝕜] G) :
    e.bilinearCongr σ = σ.bilinearComp (e.symm : W →L[𝕜] X) (e.symm : W →L[𝕜] X) := by
  ext v w
  simp

/-- Carrying a continuous bilinear form along a continuous linear equivalence `e` does not change
whether its skew part `σ - σᵀ` is nondegenerate. -/
theorem _root_.ContinuousLinearEquiv.nondegenerate_bilinearCongr_sub_flip_iff {W : Type*}
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (e : X ≃L[𝕜] W) {σ : X →L[𝕜] X →L[𝕜] 𝕜} :
    (e.bilinearCongr σ - (e.bilinearCongr σ).flip).toBilinForm.Nondegenerate ↔
      (σ.toBilinForm - σ.toBilinForm.flip).Nondegenerate := by
  set τ := e.bilinearCongr σ
  have h : (τ - τ.flip).toBilinForm = τ.toBilinForm - τ.toBilinForm.flip := by
    ext v w
    simp
  have hc : LinearMap.BilinForm.congr e.toLinearEquiv (σ.toBilinForm - σ.toBilinForm.flip) =
      LinearMap.BilinForm.congr e.toLinearEquiv σ.toBilinForm -
        (LinearMap.BilinForm.congr e.toLinearEquiv σ.toBilinForm).flip := by
    ext v w
    simp
  rw [h, e.toBilinForm_bilinearCongr, ← hc, LinearMap.BilinForm.nondegenerate_congr_iff]

end NontriviallyNormed

section SkewPart

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The skew part `½ (b - bᵀ)` of a continuous bilinear map, as a continuous linear map on the
space of continuous bilinear maps. It is the complement of Tau Ceti's `symmetrizeBilinear`. -/
noncomputable def skewSymmetrizeBilinear :
    (V →L[𝕜] V →L[𝕜] G) →L[𝕜] V →L[𝕜] V →L[𝕜] G :=
  (2 : 𝕜)⁻¹ • (ContinuousLinearMap.id 𝕜 _ -
    ((flipₗᵢ 𝕜 V V G).toContinuousLinearEquiv : _ →L[𝕜] _))

theorem skewSymmetrizeBilinear_def (b : V →L[𝕜] V →L[𝕜] G) :
    skewSymmetrizeBilinear b = (2 : 𝕜)⁻¹ • (b - b.flip) :=
  (rfl)

@[simp]
theorem skewSymmetrizeBilinear_apply (b : V →L[𝕜] V →L[𝕜] G) (v w : V) :
    skewSymmetrizeBilinear b v w = (2 : 𝕜)⁻¹ • (b v w - b w v) :=
  (rfl)

/-- The skew part vanishes on the diagonal. -/
theorem skewSymmetrizeBilinear_apply_self (b : V →L[𝕜] V →L[𝕜] G) (v : V) :
    skewSymmetrizeBilinear b v v = 0 := by
  simp

/-- The transpose of the skew part is its negative. -/
@[simp]
theorem flip_skewSymmetrizeBilinear (b : V →L[𝕜] V →L[𝕜] G) :
    (skewSymmetrizeBilinear b).flip = -skewSymmetrizeBilinear b := by
  ext v w
  simp [← smul_neg]

/-- The skew part of a continuous bilinear map whose transpose is its negative is the map
itself. -/
theorem skewSymmetrizeBilinear_of_flip_eq_neg [NeZero (2 : 𝕜)] {b : V →L[𝕜] V →L[𝕜] G}
    (hb : b.flip = -b) : skewSymmetrizeBilinear b = b := by
  rw [skewSymmetrizeBilinear_def, hb, sub_neg_eq_add, ← two_smul 𝕜]
  simp [NeZero.ne (2 : 𝕜)]

/-- A continuous bilinear map is its own skew part exactly when its transpose is its
negative. -/
theorem skewSymmetrizeBilinear_eq_self_iff [NeZero (2 : 𝕜)] {b : V →L[𝕜] V →L[𝕜] G} :
    skewSymmetrizeBilinear b = b ↔ b.flip = -b :=
  ⟨fun h => h ▸ flip_skewSymmetrizeBilinear b, skewSymmetrizeBilinear_of_flip_eq_neg⟩

/-- The skew part is idempotent. -/
@[simp]
theorem skewSymmetrizeBilinear_skewSymmetrizeBilinear [NeZero (2 : 𝕜)]
    (b : V →L[𝕜] V →L[𝕜] G) :
    skewSymmetrizeBilinear (skewSymmetrizeBilinear b) = skewSymmetrizeBilinear b :=
  skewSymmetrizeBilinear_of_flip_eq_neg (flip_skewSymmetrizeBilinear b)

/-- The skew part commutes with simultaneous pullback of its two arguments. -/
theorem skewSymmetrizeBilinear_bilinearComp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (b : V →L[𝕜] V →L[𝕜] G) (A : W →L[𝕜] V) :
    skewSymmetrizeBilinear (b.bilinearComp A A) =
      (skewSymmetrizeBilinear b).bilinearComp A A := by
  ext v w
  simp

/-- The skew part of a symmetric continuous bilinear map is zero. -/
@[simp]
theorem skewSymmetrizeBilinear_coe (b : symmetricBilinearMaps 𝕜 V G) :
    skewSymmetrizeBilinear b.val = 0 := by
  ext v w
  simp [(mem_symmetricBilinearMaps 𝕜 V G b.val).1 b.property v w]

/-- The symmetric part of the skew part is zero. -/
@[simp]
theorem symmetrizeBilinear_skewSymmetrizeBilinear (b : V →L[𝕜] V →L[𝕜] G) :
    symmetrizeBilinear (skewSymmetrizeBilinear b) = 0 := by
  apply Subtype.ext
  ext v w
  simp [← smul_add]

/-- A continuous bilinear map is the sum of its symmetric and skew parts. -/
theorem symmetrizeBilinear_add_skewSymmetrizeBilinear [NeZero (2 : 𝕜)]
    (b : V →L[𝕜] V →L[𝕜] G) :
    (symmetrizeBilinear b).val + skewSymmetrizeBilinear b = b := by
  ext v w
  simp [← smul_add, ← two_smul 𝕜, NeZero.ne (2 : 𝕜)]

/-- The skew part of a continuous bilinear map vanishes exactly when the map is symmetric. -/
theorem skewSymmetrizeBilinear_eq_zero_iff [NeZero (2 : 𝕜)] {b : V →L[𝕜] V →L[𝕜] G} :
    skewSymmetrizeBilinear b = 0 ↔ b ∈ symmetricBilinearMaps 𝕜 V G := by
  refine ⟨fun h => ?_, fun h => skewSymmetrizeBilinear_coe ⟨b, h⟩⟩
  rw [← symmetrizeBilinear_add_skewSymmetrizeBilinear b, h, add_zero]
  exact (symmetrizeBilinear b).property

/-- The skew part of a continuous bilinear form is alternating. -/
theorem isAlt_toBilinForm_skewSymmetrizeBilinear (b : V →L[𝕜] V →L[𝕜] 𝕜) :
    (skewSymmetrizeBilinear b).toBilinForm.IsAlt :=
  skewSymmetrizeBilinear_apply_self b

/-- The skew part of an alternating continuous bilinear form is the form itself. -/
theorem skewSymmetrizeBilinear_of_isAlt [NeZero (2 : 𝕜)] {b : V →L[𝕜] V →L[𝕜] 𝕜}
    (hb : b.toBilinForm.IsAlt) : skewSymmetrizeBilinear b = b :=
  skewSymmetrizeBilinear_of_flip_eq_neg <| by
    ext v w
    exact (hb.neg_eq v w).symm

/-- The skew part of a continuous bilinear form is nondegenerate if and only if `b - bᵀ` is. -/
theorem nondegenerate_toBilinForm_skewSymmetrizeBilinear_iff [NeZero (2 : 𝕜)]
    (b : V →L[𝕜] V →L[𝕜] 𝕜) :
    (skewSymmetrizeBilinear b).toBilinForm.Nondegenerate ↔
      (b - b.flip).toBilinForm.Nondegenerate := by
  have h : (skewSymmetrizeBilinear b).toBilinForm = (2 : 𝕜)⁻¹ • (b - b.flip).toBilinForm := by
    ext v w
    simp
  rw [h]
  exact BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero (inv_ne_zero (NeZero.ne _)))

/-- In finite dimension, the continuous bilinear forms `b` such that `b - bᵀ` is nondegenerate
form an open set. -/
theorem isOpen_setOfPred_nondegenerate_toBilinForm_sub_flip [FiniteDimensional 𝕜 V] :
    IsOpen {b : V →L[𝕜] V →L[𝕜] 𝕜 | (b - b.flip).toBilinForm.Nondegenerate} :=
  isOpen_setOf_nondegenerate_toBilinForm.preimage
    (continuous_id.sub (flipₗᵢ 𝕜 V V 𝕜).continuous)

end SkewPart

section BilinAdjoint

variable {𝕜 V₀ V₁ : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup V₀] [Module 𝕜 V₀] [TopologicalSpace V₀] [IsNormableSpace 𝕜 V₀]
  [AddCommGroup V₁] [Module 𝕜 V₁] [TopologicalSpace V₁] [IsNormableSpace 𝕜 V₁]

/-- The adjoint `u ↦ β₁⁻¹ (β₀ u ∘ T)` of `T : V₁ →L V₀` for the bilinear forms `β₀` on `V₀` and
`β₁` on `V₁`. When `β₁` is invertible, it is the unique map `A` with `β₁ (A u) y = β₀ u (T y)`
(`ContinuousLinearMap.eq_bilinAdjoint_iff`). -/
noncomputable def bilinAdjoint (β₀ : V₀ →L[𝕜] V₀ →L[𝕜] 𝕜) (β₁ : V₁ →L[𝕜] V₁ →L[𝕜] 𝕜)
    (T : V₁ →L[𝕜] V₀) : V₀ →L[𝕜] V₁ :=
  β₁.inverse ∘L (β₀.flip ∘L T).flip

theorem bilinAdjoint_def (β₀ : V₀ →L[𝕜] V₀ →L[𝕜] 𝕜) (β₁ : V₁ →L[𝕜] V₁ →L[𝕜] 𝕜)
    (T : V₁ →L[𝕜] V₀) : bilinAdjoint β₀ β₁ T = β₁.inverse ∘L (β₀.flip ∘L T).flip :=
  (rfl)

variable {β₀ : V₀ →L[𝕜] V₀ →L[𝕜] 𝕜} {β₁ : V₁ →L[𝕜] V₁ →L[𝕜] 𝕜}

/-- The defining identity of the adjoint: `β₁ (A u) y = β₀ u (T y)`. -/
theorem apply_bilinAdjoint_apply (hβ₁ : β₁.IsInvertible) (T : V₁ →L[𝕜] V₀) (u : V₀) (y : V₁) :
    β₁ (bilinAdjoint β₀ β₁ T u) y = β₀ u (T y) := by
  simp [bilinAdjoint_def, hβ₁.self_apply_inverse]

/-- For invertible `β₁`, the adjoint is the only map `A` with `β₁ (A u) y = β₀ u (T y)`. -/
theorem eq_bilinAdjoint_iff (hβ₁ : β₁.IsInvertible) {T : V₁ →L[𝕜] V₀} {A : V₀ →L[𝕜] V₁} :
    A = bilinAdjoint β₀ β₁ T ↔ ∀ u y, β₁ (A u) y = β₀ u (T y) := by
  refine ⟨fun h ↦ h ▸ apply_bilinAdjoint_apply hβ₁ T, fun h ↦ ext fun u ↦ hβ₁.injective ?_⟩
  ext y
  rw [h, apply_bilinAdjoint_apply hβ₁]

/-- For invertible `β₁`, the adjoint of `T` and `T` are an adjoint pair for the bilinear forms of
`β₀` and `β₁`: `β₁ (A u) y = β₀ u (T y)`. -/
theorem isAdjointPair_bilinAdjoint (hβ₁ : β₁.IsInvertible) (T : V₁ →L[𝕜] V₀) :
    LinearMap.IsAdjointPair β₀.toBilinForm β₁.toBilinForm
      (bilinAdjoint β₀ β₁ T : V₀ →ₗ[𝕜] V₁) (T : V₁ →ₗ[𝕜] V₀) :=
  fun u y ↦ by simp [apply_bilinAdjoint_apply hβ₁]

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup V₁] [ContinuousSMul 𝕜 V₁] [T2Space V₁]
  [FiniteDimensional 𝕜 V₁]

/-- In finite dimensions, for nondegenerate `β₁`, the adjoint is the linear map
`(β₁.toDual)⁻¹ ∘ T.dualMap ∘ β₀`. -/
theorem toLinearMap_bilinAdjoint (hβ₁ : β₁.toBilinForm.Nondegenerate) (T : V₁ →L[𝕜] V₀) :
    (bilinAdjoint β₀ β₁ T : V₀ →ₗ[𝕜] V₁) =
      (β₁.toBilinForm.toDual hβ₁).symm.toLinearMap ∘ₗ (T : V₁ →ₗ[𝕜] V₀).dualMap ∘ₗ
        β₀.toBilinForm := by
  refine LinearMap.ext fun u ↦ (β₁.toBilinForm.toDual hβ₁).injective (LinearMap.ext fun y ↦ ?_)
  simp [LinearMap.BilinForm.toDual_def,
    apply_bilinAdjoint_apply (isInvertible_iff_nondegenerate_toBilinForm.2 hβ₁)]

end BilinAdjoint

end ContinuousLinearMap

namespace ContinuousAlternatingMap

/-- In finite dimension, the continuous alternating maps `A` of two vectors whose bilinear form
`(v, w) ↦ A ![v, w]` is nondegenerate form an open set. -/
theorem isOpen_setOfPred_nondegenerate_toBilinMap {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    IsOpen {A : E [⋀^Fin 2]→L[𝕜] 𝕜 |
      LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap A.toMultilinearMap)} :=
  TauCeti.isOpen_setOf_nondegenerate fun v w ↦ by
    simpa using continuous_eval_const ![v, w]

end ContinuousAlternatingMap

namespace LinearMap.BilinForm

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V] {B : LinearMap.BilinForm 𝕜 V}

/-- For a nondegenerate bilinear form `B` in finite dimension, the inverse of the continuous map
`v ↦ B v` to the continuous dual sends a continuous linear form `f` to `(B.toDual hB).symm f`. -/
theorem toContinuousBilinearMap_inverse_apply (hB : B.Nondegenerate) (f : StrongDual 𝕜 V) :
    B.toContinuousBilinearMap.inverse f = (B.toDual hB).symm f := by
  have h : B.toContinuousBilinearMap.IsInvertible := by simpa using hB.1
  refine h.inverse_apply_eq.2 ?_
  ext w
  simp

/-- On a finite-dimensional real normed space, the sublevel sets `{x | B x x ≤ c}` of a positive
definite bilinear form `B` are compact. -/
theorem isCompact_setOfPred_apply_self_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {B : LinearMap.BilinForm ℝ E} (hB : B.toQuadraticMap.PosDef)
    (c : ℝ) : IsCompact {x | B x x ≤ c} := by
  obtain ⟨a, ha, hle⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ B.toContinuousBilinearMap) continuousOn_const fun _ _ v hv ↦ by
      simpa using hB v hv
  refine (isCompact_closedBall (0 : E) √(c / a)).of_isClosed_subset
    (isClosed_le (LinearMap.continuous_apply_self B) continuous_const)
    fun x (hx : B x x ≤ c) ↦ ?_
  rw [mem_closedBall_zero_iff]
  refine Real.le_sqrt_of_sq_le ?_
  rw [le_div_iff₀ ha, mul_comm]
  simpa using (hle () rfl x).trans hx

end LinearMap.BilinForm

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)` for every `v`, with `c > 0`, then the continuous
bilinear form `B` and the operator `A` have the same kernel. -/
theorem ker_eq_ker_of_mul_norm_sq_add_norm_sq_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {A : E →L[ℝ] F} {B : E →L[ℝ] F →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) ≤ B v (A v)) : B.ker = A.ker := by
  ext v
  simp only [LinearMap.mem_ker, coe_coe]
  constructor <;> intro hv <;> have h := h v
  · rw [hv, zero_apply, norm_zero] at h
    have : ‖A v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖A v‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  · rw [hv, map_zero, norm_zero] at h
    have : ‖B v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖B v‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))

/-- In finite dimension, a symmetric continuous bilinear form `B` whose kernel is the line
`ℝ ∙ e`, with `e ≠ 0`, takes as values `B w` every continuous linear form that vanishes on
`e`. -/
theorem exists_apply_eq_of_ker_eq_span_singleton [FiniteDimensional ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ v w, B v w = B w v) {e : E} (he : e ≠ 0) (hker : B.ker = ℝ ∙ e)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ e = 0) : ∃ w, B w = ℓ := by
  set S : Submodule ℝ (E →L[ℝ] ℝ) := LinearMap.ker (apply ℝ ℝ e).toLinearMap
  -- The range of `B` lies in the forms that vanish on `e`, and has the same dimension.
  have hle : LinearMap.range B.toLinearMap ≤ S := by
    rintro _ ⟨w, rfl⟩
    have : B e = 0 := LinearMap.mem_ker.1 (hker ▸ Submodule.mem_span_singleton_self e)
    simp [S, hB w e, this]
  have hsurj : Function.Surjective (apply ℝ ℝ e : (E →L[ℝ] ℝ) →L[ℝ] ℝ) := by
    obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ e (norm_ne_zero_iff.2 he)
    refine fun r ↦ ⟨(r / ‖e‖) • g, ?_⟩
    have : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    simp [hg, this]
  have h₁ := LinearMap.finrank_range_add_finrank_ker B.toLinearMap
  have h₂ := LinearMap.finrank_range_add_finrank_ker (apply ℝ ℝ e : (E →L[ℝ] ℝ) →L[ℝ] ℝ).toLinearMap
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at h₂
  have h₃ : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E :=
    LinearMap.toContinuousLinearMap.symm.finrank_eq.trans Subspace.dual_finrank_eq
  have h₄ : Module.finrank ℝ B.ker = 1 := by rw [hker]; exact finrank_span_singleton he
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by simp only [S] at *; omega)
  obtain ⟨w, hw⟩ := heq ▸ (show ℓ ∈ S by simp [S, hℓ])
  exact ⟨w, hw⟩

end ContinuousLinearMap

end
