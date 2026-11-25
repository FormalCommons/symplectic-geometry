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

/-!
# Continuous bilinear forms

This file collects four facts about continuous bilinear maps `V →L[𝕜] V →L[𝕜] G`.

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

Finally, a continuous alternating map `A` of two vectors gives the bilinear form
`(v, w) ↦ A ![v, w]`. On a finite-dimensional normed space, the maps whose form is
nondegenerate are an open set, by Tau Ceti's `TauCeti.isOpen_setOf_nondegenerate`.

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
* `ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm_sub_flip`: in finite dimension,
  the forms `b` with `b - b.flip` nondegenerate form an open set.
* `ContinuousLinearMap.apply_bilinAdjoint_apply`, `ContinuousLinearMap.eq_bilinAdjoint_iff`:
  for invertible `β₁`, the adjoint is the unique map `A` with `β₁ (A u) y = β₀ u (T y)`.
* `ContinuousLinearMap.isAdjointPair_bilinAdjoint`: for invertible `β₁`, the adjoint and `T`
  are an adjoint pair in the sense of `LinearMap.IsAdjointPair`.
* `ContinuousLinearMap.coe_bilinAdjoint`: in finite dimensions, its linear map is
  `(β₁.toDual)⁻¹ ∘ T.dualMap ∘ β₀`.
* `ContinuousAlternatingMap.isOpen_setOf_nondegenerate_toBilinMap`: in finite dimension, the
  continuous alternating maps of two vectors with nondegenerate bilinear form are an open set.
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
theorem isOpen_setOf_nondegenerate_toBilinForm_sub_flip [FiniteDimensional 𝕜 V] :
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
theorem coe_bilinAdjoint (hβ₁ : β₁.toBilinForm.Nondegenerate) (T : V₁ →L[𝕜] V₀) :
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
theorem isOpen_setOf_nondegenerate_toBilinMap {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    IsOpen {A : E [⋀^Fin 2]→L[𝕜] 𝕜 |
      LinearMap.BilinForm.Nondegenerate (MultilinearMap.toBilinMap A.toMultilinearMap)} :=
  TauCeti.isOpen_setOf_nondegenerate fun v w ↦ by
    simpa using continuous_eval_const ![v, w]

end ContinuousAlternatingMap

end
