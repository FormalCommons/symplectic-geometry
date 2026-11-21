/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.Topology.Algebra.Module.SymmetricBilinear.Basic

/-!
# Continuous bilinear forms

This file collects two facts about continuous bilinear maps `V →L[𝕜] V →L[𝕜] G`.

On a finite-dimensional Hausdorff topological vector space over a complete field, every bilinear
form is continuous. Tau Ceti shows that making a bilinear form continuous and then forgetting
continuity gives the form back (`LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap`). This
file gives the other round trip: forgetting the continuity of a continuous bilinear form and
making it continuous again gives the same continuous bilinear form.

On normed spaces, Tau Ceti's `ContinuousLinearMap.symmetrizeBilinear` is the symmetric part
`b ↦ ½ (b + bᵀ)` of a continuous bilinear map. This file adds its complement, the skew part
`b ↦ ½ (b - bᵀ)`, as a continuous linear endomorphism of the space of continuous bilinear
maps. When `2` is invertible, it is a projection, it fixes the maps that are antisymmetric, and
together with the symmetric part it decomposes every continuous bilinear map. For forms, its
value is alternating, and it is nondegenerate exactly when `b - bᵀ` is.

## Main definitions

* `ContinuousLinearMap.skewSymmetrizeBilinear`: the skew part `b ↦ 2⁻¹ • (b - b.flip)`.

## Main results

* `ContinuousLinearMap.toContinuousBilinearMap_toBilinForm`:
  `L.toBilinForm.toContinuousBilinearMap = L`.
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

end SkewPart

end ContinuousLinearMap

end
