/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import SymplecticGeometry.Geometry.Manifold.Instances.HalfLine.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smoothness of the normal ray and the depth coordinates of the half-line

This file extends Tau Ceti's `TauCeti.Geometry.Manifold.Boundary.Collar.Local`. Tau Ceti's normal
ray `TauCeti.EuclideanHalfSpace.normalRay : ℝ → EuclideanHalfSpace 1` sends `r` to the point at
normal distance `max r 0` from the boundary, and is continuous. On `[0, ∞)` it is the inverse of
the model with corners of the half-line, composed with a linear map, so it is smooth there, up to
the boundary point `0`. Restricted to `(-∞, 1)`, the ray takes values in the open segment
`normalIioOpens 1`, the normal factor of a collar; this gives the depth map
`SymplecticGeometry.EuclideanHalfSpace.normalIioRay`. Gluing pieces such as `(-1, ∞) × ∂W` to a
collar read the depth along `s ↦ -s`; the file gives that depth map and the map `t ↦ -t`
back, for any open set of reals between `(-1, 0]` and `(-1, ∞)`, and likewise the depth
`max s 0` and the map `t ↦ t` back, for any open set of reals between `[0, 1)` and `(-∞, 1)`.
The maps `t ↦ -t` and `t ↦ t` from depths are immersions, the depth `0` included, since the
coordinate of the half-line is one, and local diffeomorphisms at positive depth.

## Main definitions

* `SymplecticGeometry.EuclideanHalfSpace.normalIioRay`: the normal ray on `(-∞, 1)`, as a map into
  `normalIioOpens 1`.
* `SymplecticGeometry.EuclideanHalfSpace.negNormalIioRay`, `negNormalCoord`: the depth
  `max (-s) 0` of a point `s > -1`, and the point `-t` at a depth `t`.
* `SymplecticGeometry.EuclideanHalfSpace.posNormalIioRay`, `posNormalCoord`: the depth
  `max s 0` of a point `s < 1`, and the point `t` at a depth `t`.

## Main results

* `TauCeti.EuclideanHalfSpace.normalRay_mem_normalIioOpens`: the normal ray at `r` lies in
  `normalIioOpens ε`, for `ε > 0`, exactly when `r < ε`.
* `SymplecticGeometry.EuclideanHalfSpace.continuous_normalIioRay` and
  `ContMDiffAt.normalIioRay`: the depth map is continuous, and smooth at positive depth.
* `SymplecticGeometry.EuclideanHalfSpace.negNormalIioRay_negNormalCoord` and
  `negNormalCoord_negNormalIioRay`: the two maps are inverse to each other on `(-1, 0]`.
* `SymplecticGeometry.EuclideanHalfSpace.posNormalIioRay_posNormalCoord` and
  `posNormalCoord_posNormalIioRay`: the two maps are inverse to each other on `[0, 1)`.
* `SymplecticGeometry.EuclideanHalfSpace.isImmersionAt_negNormalCoord`,
  `isImmersionAt_posNormalCoord`, `isLocalDiffeomorphAt_negNormalCoord` and
  `isLocalDiffeomorphAt_posNormalCoord`: the maps `t ↦ -t` and `t ↦ t` from depths are
  immersions, and local diffeomorphisms at positive depth.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- For `ε > 0`, the normal ray at `r` lies in the open segment `[0, ε)` exactly when `r < ε`. -/
theorem normalRay_mem_normalIioOpens {ε r : ℝ} (hε : 0 < ε) :
    normalRay r ∈ normalIioOpens ε ↔ r < ε := by
  rw [mem_normalIioOpens, normalRay_coe_apply, max_lt_iff, and_iff_left hε]

end TauCeti.EuclideanHalfSpace

namespace SymplecticGeometry.EuclideanHalfSpace

open TauCeti TauCeti.EuclideanHalfSpace

/-- The normal ray on `(-∞, 1)`, as a map into the open segment `normalIioOpens 1`: the point of
`[0, 1)` at depth `max r 0`. -/
noncomputable def normalIioRay (r : Iio (1 : ℝ)) : normalIioOpens 1 :=
  ⟨normalRay r, (normalRay_mem_normalIioOpens one_pos).2 r.property⟩

/-- The point `normalIioRay r` of `[0, 1)` is the normal ray at `r`. -/
@[simp]
theorem coe_normalIioRay (r : Iio (1 : ℝ)) :
    (normalIioRay r : EuclideanHalfSpace 1) = normalRay r := (rfl)

/-- The depth of `normalIioRay r` is `max r 0`. -/
theorem normalIioRay_coe_apply (r : Iio (1 : ℝ)) :
    (normalIioRay r : EuclideanHalfSpace 1).val 0 = max (r : ℝ) 0 :=
  normalRay_coe_apply r

/-- For `0 ≤ r < 1`, the depth of `normalIioRay r` is `r`. -/
theorem normalIioRay_coe_apply_of_nonneg {r : ℝ} (hr : r < 1) (h0 : 0 ≤ r) :
    (normalIioRay ⟨r, hr⟩ : EuclideanHalfSpace 1).val 0 = r := by
  rw [normalIioRay_coe_apply]
  exact max_eq_left h0

/-- The depth map sends `r` to the origin exactly when `r ≤ 0`. -/
theorem normalIioRay_eq_zero_iff {r : ℝ} (hr : r < 1) :
    normalIioRay ⟨r, hr⟩ = normalIioOpensZero one_pos ↔ r ≤ 0 := by
  rw [← Subtype.coe_inj, coe_normalIioOpensZero, EuclideanHalfSpace.eq_zero_iff,
    normalIioRay_coe_apply]
  exact max_eq_right_iff

/-- The depth map starts at the origin. -/
@[simp]
theorem normalIioRay_zero :
    normalIioRay ⟨0, one_pos⟩ = normalIioOpensZero one_pos :=
  Subtype.ext (by simp [coe_normalIioOpensZero])

/-- The depth map is continuous. -/
theorem continuous_normalIioRay : Continuous normalIioRay :=
  (continuous_normalRay.comp continuous_subtypeVal).subtype_mk _

/-! ### The depth map read along `s ↦ -s` -/

variable {S : TopologicalSpace.Opens ℝ}

/-- For an open set `S` of reals greater than `-1`, the depth map at `-s`, for `s ∈ S`: the
point of `[0, 1)` at depth `max (-s) 0`. -/
noncomputable def negNormalIioRay (hS : (S : Set ℝ) ⊆ Ioi (-1)) (s : S) : normalIioOpens 1 :=
  normalIioRay ⟨-s, neg_lt.1 (hS s.property)⟩

theorem negNormalIioRay_def (hS : (S : Set ℝ) ⊆ Ioi (-1)) (s : S) :
    negNormalIioRay hS s = normalIioRay ⟨-s, neg_lt.1 (hS s.property)⟩ := (rfl)

/-- The point `negNormalIioRay hS s` of `[0, 1)` is the normal ray at `-s`. -/
@[simp]
theorem coe_negNormalIioRay (hS : (S : Set ℝ) ⊆ Ioi (-1)) (s : S) :
    (negNormalIioRay hS s : EuclideanHalfSpace 1) = normalRay (-s) := (rfl)

/-- The depth of `negNormalIioRay hS s` is `max (-s) 0`. -/
theorem negNormalIioRay_coe_apply (hS : (S : Set ℝ) ⊆ Ioi (-1)) (s : S) :
    (negNormalIioRay hS s : EuclideanHalfSpace 1).val 0 = max (-(s : ℝ)) 0 := by
  rw [negNormalIioRay_def, normalIioRay_coe_apply]

/-- For `s ≤ 0`, the depth of `negNormalIioRay hS s` is `-s`. -/
theorem negNormalIioRay_coe_apply_of_nonpos (hS : (S : Set ℝ) ⊆ Ioi (-1)) {s : S}
    (hs : (s : ℝ) ≤ 0) : (negNormalIioRay hS s : EuclideanHalfSpace 1).val 0 = -s := by
  rw [negNormalIioRay_coe_apply, max_eq_left (neg_nonneg.2 hs)]

/-- The point `negNormalIioRay hS s` is the origin exactly when `0 ≤ s`. -/
theorem negNormalIioRay_eq_zero_iff (hS : (S : Set ℝ) ⊆ Ioi (-1)) {s : S} :
    negNormalIioRay hS s = normalIioOpensZero one_pos ↔ 0 ≤ (s : ℝ) := by
  rw [negNormalIioRay_def, normalIioRay_eq_zero_iff, neg_nonpos]

/-- The depth map read along `s ↦ -s` is continuous. -/
theorem continuous_negNormalIioRay (hS : (S : Set ℝ) ⊆ Ioi (-1)) :
    Continuous (negNormalIioRay hS) :=
  continuous_normalIioRay.comp ((continuous_neg.comp continuous_subtypeVal).subtype_mk _)

/-- For an open set `S` of reals containing `(-1, 0]`, the point `-t` of `S` at a depth
`t ∈ [0, 1)`. It is a right inverse of `negNormalIioRay` (`negNormalIioRay_negNormalCoord`), and
a left inverse on `S ∩ (-∞, 0]` (`negNormalCoord_negNormalIioRay`). -/
def negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) : S :=
  ⟨-(t : EuclideanHalfSpace 1).val 0,
    hS ⟨neg_lt_neg (mem_normalIioOpens.1 t.property),
      neg_nonpos.2 (t : EuclideanHalfSpace 1).property⟩⟩

theorem negNormalCoord_def (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    negNormalCoord hS t = ⟨-(t : EuclideanHalfSpace 1).val 0,
      hS ⟨neg_lt_neg (mem_normalIioOpens.1 t.property),
        neg_nonpos.2 (t : EuclideanHalfSpace 1).property⟩⟩ := (rfl)

/-- Read in `ℝ`, the map `negNormalCoord hS` is `s ↦ -s 0` on the points of `[0, 1)`. -/
theorem val_comp_negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) :
    Subtype.val ∘ negNormalCoord hS =
      (fun s : EuclideanHalfSpace 1 ↦ -s.val 0) ∘ Subtype.val := (rfl)

/-- The point `negNormalCoord hS t` is minus the depth of `t`. -/
@[simp]
theorem coe_negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    (negNormalCoord hS t : ℝ) = -(t : EuclideanHalfSpace 1).val 0 := (rfl)

/-- The point `negNormalCoord hS t` is at most `0`. -/
theorem negNormalCoord_nonpos (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    (negNormalCoord hS t : ℝ) ≤ 0 := by
  rw [coe_negNormalCoord]
  exact neg_nonpos.2 (t : EuclideanHalfSpace 1).property

/-- At a positive depth `t`, the point `negNormalCoord hS t` is negative. -/
theorem negNormalCoord_neg (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) {t : normalIioOpens 1}
    (ht : 0 < (t : EuclideanHalfSpace 1).val 0) : (negNormalCoord hS t : ℝ) < 0 := by
  rw [coe_negNormalCoord]
  exact neg_neg_of_pos ht

/-- The map `t ↦ -t` from depths into `S` is continuous. -/
theorem continuous_negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) :
    Continuous (negNormalCoord hS) :=
  Continuous.subtype_mk (by fun_prop) _

/-- The depth of `-t` is `t`. -/
@[simp]
theorem negNormalIioRay_negNormalCoord (hS : (S : Set ℝ) ⊆ Ioi (-1))
    (hS' : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    negNormalIioRay hS (negNormalCoord hS' t) = t :=
  Subtype.ext (by simp [negNormalIioRay_def, normalRay_normalCoord])

/-- For `s ≤ 0`, the point `-t` at the depth `t = -s` is `s`. -/
theorem negNormalCoord_negNormalIioRay (hS : (S : Set ℝ) ⊆ Ioi (-1))
    (hS' : Ioc (-1) 0 ⊆ (S : Set ℝ)) {s : S} (hs : (s : ℝ) ≤ 0) :
    negNormalCoord hS' (negNormalIioRay hS s) = s :=
  Subtype.ext (by rw [coe_negNormalCoord, negNormalIioRay_coe_apply_of_nonpos hS hs, neg_neg])

/-! ### The depth map on reals below `1` -/

/-- For an open set `S` of reals less than `1`, the depth map at `s ∈ S`: the point of `[0, 1)` at
depth `max s 0`. -/
noncomputable def posNormalIioRay (hS : (S : Set ℝ) ⊆ Iio 1) (s : S) : normalIioOpens 1 :=
  normalIioRay ⟨s, hS s.property⟩

theorem posNormalIioRay_def (hS : (S : Set ℝ) ⊆ Iio 1) (s : S) :
    posNormalIioRay hS s = normalIioRay ⟨s, hS s.property⟩ := (rfl)

/-- The point `posNormalIioRay hS s` of `[0, 1)` is the normal ray at `s`. -/
@[simp]
theorem coe_posNormalIioRay (hS : (S : Set ℝ) ⊆ Iio 1) (s : S) :
    (posNormalIioRay hS s : EuclideanHalfSpace 1) = normalRay s := (rfl)

/-- The depth of `posNormalIioRay hS s` is `max s 0`. -/
theorem posNormalIioRay_coe_apply (hS : (S : Set ℝ) ⊆ Iio 1) (s : S) :
    (posNormalIioRay hS s : EuclideanHalfSpace 1).val 0 = max (s : ℝ) 0 := by
  rw [posNormalIioRay_def, normalIioRay_coe_apply]

/-- For `0 ≤ s`, the depth of `posNormalIioRay hS s` is `s`. -/
theorem posNormalIioRay_coe_apply_of_nonneg (hS : (S : Set ℝ) ⊆ Iio 1) {s : S}
    (hs : 0 ≤ (s : ℝ)) : (posNormalIioRay hS s : EuclideanHalfSpace 1).val 0 = s := by
  rw [posNormalIioRay_def, normalIioRay_coe_apply_of_nonneg _ hs]

/-- The point `posNormalIioRay hS s` is the origin exactly when `s ≤ 0`. -/
theorem posNormalIioRay_eq_zero_iff (hS : (S : Set ℝ) ⊆ Iio 1) {s : S} :
    posNormalIioRay hS s = normalIioOpensZero one_pos ↔ (s : ℝ) ≤ 0 := by
  rw [posNormalIioRay_def, normalIioRay_eq_zero_iff]

/-- The depth map on `S` is continuous. -/
theorem continuous_posNormalIioRay (hS : (S : Set ℝ) ⊆ Iio 1) :
    Continuous (posNormalIioRay hS) :=
  continuous_normalIioRay.comp (continuous_subtypeVal.subtype_mk _)

/-- For an open set `S` of reals containing `[0, 1)`, the point `t` of `S` at a depth
`t ∈ [0, 1)`. It is a right inverse of `posNormalIioRay` (`posNormalIioRay_posNormalCoord`), and
a left inverse on `S ∩ [0, ∞)` (`posNormalCoord_posNormalIioRay`). -/
def posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) : S :=
  ⟨(t : EuclideanHalfSpace 1).val 0,
    hS ⟨(t : EuclideanHalfSpace 1).property, mem_normalIioOpens.1 t.property⟩⟩

theorem posNormalCoord_def (hS : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    posNormalCoord hS t = ⟨(t : EuclideanHalfSpace 1).val 0,
      hS ⟨(t : EuclideanHalfSpace 1).property, mem_normalIioOpens.1 t.property⟩⟩ := (rfl)

/-- Read in `ℝ`, the map `posNormalCoord hS` is `s ↦ s 0` on the points of `[0, 1)`. -/
theorem val_comp_posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ)) :
    Subtype.val ∘ posNormalCoord hS =
      (fun s : EuclideanHalfSpace 1 ↦ s.val 0) ∘ Subtype.val := (rfl)

/-- The point `posNormalCoord hS t` is the depth of `t`. -/
@[simp]
theorem coe_posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    (posNormalCoord hS t : ℝ) = (t : EuclideanHalfSpace 1).val 0 := (rfl)

/-- The point `posNormalCoord hS t` is at least `0`. -/
theorem posNormalCoord_nonneg (hS : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    0 ≤ (posNormalCoord hS t : ℝ) := by
  rw [coe_posNormalCoord]
  exact (t : EuclideanHalfSpace 1).property

/-- At a positive depth `t`, the point `posNormalCoord hS t` is positive. -/
theorem posNormalCoord_pos (hS : Ico 0 1 ⊆ (S : Set ℝ)) {t : normalIioOpens 1}
    (ht : 0 < (t : EuclideanHalfSpace 1).val 0) : 0 < (posNormalCoord hS t : ℝ) := by
  rwa [coe_posNormalCoord]

/-- The map `t ↦ t` from depths into `S` is continuous. -/
theorem continuous_posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ)) :
    Continuous (posNormalCoord hS) :=
  Continuous.subtype_mk (by fun_prop) _

/-- The depth of `t` is `t`. -/
@[simp]
theorem posNormalIioRay_posNormalCoord (hS : (S : Set ℝ) ⊆ Iio 1)
    (hS' : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    posNormalIioRay hS (posNormalCoord hS' t) = t :=
  Subtype.ext (by simp [posNormalIioRay_def, normalRay_normalCoord])

/-- For `0 ≤ s`, the point `t` at the depth `t = s` is `s`. -/
theorem posNormalCoord_posNormalIioRay (hS : (S : Set ℝ) ⊆ Iio 1)
    (hS' : Ico 0 1 ⊆ (S : Set ℝ)) {s : S} (hs : 0 ≤ (s : ℝ)) :
    posNormalCoord hS' (posNormalIioRay hS s) = s :=
  Subtype.ext (by rw [coe_posNormalCoord, posNormalIioRay_coe_apply_of_nonneg hS hs])

/-! ### Smoothness of the coordinate maps -/

variable {n : WithTop ℕ∞}

open Manifold

/-- The map `t ↦ -t` from depths into `S` is a `C^n` immersion, the depth `0` included. -/
theorem isImmersionAt_negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    IsImmersionAt (𝓡∂ 1) 𝓘(ℝ) n (negNormalCoord hS) t := by
  rw [funext (negNormalCoord_def hS)]
  refine (isImmersionAt_codRestrict_opens_iff
    (f := fun t : normalIioOpens 1 ↦ -(t : EuclideanHalfSpace 1).val 0)
    fun t ↦ (negNormalCoord hS t).property).2 ?_
  refine (isImmersionAt_comp_subtypeVal_iff (f := fun t : EuclideanHalfSpace 1 ↦ -t.val 0)).2 ?_
  exact isImmersionAt_isLocalDiffeomorphAt_comp (f := fun s : EuclideanHalfSpace 1 ↦ s.val 0)
    (SymplecticGeometry.isLocalDiffeomorph_neg _) (isImmersionAt_val_zero _)

/-- The map `t ↦ t` from depths into `S` is a `C^n` immersion, the depth `0` included. -/
theorem isImmersionAt_posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ)) (t : normalIioOpens 1) :
    IsImmersionAt (𝓡∂ 1) 𝓘(ℝ) n (posNormalCoord hS) t := by
  rw [funext (posNormalCoord_def hS)]
  refine (isImmersionAt_codRestrict_opens_iff
    (f := fun t : normalIioOpens 1 ↦ (t : EuclideanHalfSpace 1).val 0)
    fun t ↦ (posNormalCoord hS t).property).2 ?_
  exact (isImmersionAt_comp_subtypeVal_iff (f := fun t : EuclideanHalfSpace 1 ↦ t.val 0)).2
    (isImmersionAt_val_zero _)

/-- At a positive depth, the map `t ↦ -t` from depths into `S` is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_negNormalCoord (hS : Ioc (-1) 0 ⊆ (S : Set ℝ))
    {t : normalIioOpens 1} (ht : 0 < (t : EuclideanHalfSpace 1).val 0) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) n (negNormalCoord hS) t := by
  refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
  rw [val_comp_negNormalCoord]
  exact (isLocalDiffeomorphAt_opens_val_zero ht).comp
    (hg := SymplecticGeometry.isLocalDiffeomorph_neg _)

/-- At a positive depth, the map `t ↦ t` from depths into `S` is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorphAt_posNormalCoord (hS : Ico 0 1 ⊆ (S : Set ℝ))
    {t : normalIioOpens 1} (ht : 0 < (t : EuclideanHalfSpace 1).val 0) :
    IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ) n (posNormalCoord hS) t := by
  refine isLocalDiffeomorphAt_subtypeVal_comp_iff.1 ?_
  rw [val_comp_posNormalCoord]
  exact isLocalDiffeomorphAt_opens_val_zero ht

end SymplecticGeometry.EuclideanHalfSpace

namespace ContMDiffAt

open TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The depth map composed with a `C^n` real function `f < 1` is `C^n` at a point where `f` is
positive. -/
theorem normalIioRay {n : WithTop ℕ∞} {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) n f x)
    (h1 : ∀ y, f y < 1) (hx : 0 < f x) :
    ContMDiffAt I (𝓡∂ 1) n (fun y ↦ normalIioRay ⟨f y, h1 y⟩) x :=
  (TauCeti.ContMDiffAt.subtypeVal_comp_iff _ _ _).1
    ((contMDiffOn_normalRay.contMDiffAt (Ici_mem_nhds hx)).comp x hf)

end ContMDiffAt

end
