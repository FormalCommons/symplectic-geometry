/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.End
public import TauCeti.Geometry.Manifold.Gluing.Basic
public import TauCeti.Topology.Constructions.DoubleAlong.Separation
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The double of a manifold along a smooth collar

For a manifold `W` with boundary, modelled on the half-space, and a smooth collar `c` of its
boundary, the double `c.Double` is Tau Ceti's topological double `TauCeti.DoubleAlong` of `W`
along `∂W`: two copies of `W` glued by the identity along the boundary. The collar gives it the
structure of a smooth manifold without boundary over `ℝⁿ⁺¹`, glued (by Tau Ceti's
`TauCeti.chartedSpaceOfIsOpenEmbedding`) from three open pieces: the two copies of the interior of
`W`, re-modelled as `SymplecticGeometry.InteriorModel`, and the band `(-1, 1) × ∂W`,
re-modelled along `TauCeti.SmoothCollar.endModelDiffeomorph`. The point `(s, x)` of the band is
the collar point `c (x, -s)` of the first copy for `s ≤ 0`, and `c (x, s)` of the second copy for
`s ≥ 0`; so the collar coordinate is reflected from one copy to the other.

The transition maps between the pieces are read in `c.WithEnd` (`Boundary/Collar/End.lean`): in
it, the first copy of the interior and the band are the interior of `W` and a part of its end,
and the same holds for the second copy and the band reflected by `s ↦ -s`. Each transition map
is then a local inverse of a local diffeomorphism into `c.WithEnd` composed with another
(`IsLocalDiffeomorphAt.exists_contMDiffAt_transition`).

The type `c.Double` is a definition that keeps `c`, since its smooth structure depends on `c`;
its topology is that of `TauCeti.DoubleAlong` (`Double.homeomorphDoubleAlong`), with the two
copies of `W` as `Double.inl` and `Double.inr`.

## Main definitions

* `TauCeti.SmoothCollar.Double`: the double of `W` along `c`, with its smooth structure
  `Double.instChartedSpace`, `Double.instIsManifold`.
* `TauCeti.SmoothCollar.Double.inl`, `Double.inr`: the two copies of `W`;
  `Double.inlInterior`, `Double.inrInterior`: the two copies of its interior.
* `TauCeti.SmoothCollar.Double.bandMap`: the band `(-1, 1) × ∂W` in the double.
* `TauCeti.SmoothCollar.Double.bandProj`: the projection of the band onto `∂W`.

## Main results

* `TauCeti.SmoothCollar.Double.isOpenEmbedding_inlInterior`, `isOpenEmbedding_inrInterior`,
  `isLocalDiffeomorph_inlInterior`, `isLocalDiffeomorph_inrInterior`.
* `TauCeti.SmoothCollar.Double.bandMap_of_nonpos`, `bandMap_of_nonneg`: the gluing formulas;
  `injOn_bandMap`, `isOpen_bandMap_image`, `isLocalDiffeomorphOn_bandMap` on
  `(-1, 1) × ∂W`.
* `TauCeti.SmoothCollar.Double.range_inlInterior_union_range_inrInterior_union`: the three pieces
  cover the double; `disjoint_range_inlInterior_inrInterior`.
* `TauCeti.SmoothCollar.Double.bandProj_bandMap`, `contMDiffOn_bandProj`.

The construction follows the gluing of `TauCeti.SmoothCollar.WithEnd`, and the open embeddings of
the interiors follow Tau Ceti's `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInl`.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218, 2013,
  Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Function Topology Manifold TopologicalSpace SymplecticGeometry
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar
open _root_.TauCeti.EuclideanHalfSpace

universe u

variable {n : ℕ} {W : Type u} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]

/-- The double of `W` along the smooth collar `c`: two copies of `W` glued by the identity along
the boundary `∂W`, Tau Ceti's `TauCeti.DoubleAlong`. The collar `c` determines its smooth
structure (`TauCeti.SmoothCollar.Double.instChartedSpace`). -/
@[nolint unusedArguments]
def Double (_c : SmoothCollar n ∞ W) : Type u := DoubleAlong ((𝓡∂ (n + 1)).boundary W)

variable (c : SmoothCollar n ∞ W)

instance : TopologicalSpace c.Double :=
  inferInstanceAs (TopologicalSpace (DoubleAlong ((𝓡∂ (n + 1)).boundary W)))

namespace Double

/-- The first copy of `W` in the double. -/
def inl : C(W, c.Double) := DoubleAlong.inl ((𝓡∂ (n + 1)).boundary W)

/-- The second copy of `W` in the double. -/
def inr : C(W, c.Double) := DoubleAlong.inr ((𝓡∂ (n + 1)).boundary W)

/- `c.Double` is `DoubleAlong _` by definition: the proofs below use the API of `DoubleAlong`
through these two equalities. -/
private theorem coe_inl : ⇑(inl c) = DoubleAlong.inl ((𝓡∂ (n + 1)).boundary W) := (rfl)

private theorem coe_inr : ⇑(inr c) = DoubleAlong.inr ((𝓡∂ (n + 1)).boundary W) := (rfl)

/-- The two copies of a boundary point are the same point of the double. -/
theorem inl_coe_eq_inr (x : (𝓡∂ (n + 1)).boundary W) : inl c x = inr c x := by
  rw [coe_inl, coe_inr]
  exact DoubleAlong.inl_coe_eq_inr _ x

/-- The first copy of `W` is injective. -/
theorem inl_injective : Injective (inl c) := fun _ _ h ↦ by
  rw [coe_inl] at h
  exact (DoubleAlong.inl_eq_inl_iff _).1 h

/-- The second copy of `W` is injective. -/
theorem inr_injective : Injective (inr c) := fun _ _ h ↦ by
  rw [coe_inr] at h
  exact (DoubleAlong.inr_eq_inr_iff _).1 h

/-- Two points of the first copy are equal exactly when the points of `W` are. -/
@[simp]
theorem inl_eq_inl_iff {x y : W} : inl c x = inl c y ↔ x = y := (inl_injective c).eq_iff

/-- Two points of the second copy are equal exactly when the points of `W` are. -/
@[simp]
theorem inr_eq_inr_iff {x y : W} : inr c x = inr c y ↔ x = y := (inr_injective c).eq_iff

/-- A point of the first copy is a point of the second exactly on the boundary. -/
@[simp]
theorem inl_eq_inr_iff {x y : W} : inl c x = inr c y ↔ x = y ∧ x ∈ (𝓡∂ (n + 1)).boundary W := by
  rw [coe_inl, coe_inr]
  exact DoubleAlong.inl_eq_inr_iff _

/-- Every point of the double lies on one of the two copies of `W`. -/
theorem exists_inl_or_inr (z : c.Double) : (∃ x, inl c x = z) ∨ ∃ x, inr c x = z := by
  rw [coe_inl, coe_inr]
  exact DoubleAlong.exists_inl_or_inr _ z

/-- A set is open in the double exactly when its preimages in both copies of `W` are open. -/
theorem isOpen_iff {s : Set c.Double} : IsOpen s ↔ IsOpen (inl c ⁻¹' s) ∧ IsOpen (inr c ⁻¹' s) := by
  refine ⟨fun h ↦ ⟨h.preimage (inl c).continuous, h.preimage (inr c).continuous⟩,
    fun ⟨h₁, h₂⟩ ↦ isClosed_compl_iff.1 ?_⟩
  rw [coe_inl] at h₁
  rw [coe_inr] at h₂
  -- The topology of `c.Double` is that of `DoubleAlong`, by definition.
  exact (DoubleAlong.isClosed_iff _ sᶜ).2 ⟨h₁.isClosed_compl, h₂.isClosed_compl⟩

/-- The double is Tau Ceti's double `TauCeti.DoubleAlong` of `W` along its boundary. -/
def homeomorphDoubleAlong : c.Double ≃ₜ DoubleAlong ((𝓡∂ (n + 1)).boundary W) :=
  Homeomorph.refl _

@[simp]
theorem homeomorphDoubleAlong_inl (x : W) :
    homeomorphDoubleAlong c (inl c x) = DoubleAlong.inl _ x :=
  (rfl)

@[simp]
theorem homeomorphDoubleAlong_inr (x : W) :
    homeomorphDoubleAlong c (inr c x) = DoubleAlong.inr _ x :=
  (rfl)

/-! ### Depths in the collar -/

/-- The open interval `(-1, 1)`, the range of the first coordinate of the band. -/
private def bandInterval : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩

private theorem mem_bandInterval {s : ℝ} : s ∈ bandInterval ↔ s ∈ Ioo (-1) 1 := Iff.rfl

private theorem bandInterval_subset : (bandInterval : Set ℝ) ⊆ Ioi (-1) :=
  fun _ h ↦ (mem_bandInterval.1 h).1

private theorem Ioc_subset_bandInterval : Ioc (-1) 0 ⊆ (bandInterval : Set ℝ) :=
  fun _ h ↦ mem_bandInterval.2 ⟨h.1, h.2.trans_lt one_pos⟩

private theorem bandInterval_subset_Iio : (bandInterval : Set ℝ) ⊆ Iio 1 :=
  fun _ h ↦ (mem_bandInterval.1 h).2

private theorem Ico_subset_bandInterval : Ico 0 1 ⊆ (bandInterval : Set ℝ) :=
  fun _ h ↦ mem_bandInterval.2 ⟨neg_one_lt_zero.trans_le h.1, h.2⟩

/-! ### The band as a subset of the double -/

/-- The point `(s, x)` of `(-1, 1) × ∂W` in the double: `c (x, -s)` in the first copy for
`s ≤ 0`, and `c (x, s)` in the second copy for `0 < s`. -/
private def bandPt (p : bandInterval × (𝓡∂ (n + 1)).boundary W) : c.Double :=
  if (p.1 : ℝ) ≤ 0 then inl c (c (p.2, negNormalIioRay bandInterval_subset p.1))
  else inr c (c (p.2, posNormalIioRay bandInterval_subset_Iio p.1))

private theorem inl_negNormalIioRay_eq_inr_posNormalIioRay {s : bandInterval} (hs : (s : ℝ) = 0)
    (x : (𝓡∂ (n + 1)).boundary W) :
    inl c (c (x, negNormalIioRay bandInterval_subset s)) =
      inr c (c (x, posNormalIioRay bandInterval_subset_Iio s)) := by
  rw [(negNormalIioRay_eq_zero_iff bandInterval_subset).2 hs.ge,
    (posNormalIioRay_eq_zero_iff bandInterval_subset_Iio).2 hs.le,
    c.apply_zero, inl_coe_eq_inr]

private theorem bandPt_of_nonpos {s : bandInterval} (hs : (s : ℝ) ≤ 0)
    (x : (𝓡∂ (n + 1)).boundary W) :
    bandPt c (s, x) = inl c (c (x, negNormalIioRay bandInterval_subset s)) :=
  ite_eq_left_iff.2 fun h ↦ absurd hs h

private theorem bandPt_of_nonneg {s : bandInterval} (hs : 0 ≤ (s : ℝ))
    (x : (𝓡∂ (n + 1)).boundary W) :
    bandPt c (s, x) = inr c (c (x, posNormalIioRay bandInterval_subset_Iio s)) := by
  rcases hs.eq_or_lt with h | h
  · rw [bandPt_of_nonpos c h.ge, inl_negNormalIioRay_eq_inr_posNormalIioRay c h.symm]
  · exact ite_eq_right_iff.2 fun h' ↦ absurd h' (not_le.2 h)

private theorem continuous_bandPt : Continuous (bandPt c) :=
  Continuous.if_le
    ((inl c).continuous.comp (c.continuous.comp
      (continuous_snd.prodMk
        ((continuous_negNormalIioRay bandInterval_subset).comp continuous_fst))))
    ((inr c).continuous.comp (c.continuous.comp
      (continuous_snd.prodMk
        ((continuous_posNormalIioRay bandInterval_subset_Iio).comp continuous_fst))))
    (continuous_subtypeVal.comp continuous_fst) continuous_const
    fun p hp ↦ inl_negNormalIioRay_eq_inr_posNormalIioRay c hp p.2

/-- A collar point in both copies of `W` is a boundary point. -/
private theorem inl_eq_inr_collar {x y : (𝓡∂ (n + 1)).boundary W} {t u : normalIioOpens 1}
    (h : inl c (c (x, t)) = inr c (c (y, u))) :
    x = y ∧ t = normalIioOpensZero one_pos ∧ u = normalIioOpensZero one_pos := by
  obtain ⟨h₁, h₂⟩ := (inl_eq_inr_iff c).1 h
  have hu := (c.apply_mem_boundary_iff _).1 (h₁ ▸ h₂)
  have ht := (c.apply_mem_boundary_iff _).1 h₂
  exact ⟨congrArg Prod.fst (c.injective h₁), ht, hu⟩

private theorem bandPt_injective : Injective (bandPt c) := by
  rintro ⟨s, x⟩ ⟨s', x'⟩ h
  rcases le_total (s : ℝ) 0 with hs | hs <;> rcases le_total (s' : ℝ) 0 with hs' | hs'
  · rw [bandPt_of_nonpos c hs, bandPt_of_nonpos c hs'] at h
    have h' := c.injective (inl_injective c h)
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, ht⟩ := h'
    rw [← negNormalCoord_negNormalIioRay bandInterval_subset Ioc_subset_bandInterval hs,
      ← negNormalCoord_negNormalIioRay bandInterval_subset Ioc_subset_bandInterval hs', ht]
  · rw [bandPt_of_nonpos c hs, bandPt_of_nonneg c hs'] at h
    obtain ⟨rfl, ht, hu⟩ := inl_eq_inr_collar c h
    exact Prod.ext (Subtype.ext
      ((le_antisymm hs ((negNormalIioRay_eq_zero_iff bandInterval_subset).1 ht)).trans
        (le_antisymm ((posNormalIioRay_eq_zero_iff bandInterval_subset_Iio).1 hu) hs').symm)) rfl
  · rw [bandPt_of_nonneg c hs, bandPt_of_nonpos c hs'] at h
    obtain ⟨rfl, ht, hu⟩ := inl_eq_inr_collar c h.symm
    exact Prod.ext (Subtype.ext
      ((le_antisymm ((posNormalIioRay_eq_zero_iff bandInterval_subset_Iio).1 hu) hs).trans
      (le_antisymm hs' ((negNormalIioRay_eq_zero_iff bandInterval_subset).1 ht)).symm)) rfl
  · rw [bandPt_of_nonneg c hs, bandPt_of_nonneg c hs'] at h
    have h' := c.injective (inr_injective c h)
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, ht⟩ := h'
    rw [← posNormalCoord_posNormalIioRay bandInterval_subset_Iio Ico_subset_bandInterval hs,
      ← posNormalCoord_posNormalIioRay bandInterval_subset_Iio Ico_subset_bandInterval hs', ht]

private theorem preimage_inl_image_bandPt (U : Set (bandInterval × (𝓡∂ (n + 1)).boundary W)) :
    inl c ⁻¹' (bandPt c '' U) =
      c '' ((fun p ↦ (negNormalCoord Ioc_subset_bandInterval p.2, p.1)) ⁻¹' U) := by
  ext w
  constructor
  · rintro ⟨⟨s, x⟩, hU, h⟩
    rcases le_or_gt (s : ℝ) 0 with hs | hs
    · rw [bandPt_of_nonpos c hs] at h
      refine ⟨(x, negNormalIioRay bandInterval_subset s), ?_, inl_injective c h⟩
      rwa [mem_preimage,
        negNormalCoord_negNormalIioRay bandInterval_subset Ioc_subset_bandInterval hs]
    · rw [bandPt_of_nonneg c hs.le] at h
      obtain ⟨rfl, hw⟩ := (inl_eq_inr_iff c).1 h.symm
      exact absurd ((posNormalIioRay_eq_zero_iff bandInterval_subset_Iio).1
        ((c.apply_mem_boundary_iff _).1 hw)) (not_le.2 hs)
  · rintro ⟨⟨x, t⟩, hU, rfl⟩
    refine ⟨(negNormalCoord Ioc_subset_bandInterval t, x), hU, ?_⟩
    rw [bandPt_of_nonpos c (negNormalCoord_nonpos _ t), negNormalIioRay_negNormalCoord]

private theorem preimage_inr_image_bandPt (U : Set (bandInterval × (𝓡∂ (n + 1)).boundary W)) :
    inr c ⁻¹' (bandPt c '' U) =
      c '' ((fun p ↦ (posNormalCoord Ico_subset_bandInterval p.2, p.1)) ⁻¹' U) := by
  ext w
  constructor
  · rintro ⟨⟨s, x⟩, hU, h⟩
    rcases le_or_gt 0 (s : ℝ) with hs | hs
    · rw [bandPt_of_nonneg c hs] at h
      refine ⟨(x, posNormalIioRay bandInterval_subset_Iio s), ?_, inr_injective c h⟩
      rwa [mem_preimage,
        posNormalCoord_posNormalIioRay bandInterval_subset_Iio Ico_subset_bandInterval hs]
    · rw [bandPt_of_nonpos c hs.le] at h
      obtain ⟨-, hw⟩ := (inl_eq_inr_iff c).1 h
      exact absurd ((negNormalIioRay_eq_zero_iff bandInterval_subset).1
        ((c.apply_mem_boundary_iff _).1 hw)) (not_le.2 hs)
  · rintro ⟨⟨x, t⟩, hU, rfl⟩
    refine ⟨(posNormalCoord Ico_subset_bandInterval t, x), hU, ?_⟩
    rw [bandPt_of_nonneg c (posNormalCoord_nonneg _ t), posNormalIioRay_posNormalCoord]

private theorem isOpenEmbedding_bandPt : IsOpenEmbedding (bandPt c) := by
  refine .of_continuous_injective_isOpenMap (continuous_bandPt c) (bandPt_injective c)
    fun U hU ↦ (isOpen_iff c).2 ⟨?_, ?_⟩
  · rw [preimage_inl_image_bandPt]
    exact c.isOpenEmbedding.isOpenMap _
      (hU.preimage ((continuous_negNormalCoord Ioc_subset_bandInterval).comp continuous_snd
        |>.prodMk continuous_fst))
  · rw [preimage_inr_image_bandPt]
    exact c.isOpenEmbedding.isOpenMap _
      (hU.preimage ((continuous_posNormalCoord Ico_subset_bandInterval).comp continuous_snd
        |>.prodMk continuous_fst))

private theorem bandPt_zero (x : (𝓡∂ (n + 1)).boundary W) :
    bandPt c (⟨0, by simp [mem_bandInterval]⟩, x) = inl c x := by
  rw [bandPt_of_nonpos c le_rfl, (negNormalIioRay_eq_zero_iff bandInterval_subset).2 le_rfl,
    c.apply_zero]

/-- The point `(s, x)` of the band `(-1, 1) × ∂W` in the double: the collar point `c (x, -s)` of
the first copy of `W` for `s ≤ 0`, and the collar point `c (x, s)` of the second copy for
`s ≥ 0`. Its values for `s ∉ (-1, 1)` are junk. -/
def bandMap (p : ℝ × (𝓡∂ (n + 1)).boundary W) : c.Double :=
  if h : p.1 ∈ Ioo (-1) 1 then bandPt c (⟨p.1, h⟩, p.2) else inl c p.2

private theorem bandMap_coe (p : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    bandMap c ((p.1 : ℝ), p.2) = bandPt c p := by
  rw [bandMap, dite_eq_left (mem_bandInterval.1 p.1.property)]

/-- For `s ∈ (-1, 0]`, the point `(s, x)` of the band is the collar point `c (x, -s)` of the first
copy of `W`. -/
theorem bandMap_of_nonpos {s : ℝ} (hs : s ≤ 0) (hs' : -1 < s) (x : (𝓡∂ (n + 1)).boundary W) :
    bandMap c (s, x) = inl c (c (x, normalIioRay ⟨-s, by rw [mem_Iio]; linarith⟩)) := by
  rw [bandMap_coe c (⟨s, ⟨hs', by linarith⟩⟩, x), bandPt_of_nonpos c hs, negNormalIioRay_def]

/-- For `s ∈ [0, 1)`, the point `(s, x)` of the band is the collar point `c (x, s)` of the second
copy of `W`. -/
theorem bandMap_of_nonneg {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) (x : (𝓡∂ (n + 1)).boundary W) :
    bandMap c (s, x) = inr c (c (x, normalIioRay ⟨s, hs'⟩)) := by
  rw [bandMap_coe c (⟨s, ⟨by linarith, hs'⟩⟩, x), bandPt_of_nonneg c hs, posNormalIioRay_def]

/-- The point `(0, x)` of the band is the boundary point `x` of `W`. -/
@[simp]
theorem bandMap_zero (x : (𝓡∂ (n + 1)).boundary W) : bandMap c (0, x) = inl c x := by
  rw [bandMap_coe c (⟨0, by simp [mem_bandInterval]⟩, x), bandPt_zero]

/-- On `(-1, 1) × ∂W`, the band map is injective. -/
theorem injOn_bandMap : InjOn (bandMap c) (Ioo (-1) 1 ×ˢ univ) := by
  rintro ⟨s, x⟩ ⟨hs, -⟩ ⟨s', x'⟩ ⟨hs', -⟩ h
  have h' := bandPt_injective c ((bandMap_coe c (⟨s, hs⟩, x)).symm.trans
    (h.trans (bandMap_coe c (⟨s', hs'⟩, x'))))
  simp only [Prod.mk.injEq] at h'
  exact Prod.ext (congrArg Subtype.val h'.1) h'.2

private theorem bandMap_image_eq {U : Set (ℝ × (𝓡∂ (n + 1)).boundary W)}
    (hU : U ⊆ Ioo (-1) 1 ×ˢ univ) :
    bandMap c '' U = bandPt c '' (Prod.map Subtype.val id ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨⟨s, x⟩, hp, rfl⟩
    exact ⟨(⟨s, (hU hp).1⟩, x), hp, (bandMap_coe c (⟨s, (hU hp).1⟩, x)).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨((p.1 : ℝ), p.2), hp, bandMap_coe c p⟩

/-- The band map sends open subsets of `(-1, 1) × ∂W` to open subsets of the double. -/
theorem isOpen_bandMap_image {U : Set (ℝ × (𝓡∂ (n + 1)).boundary W)}
    (hU : U ⊆ Ioo (-1) 1 ×ˢ univ) (ho : IsOpen U) : IsOpen (bandMap c '' U) := by
  rw [bandMap_image_eq c hU]
  exact (isOpenEmbedding_bandPt c).isOpenMap _
    (ho.preimage (continuous_subtypeVal.prodMap continuous_id))

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

local instance : IsManifold (𝓡 n) ∞ ((𝓡∂ (n + 1)).boundary W) := isManifold_boundary W

/-! ### The pieces -/

variable (n W) in
/-- The interior of `W`, as a boundaryless manifold over `ℝⁿ⁺¹`. -/
private abbrev InteriorPiece : Type u :=
  InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)

variable (n W) in
/-- The band `(-1, 1) × ∂W`, re-modelled on `ℝⁿ⁺¹`. -/
private abbrev BandPiece : Type u :=
  Remodel (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W)

/-- The point of the double at a point of the band. -/
private def bandIncl (q : BandPiece n W) : c.Double :=
  bandPt c ((remodelDiffeomorph (endModelDiffeomorph n) _).symm q)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandIncl_remodel (p : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    bandIncl c (remodelDiffeomorph (endModelDiffeomorph n) _ p) = bandPt c p := by
  rw [bandIncl, Diffeomorph.symm_apply_apply]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem isOpenEmbedding_bandIncl : IsOpenEmbedding (bandIncl c (n := n)) :=
  (isOpenEmbedding_bandPt c).comp
    (remodelDiffeomorph (endModelDiffeomorph n) _).symm.toHomeomorph.isOpenEmbedding

/-- The first copy of the interior of `W` in the double. -/
def inlInterior (p : InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)) : c.Double :=
  inl c p.val

/-- The second copy of the interior of `W` in the double. -/
def inrInterior (p : InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)) : c.Double :=
  inr c p.val

@[simp]
theorem inlInterior_apply (p : InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)) :
    inlInterior c p = inl c p.val :=
  (rfl)

@[simp]
theorem inrInterior_apply (p : InteriorModel (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).interiorOpens W)) :
    inrInterior c p = inr c p.val :=
  (rfl)

/-- The copy of the interior of `W`, as the complement of the boundary. -/
private def interiorToCompl (p : InteriorPiece n W) : ↥((𝓡∂ (n + 1)).boundary W)ᶜ :=
  ⟨p.val, by rw [ModelWithCorners.compl_boundary]; exact p.val_mem_interior⟩

private theorem isOpenEmbedding_interiorToCompl :
    IsOpenEmbedding (interiorToCompl (n := n) (W := W)) := by
  refine (InteriorModel.isOpenEmbedding_val.isEmbedding.codRestrict _ _
    ).isOpenEmbedding_of_surjective fun x ↦ ?_
  have hx : (x : W) ∈ (𝓡∂ (n + 1)).interior W := by
    rw [← ModelWithCorners.compl_boundary]; exact x.property
  exact ⟨InteriorModel.mk _ x hx, Subtype.ext (InteriorModel.val_mk _ _)⟩

/-- The first copy of the interior of `W` is an open embedding into the double. -/
theorem isOpenEmbedding_inlInterior : IsOpenEmbedding (inlInterior c) :=
  (DoubleAlong.isOpenEmbedding_inl_compl _ ((𝓡∂ (n + 1)).isClosed_boundary
    (n := ∞) (by simp))).comp isOpenEmbedding_interiorToCompl

/-- The second copy of the interior of `W` is an open embedding into the double. -/
theorem isOpenEmbedding_inrInterior : IsOpenEmbedding (inrInterior c) :=
  (DoubleAlong.isOpenEmbedding_inr_compl _ ((𝓡∂ (n + 1)).isClosed_boundary
    (n := ∞) (by simp))).comp isOpenEmbedding_interiorToCompl

/-! ### The smooth structure -/

/-- The three pieces of the double: the two copies of the interior of `W`, and the band. -/
private inductive Piece
  | inl | inr | band

variable (n W) in
/-- The manifold of a piece. -/
private def piece : Piece → Type u
  | .inl | .inr => InteriorPiece n W
  | .band => BandPiece n W

private instance instTopologicalSpacePiece : ∀ j, TopologicalSpace (piece n W j)
  | .inl | .inr => inferInstanceAs (TopologicalSpace (InteriorPiece n W))
  | .band => inferInstanceAs (TopologicalSpace (BandPiece n W))

private instance instChartedSpacePiece :
    ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (piece n W j)
  | .inl | .inr => inferInstanceAs (ChartedSpace _ (InteriorPiece n W))
  | .band => inferInstanceAs (ChartedSpace _ (BandPiece n W))

private instance instIsManifoldPiece : ∀ j, IsManifold (𝓡 (n + 1)) ∞ (piece n W j)
  | .inl | .inr => inferInstanceAs (IsManifold _ ∞ (InteriorPiece n W))
  | .band => inferInstanceAs (IsManifold _ ∞ (BandPiece n W))

/-- The map of a piece into the double. -/
private def pieceMap : ∀ j, piece n W j → c.Double
  | .inl => inlInterior c
  | .inr => inrInterior c
  | .band => bandIncl c

private theorem isOpenEmbedding_pieceMap : ∀ j, IsOpenEmbedding (pieceMap c j)
  | .inl => isOpenEmbedding_inlInterior c
  | .inr => isOpenEmbedding_inrInterior c
  | .band => isOpenEmbedding_bandIncl c

private theorem exists_pieceMap_eq (z : c.Double) : ∃ j y, pieceMap c j y = z := by
  have h0 : (0 : ℝ) ∈ bandInterval := by simp [mem_bandInterval]
  rcases exists_inl_or_inr c z with ⟨w, rfl⟩ | ⟨w, rfl⟩ <;>
    by_cases hw : w ∈ (𝓡∂ (n + 1)).interior W
  · exact ⟨.inl, InteriorModel.mk _ w hw, congrArg (inl c) (InteriorModel.val_mk _ _)⟩
  · rw [← ModelWithCorners.compl_boundary, Set.notMem_compl_iff] at hw
    exact ⟨.band, remodelDiffeomorph (endModelDiffeomorph n)
      (bandInterval × (𝓡∂ (n + 1)).boundary W) (⟨0, h0⟩, ⟨w, hw⟩),
      (bandIncl_remodel c _).trans (bandPt_zero c ⟨w, hw⟩)⟩
  · exact ⟨.inr, InteriorModel.mk _ w hw, congrArg (inr c) (InteriorModel.val_mk _ _)⟩
  · rw [← ModelWithCorners.compl_boundary, Set.notMem_compl_iff] at hw
    exact ⟨.band, remodelDiffeomorph (endModelDiffeomorph n)
      (bandInterval × (𝓡∂ (n + 1)).boundary W) (⟨0, h0⟩, ⟨w, hw⟩),
      ((bandIncl_remodel c _).trans (bandPt_zero c ⟨w, hw⟩)).trans (inl_coe_eq_inr c ⟨w, hw⟩)⟩

/-! The transition maps between the pieces are read in `c.WithEnd`: the first copy of the interior
and the band sit in it as the interior of `W` and the end piece `(-1, 1) × ∂W`, and so do the
second copy and the band reflected by `s ↦ -s`. -/

private theorem endMap_of_nonpos {s : bandInterval} (hs : (s : ℝ) ≤ 0)
    (x : (𝓡∂ (n + 1)).boundary W) :
    WithEnd.endMap c (s, x) =
      WithEnd.inclusion c (c (x, negNormalIioRay bandInterval_subset s)) := by
  have h := WithEnd.endMap_neg_eq_inclusion c x (negNormalIioRay bandInterval_subset s)
  rwa [negNormalIioRay_coe_apply_of_nonpos bandInterval_subset hs, neg_neg] at h

private theorem endMap_neg_of_nonneg {s : bandInterval} (hs : 0 ≤ (s : ℝ))
    (x : (𝓡∂ (n + 1)).boundary W) :
    WithEnd.endMap c (-s, x) =
      WithEnd.inclusion c (c (x, posNormalIioRay bandInterval_subset_Iio s)) := by
  have h := WithEnd.endMap_neg_eq_inclusion c x (posNormalIioRay bandInterval_subset_Iio s)
  rwa [posNormalIioRay_coe_apply_of_nonneg bandInterval_subset_Iio hs] at h

private theorem inl_eq_bandPt_iff (p : InteriorPiece n W)
    (q : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    inl c p.val = bandPt c q ↔ WithEnd.inclusion c p.val = WithEnd.endMap c (q.1, q.2) := by
  obtain ⟨s, x⟩ := q
  rcases le_total (s : ℝ) 0 with hs | hs
  · rw [bandPt_of_nonpos c hs, endMap_of_nonpos c hs]
    exact ⟨fun h ↦ congrArg _ (inl_injective c h),
      fun h ↦ congrArg _ (WithEnd.inclusion_injective c h)⟩
  · rw [bandPt_of_nonneg c hs]
    refine iff_of_false (fun h ↦ p.val_notMem_boundary ((inl_eq_inr_iff c).1 h).2) fun h ↦ ?_
    exact p.val_notMem_boundary ((WithEnd.eq_of_inclusion_eq_endMap c hs h).symm ▸ x.property)

private theorem inr_eq_bandPt_iff (p : InteriorPiece n W)
    (q : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    inr c p.val = bandPt c q ↔ WithEnd.inclusion c p.val = WithEnd.endMap c (-q.1, q.2) := by
  obtain ⟨s, x⟩ := q
  rcases le_total 0 (s : ℝ) with hs | hs
  · rw [bandPt_of_nonneg c hs, endMap_neg_of_nonneg c hs]
    exact ⟨fun h ↦ congrArg _ (inr_injective c h),
      fun h ↦ congrArg _ (WithEnd.inclusion_injective c h)⟩
  · rw [bandPt_of_nonpos c hs]
    refine iff_of_false (fun h ↦ ?_) fun h ↦ ?_
    · obtain ⟨h₁, h₂⟩ := (inl_eq_inr_iff c).1 h.symm
      exact p.val_notMem_boundary (h₁ ▸ h₂)
    · exact p.val_notMem_boundary
        ((WithEnd.eq_of_inclusion_eq_endMap c (neg_nonneg.2 hs) h).symm ▸ x.property)

/-- The interior of `W`, in `c.WithEnd`. -/
private def interiorEnd (p : InteriorPiece n W) : c.WithEnd := WithEnd.inclusion c p.val

private theorem isLocalDiffeomorph_interiorEnd :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (interiorEnd c) := fun p ↦
  (InteriorModel.isLocalDiffeomorph_val p).comp
    (hg := WithEnd.isLocalDiffeomorphAt_inclusion c p.val_mem_interior)

/-- The coordinates `(s, x)` of a point of the band, as a point of `ℝ × ∂W`. -/
private def bandCoord : BandPiece n W → ℝ × (𝓡∂ (n + 1)).boundary W :=
  Prod.map Subtype.val id ∘ (remodelDiffeomorph (endModelDiffeomorph n) _).symm

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandCoord_mem (q : BandPiece n W) : bandCoord q ∈ Ioo (-1) 1 ×ˢ univ :=
  ⟨((remodelDiffeomorph (endModelDiffeomorph n) _).symm q).1.property, trivial⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem bandMap_bandCoord (q : BandPiece n W) : bandMap c (bandCoord q) = bandIncl c q :=
  bandMap_coe c _

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem isLocalDiffeomorph_bandCoord :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓘(ℝ).prod (𝓡 n)) ∞ (bandCoord (n := n) (W := W)) :=
  fun q ↦ ((remodelDiffeomorph (endModelDiffeomorph n) _).symm.isLocalDiffeomorph q).comp
    (hg := (isLocalDiffeomorph_subtype_val.prodMap isLocalDiffeomorph_id) _)

/-- The band, in `c.WithEnd`. -/
private def bandEnd (q : BandPiece n W) : c.WithEnd := WithEnd.endMap c (bandCoord q)

/-- The band reflected by `s ↦ -s`, in `c.WithEnd`. -/
private def bandEndNeg (q : BandPiece n W) : c.WithEnd :=
  WithEnd.endMap c (Prod.map Neg.neg id (bandCoord q))

private theorem isLocalDiffeomorph_bandEnd :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (bandEnd c) := fun q ↦
  (isLocalDiffeomorph_bandCoord q).comp (hg := WithEnd.isLocalDiffeomorphOn_endMap c
    ⟨bandCoord q, (bandCoord_mem q).1.1, trivial⟩)

private theorem isLocalDiffeomorph_bandEndNeg :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (bandEndNeg c) := fun q ↦
  ((isLocalDiffeomorph_bandCoord q).comp
    (hg := ((ContinuousLinearEquiv.neg ℝ (M := ℝ)).toDiffeomorph.isLocalDiffeomorph _).prodMap
      (isLocalDiffeomorph_id _))).comp
    (hg := WithEnd.isLocalDiffeomorphOn_endMap c
      ⟨Prod.map Neg.neg id (bandCoord q), neg_lt_neg (bandCoord_mem q).1.2, trivial⟩)

private theorem exists_transition : ∀ (j k : Piece) (x : piece n W j) (y : piece n W k),
    pieceMap c j x = pieceMap c k y → ∃ T : piece n W j → piece n W k,
      ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T x ∧ pieceMap c k ∘ T =ᶠ[𝓝 x] pieceMap c j
  | .inl, .inl, _, _, _ | .inr, .inr, _, _, _ | .band, .band, _, _, _ =>
    ⟨id, contMDiffAt_id, .rfl⟩
  | .inl, .inr, x, _, h => absurd ((inl_eq_inr_iff c).1 h).2 x.val_notMem_boundary
  | .inr, .inl, _, y, h => absurd ((inl_eq_inr_iff c).1 h.symm).2 y.val_notMem_boundary
  | .inl, .band, x, y, h =>
    (isLocalDiffeomorph_interiorEnd c x).exists_contMDiffAt_transition
      (isLocalDiffeomorph_bandEnd c y) ((inl_eq_bandPt_iff c x _).1 h)
      fun u _ huv ↦ (inl_eq_bandPt_iff c u _).2 huv
  | .band, .inl, x, y, h =>
    (isLocalDiffeomorph_bandEnd c x).exists_contMDiffAt_transition
      (isLocalDiffeomorph_interiorEnd c y) ((inl_eq_bandPt_iff c y _).1 h.symm).symm
      fun _ v huv ↦ ((inl_eq_bandPt_iff c v _).2 huv.symm).symm
  | .inr, .band, x, y, h =>
    (isLocalDiffeomorph_interiorEnd c x).exists_contMDiffAt_transition
      (isLocalDiffeomorph_bandEndNeg c y) ((inr_eq_bandPt_iff c x _).1 h)
      fun u _ huv ↦ (inr_eq_bandPt_iff c u _).2 huv
  | .band, .inr, x, y, h =>
    (isLocalDiffeomorph_bandEndNeg c x).exists_contMDiffAt_transition
      (isLocalDiffeomorph_interiorEnd c y) ((inr_eq_bandPt_iff c y _).1 h.symm).symm
      fun _ v huv ↦ ((inr_eq_bandPt_iff c v _).2 huv.symm).symm

/-- The atlas of the double, glued from those of the two copies of the interior of `W` and of the
band `(-1, 1) × ∂W`. -/
@[instance_reducible]
def chartedSpaceDouble : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.Double :=
  chartedSpaceOfIsOpenEmbedding (isOpenEmbedding_pieceMap c) (exists_pieceMap_eq c)

instance instChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) c.Double :=
  chartedSpaceDouble c

/-- The double of `W` along a smooth collar is a smooth manifold without boundary. -/
instance instIsManifold : IsManifold (𝓡 (n + 1)) ∞ c.Double :=
  isManifold_chartedSpaceOfIsOpenEmbedding _ _ (exists_transition c)

private theorem isLocalDiffeomorph_pieceMap (j : Piece) :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (pieceMap c j) :=
  isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding _ _ (exists_transition c) j

/-- The first copy of the interior of `W` is a smooth local diffeomorphism into the double. -/
theorem isLocalDiffeomorph_inlInterior :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (inlInterior c) :=
  isLocalDiffeomorph_pieceMap c .inl

/-- The second copy of the interior of `W` is a smooth local diffeomorphism into the double. -/
theorem isLocalDiffeomorph_inrInterior :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (inrInterior c) :=
  isLocalDiffeomorph_pieceMap c .inr

/-- On `(-1, 1) × ∂W`, the band map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorphOn_bandMap :
    IsLocalDiffeomorphOn (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) ∞ (bandMap c) (Ioo (-1) 1 ×ˢ univ) := by
  rintro ⟨⟨s, x⟩, hs, -⟩
  let q : BandPiece n W := 
    remodelDiffeomorph (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W) (⟨s, hs⟩, x)
  have h : IsLocalDiffeomorphAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (bandMap c ∘ bandCoord) q := by
    rw [show bandMap c ∘ bandCoord = bandIncl c from funext (bandMap_bandCoord c)]
    exact isLocalDiffeomorph_pieceMap c .band q
  have hq : bandCoord q = (s, x) := by
    simp only [q, bandCoord, comp_apply, Diffeomorph.symm_apply_apply, Prod.map_apply, id_eq]
  have := h.of_comp_right (isLocalDiffeomorph_bandCoord q)
  rwa [hq] at this

/-- The two copies of the interior of `W` and the band cover the double. -/
theorem range_inlInterior_union_range_inrInterior_union :
    range (inlInterior c) ∪ range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨j, y, rfl⟩ := exists_pieceMap_eq c z
  cases j with
  | inl => exact Or.inl (Or.inl (mem_range_self y))
  | inr => exact Or.inl (Or.inr (mem_range_self y))
  | band => exact Or.inr ⟨bandCoord y, bandCoord_mem y, bandMap_bandCoord c y⟩

/-- The two copies of the interior of `W` are disjoint in the double. -/
theorem disjoint_range_inlInterior_inrInterior :
    Disjoint (range (inlInterior c)) (range (inrInterior c)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨p, rfl⟩ ⟨q, h⟩
  rw [inlInterior_apply, inrInterior_apply] at h
  exact p.val_notMem_boundary ((inl_eq_inr_iff c).1 h.symm).2

/-! ### The projection of the band onto the boundary -/

private instance : Nonempty (normalIioOpens 1) := ⟨normalIioOpensZero one_pos⟩

/-- The projection of the band of the double onto `∂W`: the collar point `c (x, t)` of either
copy of `W` goes to `x`. Off the band its values are junk, which needs a point of `∂W`. -/
def bandProj [Nonempty ((𝓡∂ (n + 1)).boundary W)] (z : c.Double) :
    (𝓡∂ (n + 1)).boundary W :=
  (invFun c (DoubleAlong.fold _ (homeomorphDoubleAlong c z))).1

variable [Nonempty ((𝓡∂ (n + 1)).boundary W)]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The projection of the band sends a collar point `c (x, t)` of the first copy to `x`. -/
@[simp]
theorem bandProj_inl_apply (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    bandProj c (inl c (c p)) = p.1 := by
  rw [bandProj, homeomorphDoubleAlong_inl, DoubleAlong.fold_inl, leftInverse_invFun c.injective]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The projection of the band sends a collar point `c (x, t)` of the second copy to `x`. -/
@[simp]
theorem bandProj_inr_apply (p : ↥((𝓡∂ (n + 1)).boundary W) × normalIioOpens 1) :
    bandProj c (inr c (c p)) = p.1 := by
  rw [bandProj, homeomorphDoubleAlong_inr, DoubleAlong.fold_inr, leftInverse_invFun c.injective]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The projection of the band sends the point `(s, x)` of the band to `x`. -/
theorem bandProj_bandMap {s : ℝ} (hs : s ∈ Ioo (-1) 1) (x : (𝓡∂ (n + 1)).boundary W) :
    bandProj c (bandMap c (s, x)) = x := by
  rcases le_total s 0 with h | h
  · rw [bandMap_of_nonpos c h hs.1, bandProj_inl_apply]
  · rw [bandMap_of_nonneg c h hs.2, bandProj_inr_apply]

/-- The projection of the band onto `∂W` is smooth on the band. -/
theorem contMDiffOn_bandProj :
    ContMDiffOn (𝓡 (n + 1)) (𝓡 n) ∞ (bandProj c) (bandMap c '' (Ioo (-1) 1 ×ˢ univ)) := by
  have himage : bandMap c '' (Ioo (-1) 1 ×ˢ univ) = range (pieceMap c .band) := by
    ext z
    constructor
    · rintro ⟨⟨s, x⟩, hs, rfl⟩
      exact ⟨remodelDiffeomorph (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W)
        (⟨s, hs.1⟩, x),
        (bandIncl_remodel c _).trans (bandMap_coe c (⟨s, hs.1⟩, x)).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨bandCoord q, bandCoord_mem q, bandMap_bandCoord c q⟩
  have hcomp (q : BandPiece n W) : bandProj c (bandIncl c q) = (bandCoord q).2 := by
    rw [← bandMap_bandCoord, bandProj_bandMap c (bandCoord_mem q).1]
  have : Nonempty (piece n W .band) :=
    ⟨remodelDiffeomorph (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W)
      (⟨0, by simp [mem_bandInterval]⟩, Classical.arbitrary _)⟩
  have hsymm := contMDiffOn_symm_chartedSpaceOfIsOpenEmbedding (isOpenEmbedding_pieceMap c)
    (exists_pieceMap_eq c) (exists_transition c) .band
  rw [himage]
  refine ((contMDiff_snd.comp (isLocalDiffeomorph_bandCoord.contMDiff)).comp_contMDiffOn
    hsymm).congr ?_
  rintro _ ⟨q, rfl⟩
  exact (hcomp q).trans (congrArg (Prod.snd ∘ bandCoord)
    ((isOpenEmbedding_pieceMap c .band).toOpenPartialHomeomorph_left_inv _ (x := q)).symm)

end Double

end TauCeti.SmoothCollar

end
