/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.End
public import TauCeti.Geometry.Manifold.Gluing.Basic
public import TauCeti.Topology.Constructions.DoubleAlong.Separation
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Local
public import TauCeti.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Interior
import SymplecticGeometry.Geometry.Manifold.Boundary.Charts

/-!
# The double of a manifold along a smooth collar

For a manifold `W` with boundary, modelled on the half-space, and a smooth collar `c` of its
boundary, the double `c.Double` is Tau Ceti's topological double `TauCeti.DoubleAlong` of `W`
along `∂W`: two copies of `W` glued by the identity along the boundary. The collar gives it the
structure of a smooth manifold without boundary over `ℝⁿ⁺¹`, glued (by Tau Ceti's
`TauCeti.chartedSpaceOfIsOpenEmbedding`) from three open pieces: the two copies of the interior of
`W`, as Tau Ceti's charted interior `(𝓡∂ (n + 1)).interior W`, and the band `(-1, 1) × ∂W`,
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
* `TauCeti.SmoothCollar.Double.bandInterval`, `Double.BandPiece`, `Double.bandIncl`: the
  interval `(-1, 1)`, the band `(-1, 1) × ∂W` re-modelled on `ℝⁿ⁺¹`, and its map into the
  double, one of the three pieces of the atlas.
* `TauCeti.SmoothCollar.Double.Piece`, `Double.piece`, `Double.pieceMap`: the three pieces of
  the atlas, the two copies `(𝓡∂ (n + 1)).interior W` of the interior and the band, as manifolds
  over `ℝⁿ⁺¹`, with their maps into the double.
* `TauCeti.SmoothCollar.Double.bandProj`: the projection of the band onto `∂W`.

## Main results

* `TauCeti.SmoothCollar.Double.isOpenEmbedding_inlInterior`, `isOpenEmbedding_inrInterior`,
  `isLocalDiffeomorph_inlInterior`, `isLocalDiffeomorph_inrInterior`.
* `TauCeti.SmoothCollar.Double.bandMap_of_nonpos`, `bandMap_of_nonneg`: the gluing formulas;
  `inl_apply_eq_bandMap`, `inr_apply_eq_bandMap`: collar points of the two copies on the band;
  `injOn_bandMap`, `isOpen_bandMap_image`, `isLocalDiffeomorphOn_bandMap` on
  `(-1, 1) × ∂W`.
* `TauCeti.SmoothCollar.Double.bandIncl_remodelDiffeomorph`, `range_bandIncl`,
  `isOpenEmbedding_bandIncl`, `isLocalDiffeomorph_bandIncl`: the band piece is the band map read
  on `(-1, 1) × ∂W`, and an open embedding and a local diffeomorphism.
* `TauCeti.SmoothCollar.Double.range_inlInterior_union_range_inrInterior_union`: the three pieces
  cover the double, as do the pieces (`iUnion_range_pieceMap`), each a local diffeomorphism
  (`isLocalDiffeomorph_pieceMap`); `disjoint_range_inlInterior_inrInterior`; `range_inlInterior`,
  `range_inrInterior`.
* `TauCeti.SmoothCollar.Double.bandMap_mem_range_inlInterior_iff`,
  `bandMap_mem_range_inrInterior_iff`: the point `(s, x)` of the band lies on the first copy of
  the interior exactly when `s < 0`, and on the second exactly when `0 < s`;
  `dense_range_inlInterior_union_range_inrInterior`: the two copies are dense.
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
open _root_.TauCeti.EuclideanHalfSpace SymplecticGeometry.EuclideanHalfSpace

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
def bandInterval : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩

@[simp]
theorem coe_bandInterval : (bandInterval : Set ℝ) = Ioo (-1) 1 := (rfl)

@[simp]
theorem mem_bandInterval {s : ℝ} : s ∈ bandInterval ↔ s ∈ Ioo (-1) 1 := Iff.rfl

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
    bandPt c (⟨0, by simp⟩, x) = inl c x := by
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
  rw [bandMap_coe c (⟨0, by simp⟩, x), bandPt_zero]

/-- The collar point `c (x, t)` of the first copy of `W` is the point `(-t, x)` of the band. -/
theorem inl_apply_eq_bandMap (x : (𝓡∂ (n + 1)).boundary W) (t : normalIioOpens 1) :
    inl c (c (x, t)) = bandMap c (-(t : EuclideanHalfSpace 1).val 0, x) := by
  have h1 := mem_normalIioOpens.1 t.property
  rw [bandMap_of_nonpos c (neg_nonpos.2 (t : EuclideanHalfSpace 1).property) (by linarith)]
  congr 3
  exact Subtype.ext (by simp [normalRay_normalCoord])

/-- The collar point `c (x, t)` of the second copy of `W` is the point `(t, x)` of the band. -/
theorem inr_apply_eq_bandMap (x : (𝓡∂ (n + 1)).boundary W) (t : normalIioOpens 1) :
    inr c (c (x, t)) = bandMap c ((t : EuclideanHalfSpace 1).val 0, x) := by
  rw [bandMap_of_nonneg c (t : EuclideanHalfSpace 1).property (mem_normalIioOpens.1 t.property)]
  congr 3
  exact Subtype.ext (by simp [normalRay_normalCoord])

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

/-! ### The pieces -/

variable (n W) in
/-- The band `(-1, 1) × ∂W`, re-modelled on `ℝⁿ⁺¹` along `endModelDiffeomorph`. -/
abbrev BandPiece : Type u :=
  Remodel (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W)

/-- The point of the double at a point `(s, x)` of the band, the point `bandMap c (s, x)`
(`bandIncl_remodelDiffeomorph`). -/
def bandIncl (q : BandPiece n W) : c.Double :=
  bandPt c ((remodelDiffeomorph (endModelDiffeomorph n) _).symm q)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The point `(s, x)` of the band piece is the point `bandMap c (s, x)` of the double. -/
theorem bandIncl_remodelDiffeomorph (p : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    bandIncl c (remodelDiffeomorph (endModelDiffeomorph n) _ p) = bandMap c (p.1, p.2) := by
  rw [bandIncl, Diffeomorph.symm_apply_apply, bandMap_coe]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The band piece covers the image of `(-1, 1) × ∂W` under the band map. -/
theorem range_bandIncl : range (bandIncl c (n := n)) = bandMap c '' (Ioo (-1) 1 ×ˢ univ) := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := (remodelDiffeomorph (endModelDiffeomorph n)
      (bandInterval × (𝓡∂ (n + 1)).boundary W)).surjective q
    exact ⟨(p.1, p.2), ⟨p.1.property, trivial⟩, (bandIncl_remodelDiffeomorph c p).symm⟩
  · rintro ⟨⟨s, x⟩, hs, rfl⟩
    exact ⟨remodelDiffeomorph (endModelDiffeomorph n) _ (⟨s, hs.1⟩, x),
      bandIncl_remodelDiffeomorph c _⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The band piece is an open embedding into the double. -/
theorem isOpenEmbedding_bandIncl : IsOpenEmbedding (bandIncl c (n := n)) :=
  (isOpenEmbedding_bandPt c).comp
    (remodelDiffeomorph (endModelDiffeomorph n) _).symm.toHomeomorph.isOpenEmbedding

/-- The first copy of the interior of `W` in the double. -/
def inlInterior (p : (𝓡∂ (n + 1)).interior W) : c.Double :=
  inl c p.val

/-- The second copy of the interior of `W` in the double. -/
def inrInterior (p : (𝓡∂ (n + 1)).interior W) : c.Double :=
  inr c p.val

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
@[simp]
theorem inlInterior_apply (p : (𝓡∂ (n + 1)).interior W) : inlInterior c p = inl c p.val :=
  (rfl)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
@[simp]
theorem inrInterior_apply (p : (𝓡∂ (n + 1)).interior W) : inrInterior c p = inr c p.val :=
  (rfl)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The first copy of the interior of `W` is the image of the interior under `inl`. -/
theorem range_inlInterior : range (inlInterior c) = inl c '' (𝓡∂ (n + 1)).interior W := by
  rw [image_eq_range]
  exact congrArg range (funext (inlInterior_apply c))

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The second copy of the interior of `W` is the image of the interior under `inr`. -/
theorem range_inrInterior : range (inrInterior c) = inr c '' (𝓡∂ (n + 1)).interior W := by
  rw [image_eq_range]
  exact congrArg range (funext (inrInterior_apply c))

/-- The first copy of the interior of `W` is an open embedding into the double. -/
theorem isOpenEmbedding_inlInterior : IsOpenEmbedding (inlInterior c) :=
  (DoubleAlong.isOpenEmbedding_inl_compl _ ((𝓡∂ (n + 1)).isClosed_boundary
    (n := ∞) (by simp))).comp
    (Homeomorph.setCongr (𝓡∂ (n + 1)).compl_boundary.symm).isOpenEmbedding

/-- The second copy of the interior of `W` is an open embedding into the double. -/
theorem isOpenEmbedding_inrInterior : IsOpenEmbedding (inrInterior c) :=
  (DoubleAlong.isOpenEmbedding_inr_compl _ ((𝓡∂ (n + 1)).isClosed_boundary
    (n := ∞) (by simp))).comp
    (Homeomorph.setCongr (𝓡∂ (n + 1)).compl_boundary.symm).isOpenEmbedding

/-! ### The smooth structure -/

/-- The three pieces of the double: the two copies of the interior of `W`, and the band. -/
inductive Piece
  | inl | inr | band

instance : Nonempty Piece := ⟨.inl⟩

variable (n W) in
/-- The manifold of a piece. -/
@[expose]
def piece : Piece → Type u
  | .inl | .inr => (𝓡∂ (n + 1)).interior W
  | .band => BandPiece n W

/-- The topology of a piece. -/
instance instTopologicalSpacePiece : ∀ j, TopologicalSpace (piece n W j)
  | .inl | .inr => inferInstanceAs (TopologicalSpace ((𝓡∂ (n + 1)).interior W))
  | .band => inferInstanceAs (TopologicalSpace (BandPiece n W))

/-- The charts of a piece, on `ℝⁿ⁺¹`. -/
instance instChartedSpacePiece :
    ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (piece n W j)
  | .inl | .inr => inferInstanceAs (ChartedSpace _ ((𝓡∂ (n + 1)).interior W))
  | .band => inferInstanceAs (ChartedSpace _ (BandPiece n W))

/-- Each piece is a smooth manifold. -/
instance instIsManifoldPiece : ∀ j, IsManifold (𝓡 (n + 1)) ∞ (piece n W j)
  | .inl | .inr => inferInstanceAs (IsManifold _ ∞ ((𝓡∂ (n + 1)).interior W))
  | .band => inferInstanceAs (IsManifold _ ∞ (BandPiece n W))

/-- The map of a piece into the double. -/
@[expose]
def pieceMap : ∀ j, piece n W j → c.Double
  | .inl => inlInterior c
  | .inr => inrInterior c
  | .band => bandIncl c

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
@[simp] theorem pieceMap_inl : pieceMap c .inl = inlInterior c := (rfl)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
@[simp] theorem pieceMap_inr : pieceMap c .inr = inrInterior c := (rfl)

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
@[simp] theorem pieceMap_band : pieceMap c .band = bandIncl c := (rfl)

private theorem isOpenEmbedding_pieceMap : ∀ j, IsOpenEmbedding (pieceMap c j)
  | .inl => isOpenEmbedding_inlInterior c
  | .inr => isOpenEmbedding_inrInterior c
  | .band => isOpenEmbedding_bandIncl c

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
private theorem exists_pieceMap_eq (z : c.Double) : ∃ j y, pieceMap c j y = z := by
  have h0 : (0 : ℝ) ∈ bandInterval := by simp
  rcases exists_inl_or_inr c z with ⟨w, rfl⟩ | ⟨w, rfl⟩ <;>
    by_cases hw : w ∈ (𝓡∂ (n + 1)).interior W
  · exact ⟨.inl, ⟨w, hw⟩, rfl⟩
  · rw [← ModelWithCorners.compl_boundary, Set.notMem_compl_iff] at hw
    exact ⟨.band, remodelDiffeomorph (endModelDiffeomorph n)
      (bandInterval × (𝓡∂ (n + 1)).boundary W) (⟨0, h0⟩, ⟨w, hw⟩),
      (bandIncl_remodelDiffeomorph c _).trans (bandMap_zero c ⟨w, hw⟩)⟩
  · exact ⟨.inr, ⟨w, hw⟩, rfl⟩
  · rw [← ModelWithCorners.compl_boundary, Set.notMem_compl_iff] at hw
    exact ⟨.band, remodelDiffeomorph (endModelDiffeomorph n)
      (bandInterval × (𝓡∂ (n + 1)).boundary W) (⟨0, h0⟩, ⟨w, hw⟩),
      ((bandIncl_remodelDiffeomorph c _).trans (bandMap_zero c ⟨w, hw⟩)).trans
        (inl_coe_eq_inr c ⟨w, hw⟩)⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The three pieces cover the double. -/
theorem iUnion_range_pieceMap : ⋃ j, range (pieceMap c (n := n) (W := W) j) = univ :=
  eq_univ_of_forall fun z ↦ mem_iUnion.2 <| (exists_pieceMap_eq c z).imp fun _ ↦ id

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

private theorem inl_eq_bandPt_iff (p : (𝓡∂ (n + 1)).interior W)
    (q : bandInterval × (𝓡∂ (n + 1)).boundary W) :
    inl c p.val = bandPt c q ↔ WithEnd.inclusion c p.val = WithEnd.endMap c (q.1, q.2) := by
  obtain ⟨s, x⟩ := q
  rcases le_total (s : ℝ) 0 with hs | hs
  · rw [bandPt_of_nonpos c hs, endMap_of_nonpos c hs]
    exact ⟨fun h ↦ congrArg _ (inl_injective c h),
      fun h ↦ congrArg _ (WithEnd.inclusion_injective c h)⟩
  · rw [bandPt_of_nonneg c hs]
    refine iff_of_false
      (fun h ↦ disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property
        ((inl_eq_inr_iff c).1 h).2) fun h ↦ ?_
    exact disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property
      ((WithEnd.eq_of_inclusion_eq_endMap c hs h).symm ▸ x.property)

private theorem inr_eq_bandPt_iff (p : (𝓡∂ (n + 1)).interior W)
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
      exact (disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property) (h₁ ▸ h₂)
    · exact (disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property)
        ((WithEnd.eq_of_inclusion_eq_endMap c (neg_nonneg.2 hs) h).symm ▸ x.property)

/-- The interior of `W`, in `c.WithEnd`. -/
private def interiorEnd (p : (𝓡∂ (n + 1)).interior W) : c.WithEnd := WithEnd.inclusion c p.val

private theorem isLocalDiffeomorph_interiorEnd :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (interiorEnd c) := fun p ↦
  ((𝓡∂ (n + 1)).isLocalDiffeomorph_subtypeVal_interior p).comp
    (hg := WithEnd.isLocalDiffeomorphAt_inclusion c p.property)

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
    (hg := (isLocalDiffeomorph_neg _).prodMap (isLocalDiffeomorph_id _))).comp
    (hg := WithEnd.isLocalDiffeomorphOn_endMap c
      ⟨Prod.map Neg.neg id (bandCoord q), neg_lt_neg (bandCoord_mem q).1.2, trivial⟩)

private theorem exists_transition : ∀ (j k : Piece) (x : piece n W j) (y : piece n W k),
    pieceMap c j x = pieceMap c k y → ∃ T : piece n W j → piece n W k,
      ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ T x ∧ pieceMap c k ∘ T =ᶠ[𝓝 x] pieceMap c j
  | .inl, .inl, _, _, _ | .inr, .inr, _, _, _ | .band, .band, _, _, _ =>
    ⟨id, contMDiffAt_id, .rfl⟩
  | .inl, .inr, x, _, h =>
    absurd ((inl_eq_inr_iff c).1 h).2
      (disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary x.property)
  | .inr, .inl, _, y, h =>
    absurd ((inl_eq_inr_iff c).1 h.symm).2
      (disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary y.property)
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

/-- Each piece is a smooth local diffeomorphism into the double. -/
theorem isLocalDiffeomorph_pieceMap (j : Piece) :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (pieceMap c j) :=
  isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding _ _ (exists_transition c) j

/-- The band piece is a smooth local diffeomorphism into the double. -/
theorem isLocalDiffeomorph_bandIncl :
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (bandIncl c (n := n)) :=
  isLocalDiffeomorph_pieceMap c .band

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
    exact isLocalDiffeomorph_bandIncl c q
  have hq : bandCoord q = (s, x) := by
    simp only [q, bandCoord, comp_apply, Diffeomorph.symm_apply_apply, Prod.map_apply, id_eq]
  have := h.of_comp_right (isLocalDiffeomorph_bandCoord q)
  rwa [hq] at this

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The two copies of the interior of `W` and the band cover the double. -/
theorem range_inlInterior_union_range_inrInterior_union :
    range (inlInterior c) ∪ range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨j, y, rfl⟩ := exists_pieceMap_eq c z
  cases j with
  | inl => exact Or.inl (Or.inl (mem_range_self y))
  | inr => exact Or.inl (Or.inr (mem_range_self y))
  | band => exact Or.inr ⟨bandCoord y, bandCoord_mem y, bandMap_bandCoord c y⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The two copies of the interior of `W` are disjoint in the double. -/
theorem disjoint_range_inlInterior_inrInterior :
    Disjoint (range (inlInterior c)) (range (inrInterior c)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨p, rfl⟩ ⟨q, h⟩
  rw [inlInterior_apply, inrInterior_apply] at h
  exact disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property
    ((inl_eq_inr_iff c).1 h.symm).2

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- A point `(s, x)` of the band lies on the first copy of the interior of `W` exactly when
`s < 0`. -/
theorem bandMap_mem_range_inlInterior_iff {s : ℝ} (hs : s ∈ Ioo (-1) 1)
    (x : (𝓡∂ (n + 1)).boundary W) : bandMap c (s, x) ∈ range (inlInterior c) ↔ s < 0 := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra h
    rw [bandMap_of_nonneg c (not_lt.1 h) hs.2, inlInterior_apply] at hq
    exact disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary q.property
      ((inl_eq_inr_iff c).1 hq).2
  · intro h
    rw [bandMap_of_nonpos c h.le hs.1]
    refine ⟨⟨_, ?_⟩, by rw [inlInterior_apply]⟩
    rw [c.apply_mem_interior_iff_pos, normalIioRay_coe_apply_of_nonneg _ (by linarith)]
    linarith

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- A point `(s, x)` of the band lies on the second copy of the interior of `W` exactly when
`0 < s`. -/
theorem bandMap_mem_range_inrInterior_iff {s : ℝ} (hs : s ∈ Ioo (-1) 1)
    (x : (𝓡∂ (n + 1)).boundary W) : bandMap c (s, x) ∈ range (inrInterior c) ↔ 0 < s := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra h
    rw [bandMap_of_nonpos c (not_lt.1 h) hs.1, inrInterior_apply] at hq
    obtain ⟨h₁, h₂⟩ := (inl_eq_inr_iff c).1 hq.symm
    exact disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary q.property (h₁ ▸ h₂)
  · intro h
    rw [bandMap_of_nonneg c h.le hs.2]
    refine ⟨⟨_, ?_⟩, by rw [inrInterior_apply]⟩
    rw [c.apply_mem_interior_iff_pos, normalIioRay_coe_apply_of_nonneg _ h.le]
    exact h

/-- The two copies of the interior of `W` are dense in the double: the rest is the middle
`bandMap c '' ({0} ×ˢ univ)` of the band, a limit of points `(s, x)` with `s < 0`. -/
theorem dense_range_inlInterior_union_range_inrInterior :
    Dense (range (inlInterior c) ∪ range (inrInterior c)) := by
  intro z
  rcases (range_inlInterior_union_range_inrInterior_union c ▸ mem_univ z :
    z ∈ range (inlInterior c) ∪ range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ))
    with hz | ⟨⟨s, x⟩, ⟨hs, -⟩, rfl⟩
  · exact subset_closure hz
  rcases lt_trichotomy s 0 with h | rfl | h
  · exact subset_closure (Or.inl ((bandMap_mem_range_inlInterior_iff c hs x).2 h))
  · have hg : ContinuousAt (fun t : ℝ ↦ bandMap c (t, x)) 0 := by
      have hU : Ioo (-1) 1 ×ˢ univ ∈ 𝓝 ((0 : ℝ), x) :=
        (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩
      exact (((isLocalDiffeomorphOn_bandMap c).contMDiffOn.continuousOn).continuousAt hU).comp
        (f := fun t : ℝ ↦ (t, x)) (continuous_id.prodMk continuous_const).continuousAt
    -- The points `(t, x)` with `-1 < t < 0` lie on the first copy.
    have hmem : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        bandMap c (t, x) ∈ range (inlInterior c) ∪ range (inrInterior c) := by
      filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with t ht
      exact Or.inl ((bandMap_mem_range_inlInterior_iff c ⟨ht.1, ht.2.trans one_pos⟩ x).2 ht.2)
    exact mem_closure_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds) hmem
  · exact subset_closure (Or.inr ((bandMap_mem_range_inrInterior_iff c hs x).2 h))

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
  have himage : bandMap c '' (Ioo (-1) 1 ×ˢ univ) = range (pieceMap c .band) :=
    (range_bandIncl c).symm
  have hcomp (q : BandPiece n W) : bandProj c (bandIncl c q) = (bandCoord q).2 := by
    rw [← bandMap_bandCoord, bandProj_bandMap c (bandCoord_mem q).1]
  have : Nonempty (piece n W .band) :=
    ⟨remodelDiffeomorph (endModelDiffeomorph n) (bandInterval × (𝓡∂ (n + 1)).boundary W)
      (⟨0, by simp⟩, Classical.arbitrary _)⟩
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
