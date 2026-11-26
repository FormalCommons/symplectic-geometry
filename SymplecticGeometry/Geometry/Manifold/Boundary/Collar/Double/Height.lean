/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Manifold.RegularValue
public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Basic
import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Topology
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# The height function of the double

For a manifold `W` modelled on the half-space with a smooth collar `c`, the double `c.Double`
carries a smooth function `Double.height c : c.Double → ℝ` that splits it into its two copies of
`W`. On the band, at the point `(s, x)` of `(-1, 1) × ∂W`, it is `smoothSign s`, for the smooth
odd function `smoothSign : ℝ → ℝ` with `smoothSign s = s` for `|s| ≤ 1/4`, `smoothSign s = ±1`
for `±s ≥ 1/2`, and of the sign of `s`. Off the band it is `-1` on the first copy of `W` and `1`
on the second. So `{height ≤ 0}` is the first copy of `W`, `{height < 0}` the first copy of its
interior and `{height = 0}` the common boundary, and `0` is a regular value.

## Main definitions

* `TauCeti.SmoothCollar.Double.height`: the height function of the double.
* `TauCeti.SmoothCollar.Double.homeomorphSublevel`: `W` is homeomorphic to `{height ≤ 0}`, by the
  first copy `Double.inl`.

## Main results

* `TauCeti.SmoothCollar.Double.contMDiff_height`: `height` is smooth, when `∂W` is compact and `W`
  is Hausdorff.
* `TauCeti.SmoothCollar.Double.isRegularValue_height_zero`: `0` is a regular value of `height`.
* `TauCeti.SmoothCollar.Double.preimage_height_Iic`, `preimage_height_Iio`,
  `preimage_height_zero`: the sublevel set, the strict sublevel set and the level set of `0`.
* `TauCeti.SmoothCollar.Double.image_interior_homeomorphSublevel`: `homeomorphSublevel` maps the
  interior of `W` onto `{height < 0}`.
* `TauCeti.SmoothCollar.Double.preimage_height_Iic_subset_range_inlInterior_union_bandMap_image`,
  `preimage_height_Ici_subset_range_inrInterior_union_bandMap_image`: `{height ≤ 0}` and
  `{height ≥ 0}` lie in the open sets made of a copy of the interior of `W` and the band, which
  cover the double and meet in the band.

## Implementation notes

Smoothness needs `∂W` compact: the part of the band where `|s| ≤ 1/2` is then compact, hence
closed in the Hausdorff double, and off it `height` is locally constant on each copy of the
interior. Without compactness the collar points of depth `1/2` may accumulate at a point of `W`
outside the collar.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
-/

public section

open Set Function Topology Manifold SymplecticGeometry
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothCollar.Double
open _root_.TauCeti.EuclideanHalfSpace

/-! ### The height function -/

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  (c : SmoothCollar n ∞ W)

open scoped Classical in
/-- The height function of the double `c.Double`: at the point `(s, x)` of the band
`(-1, 1) × ∂W` it is a smooth odd function of `s`, equal to `s` for `|s| ≤ 1/4`, to `-1` for
`s ≤ -1/2` and to `1` for `s ≥ 1/2`, and of the sign of `s`; off the band it is `-1` on the first
copy of `W` and `1` on the second. -/
def height (z : c.Double) : ℝ :=
  if h : z ∈ bandMap c '' (Ioo (-1) 1 ×ˢ univ) then smoothSign h.choose.1
  else if z ∈ range (inl c) then -1 else 1

/-- The height of the point `(s, x)` of the band is `smoothSign s`. -/
theorem height_bandMap {s : ℝ} (hs : s ∈ Ioo (-1) 1) (x : (𝓡∂ (n + 1)).boundary W) :
    height c (bandMap c (s, x)) = smoothSign s := by
  have h : bandMap c (s, x) ∈ bandMap c '' (Ioo (-1) 1 ×ˢ univ) :=
    mem_image_of_mem _ ⟨hs, mem_univ _⟩
  rw [height, dite_eq_left h, injOn_bandMap c h.choose_spec.1 ⟨hs, mem_univ _⟩ h.choose_spec.2]

/-- Near `0`, the height of the point `(s, x)` of the band is `s`. -/
theorem height_bandMap_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 4) (x : (𝓡∂ (n + 1)).boundary W) :
    height c (bandMap c (s, x)) = s := by
  have := abs_le.1 hs
  rw [height_bandMap c ⟨by linarith, by linarith⟩, smoothSign_of_abs_le hs]

/-- On the band, the height is an odd function of the band coordinate. -/
theorem height_bandMap_neg {s : ℝ} (hs : s ∈ Ioo (-1) 1) (x : (𝓡∂ (n + 1)).boundary W) :
    height c (bandMap c (-s, x)) = -height c (bandMap c (s, x)) := by
  rw [height_bandMap c hs, height_bandMap c ⟨by linarith [hs.2], by linarith [hs.1]⟩,
    smoothSign_neg]

/-- The height of the point `(s, x)` of the band is `1` for `s ∈ [1/2, 1)`. -/
theorem height_bandMap_of_le {s : ℝ} (hs : 1 / 2 ≤ s) (hs' : s < 1)
    (x : (𝓡∂ (n + 1)).boundary W) : height c (bandMap c (s, x)) = 1 := by
  rw [height_bandMap c ⟨by linarith, hs'⟩, smoothSign_of_le hs]

/-- The height of the point `(s, x)` of the band is `-1` for `s ∈ (-1, -1/2]`. -/
theorem height_bandMap_of_le_neg {s : ℝ} (hs : s ≤ -(1 / 2)) (hs' : -1 < s)
    (x : (𝓡∂ (n + 1)).boundary W) : height c (bandMap c (s, x)) = -1 := by
  rw [height_bandMap c ⟨hs', by linarith⟩, smoothSign_of_le_neg hs]

/-- On the band, the height is negative exactly where the band coordinate is. -/
theorem height_bandMap_lt_zero_iff {s : ℝ} (hs : s ∈ Ioo (-1) 1)
    (x : (𝓡∂ (n + 1)).boundary W) : height c (bandMap c (s, x)) < 0 ↔ s < 0 := by
  rw [height_bandMap c hs, smoothSign_lt_zero_iff]

/-- On the band, the height vanishes exactly where the band coordinate does. -/
theorem height_bandMap_eq_zero_iff {s : ℝ} (hs : s ∈ Ioo (-1) 1)
    (x : (𝓡∂ (n + 1)).boundary W) : height c (bandMap c (s, x)) = 0 ↔ s = 0 := by
  rw [height_bandMap c hs, smoothSign_eq_zero_iff]

private theorem neg_depth_mem_Ioo (t : normalIioOpens 1) :
    -(t : EuclideanHalfSpace 1).val 0 ∈ Ioo (-1) 1 := by
  have h0 := (t : EuclideanHalfSpace 1).property
  have h1 := mem_normalIioOpens.1 t.property
  constructor <;> linarith

private theorem depth_mem_Ioo (t : normalIioOpens 1) :
    (t : EuclideanHalfSpace 1).val 0 ∈ Ioo (-1) 1 := by
  have h0 := (t : EuclideanHalfSpace 1).property
  have h1 := mem_normalIioOpens.1 t.property
  constructor <;> linarith

private theorem depth_eq_zero_iff (t : normalIioOpens 1) :
    (t : EuclideanHalfSpace 1).val 0 = 0 ↔ t = normalIioOpensZero one_pos := by
  rw [← Subtype.coe_inj, coe_normalIioOpensZero, EuclideanHalfSpace.eq_zero_iff]

/-- A point of the first copy of `W` lies on the band exactly when it lies in the collar. -/
private theorem inl_mem_band_iff {w : W} :
    inl c w ∈ bandMap c '' (Ioo (-1) 1 ×ˢ univ) ↔ w ∈ range c := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨s, x⟩, ⟨hs, -⟩, h⟩
    rcases le_total s 0 with h0 | h0
    · rw [bandMap_of_nonpos c h0 hs.1, inl_eq_inl_iff] at h
      exact ⟨_, h⟩
    · rw [bandMap_of_nonneg c h0 hs.2, eq_comm, inl_eq_inr_iff] at h
      exact ⟨_, h.1.symm⟩
  · rintro ⟨⟨x, t⟩, rfl⟩
    rw [inl_apply_eq_bandMap]
    exact mem_image_of_mem _ ⟨neg_depth_mem_Ioo t, mem_univ _⟩

/-- A point of the second copy of `W` lies on the band exactly when it lies in the collar. -/
private theorem inr_mem_band_iff {w : W} :
    inr c w ∈ bandMap c '' (Ioo (-1) 1 ×ˢ univ) ↔ w ∈ range c := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨s, x⟩, ⟨hs, -⟩, h⟩
    rcases le_total s 0 with h0 | h0
    · rw [bandMap_of_nonpos c h0 hs.1, inl_eq_inr_iff] at h
      exact ⟨_, h.1⟩
    · rw [bandMap_of_nonneg c h0 hs.2, inr_eq_inr_iff] at h
      exact ⟨_, h⟩
  · rintro ⟨⟨x, t⟩, rfl⟩
    rw [inr_apply_eq_bandMap]
    exact mem_image_of_mem _ ⟨depth_mem_Ioo t, mem_univ _⟩

/-- Away from the collar, the height of the first copy of `W` is `-1`. -/
theorem height_inl_of_notMem_range {w : W} (hw : w ∉ range c) : height c (inl c w) = -1 := by
  rw [height, dite_eq_right ((inl_mem_band_iff c).not.2 hw), ite_eq_left (mem_range_self w)]

/-- Away from the collar, the height of the second copy of `W` is `1`. -/
theorem height_inr_of_notMem_range {w : W} (hw : w ∉ range c) : height c (inr c w) = 1 := by
  have hl : inr c w ∉ range (inl c) := by
    rintro ⟨v, hv⟩
    obtain ⟨rfl, hb⟩ := (inl_eq_inr_iff c).1 hv
    exact hw (c.boundary_subset_range hb)
  rw [height, dite_eq_right ((inr_mem_band_iff c).not.2 hw), ite_eq_right hl]

/-- The height is nonpositive on the first copy of `W`, and vanishes there exactly on `∂W`. -/
private theorem height_inl_nonpos_and_eq_zero_iff (w : W) :
    height c (inl c w) ≤ 0 ∧ (height c (inl c w) = 0 ↔ w ∈ (𝓡∂ (n + 1)).boundary W) := by
  by_cases hw : w ∈ range c
  · obtain ⟨⟨x, t⟩, rfl⟩ := hw
    rw [inl_apply_eq_bandMap, height_bandMap c (neg_depth_mem_Ioo t), smoothSign_nonpos_iff,
      smoothSign_eq_zero_iff, neg_eq_zero, depth_eq_zero_iff, c.apply_mem_boundary_iff]
    exact ⟨neg_nonpos.2 (t : EuclideanHalfSpace 1).property, Iff.rfl⟩
  · rw [height_inl_of_notMem_range c hw]
    exact ⟨by norm_num, by norm_num; exact fun h ↦ hw (c.boundary_subset_range h)⟩

/-- The height is nonnegative on the second copy of `W`, and vanishes there exactly on `∂W`. -/
private theorem height_inr_nonneg_and_eq_zero_iff (w : W) :
    0 ≤ height c (inr c w) ∧ (height c (inr c w) = 0 ↔ w ∈ (𝓡∂ (n + 1)).boundary W) := by
  by_cases hw : w ∈ range c
  · obtain ⟨⟨x, t⟩, rfl⟩ := hw
    rw [inr_apply_eq_bandMap, height_bandMap c (depth_mem_Ioo t), smoothSign_eq_zero_iff,
      depth_eq_zero_iff, c.apply_mem_boundary_iff]
    refine ⟨?_, Iff.rfl⟩
    rw [smoothSign_nonneg_iff]
    exact (t : EuclideanHalfSpace 1).property
  · rw [height_inr_of_notMem_range c hw]
    exact ⟨by norm_num, by norm_num; exact fun h ↦ hw (c.boundary_subset_range h)⟩

/-- The height is nonpositive on the first copy of `W`. -/
theorem height_inl_nonpos (w : W) : height c (inl c w) ≤ 0 :=
  (height_inl_nonpos_and_eq_zero_iff c w).1

/-- The height vanishes on the first copy of `W` exactly on `∂W`. -/
theorem height_inl_eq_zero_iff {w : W} :
    height c (inl c w) = 0 ↔ w ∈ (𝓡∂ (n + 1)).boundary W :=
  (height_inl_nonpos_and_eq_zero_iff c w).2

/-- The height is nonnegative on the second copy of `W`. -/
theorem height_inr_nonneg (w : W) : 0 ≤ height c (inr c w) :=
  (height_inr_nonneg_and_eq_zero_iff c w).1

/-- The height vanishes on the second copy of `W` exactly on `∂W`. -/
theorem height_inr_eq_zero_iff {w : W} :
    height c (inr c w) = 0 ↔ w ∈ (𝓡∂ (n + 1)).boundary W :=
  (height_inr_nonneg_and_eq_zero_iff c w).2

/-- The sublevel set `{height ≤ 0}` is the first copy of `W`. -/
theorem preimage_height_Iic : height c ⁻¹' Iic 0 = range (inl c) := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · rcases exists_inl_or_inr c z with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact mem_range_self w
    · have hw := (height_inr_eq_zero_iff c).1 (le_antisymm hz (height_inr_nonneg c w))
      exact ⟨w, (inl_eq_inr_iff c).2 ⟨rfl, hw⟩⟩
  · rintro ⟨w, rfl⟩
    exact height_inl_nonpos c w

/-- The level set `{height = 0}` is the slice `{0} × ∂W` of the band. -/
theorem preimage_height_zero : height c ⁻¹' {0} = bandMap c '' ({0} ×ˢ univ) := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · have hz : height c z = 0 := hz
    rcases exists_inl_or_inr c z with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have hw := (height_inl_eq_zero_iff c).1 hz
      exact ⟨(0, ⟨w, hw⟩), ⟨rfl, mem_univ _⟩, bandMap_zero c _⟩
    · have hw := (height_inr_eq_zero_iff c).1 hz
      exact ⟨(0, ⟨w, hw⟩), ⟨rfl, mem_univ _⟩, (bandMap_zero c _).trans
        ((inl_eq_inr_iff c).2 ⟨rfl, hw⟩)⟩
  · rintro ⟨⟨s, x⟩, ⟨rfl, -⟩, rfl⟩
    exact (height_bandMap_eq_zero_iff c (by norm_num) x).2 rfl

/-- The manifold `W` is homeomorphic to the sublevel set `{height ≤ 0}` of the double, by its
first copy `inl`. -/
def homeomorphSublevel : W ≃ₜ height c ⁻¹' Iic 0 :=
  (isEmbedding_inl c).toHomeomorph.trans (Homeomorph.setCongr (preimage_height_Iic c).symm)

/-- The homeomorphism of `W` with `{height ≤ 0}` is the first copy `inl`. -/
@[simp]
theorem coe_homeomorphSublevel (w : W) : (homeomorphSublevel c w : c.Double) = inl c w :=
  (rfl)

variable [IsManifold (𝓡∂ (n + 1)) ∞ W]

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The strict sublevel set `{height < 0}` is the first copy of the interior of `W`. -/
theorem preimage_height_Iio : height c ⁻¹' Iio 0 = range (inlInterior c) := by
  rw [range_inlInterior, ← (𝓡∂ (n + 1)).compl_boundary]
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · have hz : height c z < 0 := hz
    rcases exists_inl_or_inr c z with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact mem_image_of_mem _ fun hw ↦ hz.ne ((height_inl_eq_zero_iff c).2 hw)
    · exact absurd hz (height_inr_nonneg c w).not_gt
  · rintro ⟨w, hw, rfl⟩
    exact (height_inl_nonpos c w).lt_of_ne fun h ↦ hw ((height_inl_eq_zero_iff c).1 h)

/-! ### The two open sets around the copies of `W` -/

/-- The first copy of the interior of `W` together with the band is open in the double. -/
theorem isOpen_range_inlInterior_union_bandMap_image :
    IsOpen (range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) :=
  (isOpenEmbedding_inlInterior c).isOpen_range.union
    (isOpen_bandMap_image c subset_rfl (isOpen_Ioo.prod isOpen_univ))

/-- The second copy of the interior of `W` together with the band is open in the double. -/
theorem isOpen_range_inrInterior_union_bandMap_image :
    IsOpen (range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) :=
  (isOpenEmbedding_inrInterior c).isOpen_range.union
    (isOpen_bandMap_image c subset_rfl (isOpen_Ioo.prod isOpen_univ))

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The two copies of the interior of `W`, each with the band, cover the double. -/
theorem range_inlInterior_union_bandMap_image_union_range_inrInterior_union_bandMap_image :
    (range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) ∪
      (range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) = univ := by
  rw [← range_inlInterior_union_range_inrInterior_union c]
  ext z
  simp only [mem_union]
  tauto

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The two copies of the interior of `W`, each with the band, meet in the band. -/
theorem range_inlInterior_union_bandMap_image_inter_range_inrInterior_union_bandMap_image :
    (range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) ∩
      (range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ)) =
      bandMap c '' (Ioo (-1) 1 ×ˢ univ) := by
  refine Subset.antisymm ?_ fun z hz ↦ ⟨Or.inr hz, Or.inr hz⟩
  rintro z ⟨hl | hl, hr | hr⟩
  · exact absurd hr ((disjoint_range_inlInterior_inrInterior c).notMem_of_mem_left hl)
  all_goals assumption

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The sublevel set `{height ≤ 0}` lies in the first copy of the interior of `W` together with
the band. -/
theorem preimage_height_Iic_subset_range_inlInterior_union_bandMap_image :
    height c ⁻¹' Iic 0 ⊆ range (inlInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ) := by
  intro z hz
  rcases (range_inlInterior_union_range_inrInterior_union c).symm ▸ mem_univ z with
    (h | ⟨p, rfl⟩) | h
  · exact Or.inl h
  · rw [inrInterior_apply] at hz
    exact absurd ((height_inr_eq_zero_iff c).1 (le_antisymm hz (height_inr_nonneg c _)))
      (disjoint_left.1 (𝓡∂ (n + 1)).disjoint_interior_boundary p.property)
  · exact Or.inr h

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The superlevel set `{height ≥ 0}` lies in the second copy of the interior of `W` together
with the band. -/
theorem preimage_height_Ici_subset_range_inrInterior_union_bandMap_image :
    height c ⁻¹' Ici 0 ⊆ range (inrInterior c) ∪ bandMap c '' (Ioo (-1) 1 ×ˢ univ) := by
  intro z hz
  rcases (range_inlInterior_union_range_inrInterior_union c).symm ▸ mem_univ z with
    (h | h) | h
  · rw [← preimage_height_Iio c] at h
    exact absurd (mem_Ici.1 hz) (not_le.2 h)
  · exact Or.inl h
  · exact Or.inr h

/-- The height is smooth at the points of the band. -/
private theorem contMDiffAt_height_bandMap {s : ℝ} (hs : s ∈ Ioo (-1) 1)
    (x : (𝓡∂ (n + 1)).boundary W) :
    ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ) ∞ (height c) (bandMap c (s, x)) := by
  have hd := isLocalDiffeomorphOn_bandMap c ⟨(s, x), ⟨hs, mem_univ _⟩⟩
  refine (hd.contMDiffAt_comp_iff le_rfl).1 ?_
  refine (contDiff_smoothSign.contMDiff.comp contMDiff_fst).contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds (⟨hs, mem_univ _⟩ :
    (s, x) ∈ Ioo (-1 : ℝ) 1 ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)))] with p hp
  exact height_bandMap c hp.1 p.2

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- Off the middle `|s| ≤ 1/2` of the band, the height is `-1` on the first copy of the interior
of `W`. -/
private theorem height_eq_neg_one {z : c.Double} (hz : z ∈ range (inlInterior c))
    (hK : z ∉ bandMap c '' (Icc (-(1 / 2)) (1 / 2) ×ˢ univ)) : height c z = -1 := by
  obtain ⟨p, rfl⟩ := hz
  rw [inlInterior_apply] at hK ⊢
  by_cases hw : p.val ∈ range c
  · obtain ⟨⟨x, t⟩, ht⟩ := hw
    rw [← ht, inl_apply_eq_bandMap] at hK ⊢
    have h0 := (t : EuclideanHalfSpace 1).property
    have hlt : -(t : EuclideanHalfSpace 1).val 0 < -(1 / 2) := by
      by_contra h
      exact hK (mem_image_of_mem _ ⟨⟨not_lt.1 h, by linarith⟩, mem_univ _⟩)
    exact height_bandMap_of_le_neg c hlt.le (neg_depth_mem_Ioo t).1 x
  · exact height_inl_of_notMem_range c hw

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- Off the middle `|s| ≤ 1/2` of the band, the height is `1` on the second copy of the interior
of `W`. -/
private theorem height_eq_one {z : c.Double} (hz : z ∈ range (inrInterior c))
    (hK : z ∉ bandMap c '' (Icc (-(1 / 2)) (1 / 2) ×ˢ univ)) : height c z = 1 := by
  obtain ⟨p, rfl⟩ := hz
  rw [inrInterior_apply] at hK ⊢
  by_cases hw : p.val ∈ range c
  · obtain ⟨⟨x, t⟩, ht⟩ := hw
    rw [← ht, inr_apply_eq_bandMap] at hK ⊢
    have h0 := (t : EuclideanHalfSpace 1).property
    have hlt : 1 / 2 < (t : EuclideanHalfSpace 1).val 0 := by
      by_contra h
      exact hK (mem_image_of_mem _ ⟨⟨by linarith, not_lt.1 h⟩, mem_univ _⟩)
    exact height_bandMap_of_le c hlt.le (depth_mem_Ioo t).2 x
  · exact height_inr_of_notMem_range c hw

/-- The height function of the double is smooth, when `W` is Hausdorff with compact boundary. -/
theorem contMDiff_height [T2Space W] [CompactSpace ((𝓡∂ (n + 1)).boundary W)] :
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ) ∞ (height c) := by
  have hKsub : Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ (univ : Set ((𝓡∂ (n + 1)).boundary W)) ⊆
      Ioo (-1) 1 ×ˢ univ :=
    prod_mono (Icc_subset_Ioo (by norm_num) (by norm_num)) subset_rfl
  have hK : IsClosed (bandMap c '' (Icc (-(1 / 2)) (1 / 2) ×ˢ univ)) :=
    ((isCompact_Icc.prod isCompact_univ).image_of_continuousOn
      ((isLocalDiffeomorphOn_bandMap c).isLocalHomeomorphOn.continuousOn.mono hKsub)).isClosed
  intro z
  by_cases hz : z ∈ bandMap c '' (Ioo (-1) 1 ×ˢ univ)
  · obtain ⟨⟨s, x⟩, ⟨hs, -⟩, rfl⟩ := hz
    exact contMDiffAt_height_bandMap c hs x
  have hzK : z ∉ bandMap c '' (Icc (-(1 / 2)) (1 / 2) ×ˢ univ) :=
    fun h ↦ hz (image_mono hKsub h)
  have hcover := range_inlInterior_union_range_inrInterior_union c
  rcases (hcover.symm ▸ mem_univ z : z ∈ _) with (hl | hr) | hb
  · refine (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(hK.isOpen_compl.inter (isOpenEmbedding_inlInterior c).isOpen_range).mem_nhds
      ⟨hzK, hl⟩] with y hy
    exact height_eq_neg_one c hy.2 hy.1
  · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(hK.isOpen_compl.inter (isOpenEmbedding_inrInterior c).isOpen_range).mem_nhds
      ⟨hzK, hr⟩] with y hy
    exact height_eq_one c hy.2 hy.1
  · exact absurd hb hz

/-- `0` is a regular value of the height function of the double. -/
theorem isRegularValue_height_zero : IsRegularValue (𝓡 (n + 1)) 𝓘(ℝ) (height c) 0 := by
  refine isRegularValue_iff.2 fun z hz ↦ isRegularPoint_iff.2 ?_
  obtain ⟨⟨s, x⟩, ⟨rfl, -⟩, rfl⟩ : z ∈ bandMap c '' ({0} ×ˢ univ) := by
    rw [← preimage_height_zero]; exact hz
  have hd := isLocalDiffeomorphOn_bandMap c ⟨(0, x), ⟨by norm_num, mem_univ _⟩⟩
  have hfst : height c ∘ bandMap c =ᶠ[𝓝 (0, x)] Prod.fst := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds
      (Icc_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 4))] with p hp
    exact height_bandMap_of_abs_le c (abs_le.2 hp) p.2
  have h := hd.mfderiv_comp (I' := 𝓘(ℝ)) (by simp) (height c)
  rw [hfst.mfderiv_eq, mfderiv_fst] at h
  refine Surjective.of_comp (g := mfderiv (𝓘(ℝ).prod (𝓡 n)) (𝓡 (n + 1)) (bandMap c) (0, x)) ?_
  rw [← ContinuousLinearMap.coe_comp, ← h]
  exact fun v ↦ ⟨(v, 0), rfl⟩

omit [IsManifold (𝓡∂ (n + 1)) ∞ W] in
/-- The homeomorphism of `W` with `{height ≤ 0}` maps the interior of `W` onto `{height < 0}`. -/
theorem image_interior_homeomorphSublevel :
    homeomorphSublevel c '' (𝓡∂ (n + 1)).interior W = Subtype.val ⁻¹' (height c ⁻¹' Iio 0) := by
  rw [preimage_height_Iio, range_inlInterior]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (coe_homeomorphSublevel c w).symm⟩
  · rintro ⟨w, hw, hz⟩
    refine ⟨w, hw, Subtype.ext ?_⟩
    rw [coe_homeomorphSublevel, hz]

end TauCeti.SmoothCollar.Double

end
