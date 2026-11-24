/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension

/-!
# Time extension of maps

For a map `f : unitInterval × M → F` into a real normed space, `timeExtend f : ℝ × M → F`
extends `f` in the time variable by Seeley's operator from `[0, 1]`, applied at each point of
`M` separately: `timeExtend f (t, x) = seeleyIccExtend (fun s ↦ f (projIcc 0 1 _ s, x)) t`.
It agrees with `f` on `unitInterval × M`, is linear in `f`, commutes with linear maps, and
its value at a point of `M` depends only on the values of `f` at that point; in particular it
vanishes at every time at a point where `f` vanishes at every time.

The main result is that on a boundaryless manifold `M` the extension of a map smooth on
`univ ×ˢ U`, for `U` open in `M`, is smooth on `univ ×ˢ U`. It is read in a chart of `M`,
where it is `contDiffOn_seeleyIccExtend`; the time coordinate needs only `projIcc`.

## Main definitions

* `SymplecticGeometry.timeExtend`: the extension of `f : unitInterval × M → F` to `ℝ × M`.
* `SymplecticGeometry.timeExtendLinearMap`: the same extension, as an `ℝ`-linear map.

## Main results

* `SymplecticGeometry.timeExtend_apply_coe`: the extension agrees with `f` on
  `unitInterval × M`.
* `SymplecticGeometry.timeExtend_eq_zero`: the extension vanishes at a point where `f` vanishes
  at every time.
* `ContMDiffOn.timeExtend`, `ContMDiff.timeExtend`: the extension of a smooth map is smooth.
* `Continuous.exists_Icc_prod_extChartAt`: for a continuous `f : unitInterval × M → N`, a
  neighbourhood `[a, b] × U` of a point, read in the chart at a point of `M`, that `f` maps into
  the chart at the image point.
* `ContMDiff.contDiffOn_extChartAt_comp_projIcc`: a smooth `f` read in these charts, through
  `projIcc` in the time variable, is smooth on `[a, b] × U`, so that Seeley's extension applies.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {M F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- The extension of `f : unitInterval × M → F` to `ℝ × M` by Seeley's operator in the time
variable, at each point of `M` separately. -/
noncomputable def timeExtend (f : unitInterval × M → F) (p : ℝ × M) : F :=
  seeleyIccExtend (fun s ↦ f (projIcc 0 1 zero_le_one s, p.2)) p.1

theorem timeExtend_def (f : unitInterval × M → F) (p : ℝ × M) :
    timeExtend f p = seeleyIccExtend (fun s ↦ f (projIcc 0 1 zero_le_one s, p.2)) p.1 := (rfl)

@[simp]
theorem timeExtend_apply_coe (f : unitInterval × M → F) (t : unitInterval) (x : M) :
    timeExtend f (t, x) = f (t, x) := by
  rw [timeExtend_def, seeleyIccExtend_of_mem _ t.property, projIcc_val]

theorem timeExtend_add (f g : unitInterval × M → F) :
    timeExtend (f + g) = timeExtend f + timeExtend g := by
  funext p
  exact congrFun (seeleyIccExtend_add (fun s ↦ f (projIcc 0 1 zero_le_one s, p.2))
    (fun s ↦ g (projIcc 0 1 zero_le_one s, p.2))) p.1

theorem timeExtend_smul (c : ℝ) (f : unitInterval × M → F) :
    timeExtend (c • f) = c • timeExtend f := by
  funext p
  exact congrFun (seeleyIccExtend_smul c fun s ↦ f (projIcc 0 1 zero_le_one s, p.2)) p.1

variable (M F) in
/-- The time extension `timeExtend`, as an `ℝ`-linear map from maps `unitInterval × M → F` to
maps `ℝ × M → F`. -/
noncomputable def timeExtendLinearMap : (unitInterval × M → F) →ₗ[ℝ] (ℝ × M → F) where
  toFun := timeExtend
  map_add' := timeExtend_add
  map_smul' := timeExtend_smul

@[simp]
theorem coe_timeExtendLinearMap : ⇑(timeExtendLinearMap M F) = timeExtend := (rfl)

@[simp]
theorem timeExtend_zero : timeExtend (0 : unitInterval × M → F) = 0 := by
  rw [← coe_timeExtendLinearMap, map_zero]

/-- The time extension commutes with linear maps. -/
theorem _root_.LinearMap.map_timeExtend (L : F →ₗ[ℝ] G) (f : unitInterval × M → F)
    (p : ℝ × M) : L (timeExtend f p) = timeExtend (L ∘ f) p :=
  L.map_seeleyIccExtend _ p.1

/-- The time extension at a point `x` depends only on the values of `f` at `x`. -/
theorem timeExtend_congr {f g : unitInterval × M → F} {x : M} (h : ∀ s, f (s, x) = g (s, x))
    (t : ℝ) : timeExtend f (t, x) = timeExtend g (t, x) := by
  simp only [timeExtend_def, h]

/-- If `f` vanishes at `x` at every time, so does its time extension. -/
theorem timeExtend_eq_zero {f : unitInterval × M → F} {x : M} (h : ∀ s, f (s, x) = 0) (t : ℝ) :
    timeExtend f (t, x) = 0 := by
  rw [timeExtend_congr (g := 0) h, timeExtend_zero, Pi.zero_apply]

section Smooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- On a boundaryless manifold, the time extension of a map that is smooth on `univ ×ˢ U`, for
an open `U`, is smooth on `univ ×ˢ U`. -/
theorem _root_.ContMDiffOn.timeExtend [IsManifold I ∞ M] [BoundarylessManifold I M]
    {f : unitInterval × M → F} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓡∂ 1).prod I) 𝓘(ℝ, F) ∞ f (univ ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ (timeExtend f) (univ ×ˢ U) := by
  refine contMDiffOn_of_locally_contMDiffOn fun z hz ↦ ?_
  set φ := extChartAt I z.2
  -- The points of the chart's interior whose preimage lies in `U`, and their preimage.
  set V : Set E := interior φ.target ∩ φ.symm ⁻¹' U
  have hV : IsOpen V := ((continuousOn_extChartAt_symm z.2).mono interior_subset)
    |>.isOpen_inter_preimage isOpen_interior hU
  set W : Set M := φ.source ∩ φ ⁻¹' V
  have hW : IsOpen W := isOpen_extChartAt_preimage' z.2 hV
  have hzW : z.2 ∈ W := ⟨mem_extChartAt_source z.2,
    (I.isInteriorPoint_iff).1 BoundarylessManifold.isInteriorPoint,
    by simpa [φ, extChartAt_to_inv] using hz.2⟩
  -- `f` read in the chart.
  set g : ℝ × E → F := fun q ↦ f (projIcc 0 1 zero_le_one q.1, φ.symm q.2)
  have hg : ContDiffOn ℝ ∞ g (Icc 0 1 ×ˢ V) := by
    rw [← contMDiffOn_iff_contDiffOn]
    refine hf.comp (((contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp
      contDiff_fst.contMDiff.contMDiffOn fun q (hq : q ∈ Icc 0 1 ×ˢ V) ↦ hq.1).prodMk
      ((contMDiffOn_extChartAt_symm z.2).comp contDiff_snd.contMDiff.contMDiffOn
        fun q hq ↦ interior_subset (s := φ.target) hq.2.1)) fun q hq ↦ ⟨trivial, hq.2.2⟩
  have hext := (contMDiffOn_iff_contDiffOn.2 (contDiffOn_seeleyIccExtend hV hg))
  have hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ (fun p : ℝ × M ↦ (p.1, φ p.2))
      (univ ×ˢ W) :=
    contMDiffOn_fst.prodMk_space ((contMDiffOn_extChartAt (x := z.2)).comp contMDiffOn_snd
      fun p hp ↦ by simpa [φ] using hp.2.1)
  refine ⟨univ ×ˢ W, isOpen_univ.prod hW, ⟨trivial, hzW⟩, ?_⟩
  refine ((hext.comp hφ fun p hp ↦ ⟨trivial, hp.2.2⟩).mono inter_subset_right).congr ?_
  intro p hp
  simp only [timeExtend_def, Function.comp_apply, g, φ.left_inv hp.2.2.1]

/-- On a boundaryless manifold, the time extension of a smooth map is smooth. -/
theorem _root_.ContMDiff.timeExtend [IsManifold I ∞ M] [BoundarylessManifold I M]
    {f : unitInterval × M → F} (hf : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, F) ∞ f) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ (timeExtend f) := by
  rw [← contMDiffOn_univ, ← univ_prod_univ] at hf ⊢
  exact hf.timeExtend isOpen_univ

end Smooth

end SymplecticGeometry

section Charts

/-! ### Maps on `unitInterval × M` read in charts -/

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

open Filter
open scoped Topology

/-- For a continuous `f` on `unitInterval × M` and a point `(t₀, x₀)`, there are an interval
`[a, b] ⊆ [0, 1]` that is a neighbourhood of `t₀` in `[0, 1]` and an open `U` in the target of the
chart at `x₀`, containing the image of `x₀`, such that `f` maps `[a, b] × U`, read through the
chart at `x₀`, into the source of the chart at `f (t₀, x₀)`. -/
theorem Continuous.exists_Icc_prod_extChartAt [BoundarylessManifold I M]
    {f : unitInterval × M → N} (hf : Continuous f) (t₀ : unitInterval) (x₀ : M) :
    ∃ a b : ℝ, ∃ U : Set E, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ IsOpen U ∧ extChartAt I x₀ x₀ ∈ U ∧
      {s : unitInterval | (s : ℝ) ∈ Icc a b} ∈ 𝓝 t₀ ∧
      ∀ s : unitInterval, (s : ℝ) ∈ Icc a b → ∀ u ∈ U, u ∈ (extChartAt I x₀).target ∧
        f (s, (extChartAt I x₀).symm u) ∈ (extChartAt J (f (t₀, x₀))).source := by
  set e := extChartAt I x₀
  have htarget : e.target ∈ 𝓝 (e x₀) :=
    nhdsWithin_eq_nhds.2 (range_mem_nhds_isInteriorPoint
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))) ▸
      extChartAt_target_mem_nhdsWithin x₀
  have hc : ContinuousAt (fun q : unitInterval × E ↦ f (q.1, e.symm q.2)) (t₀, e x₀) :=
    hf.continuousAt.comp (continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd)
      (continuousAt_extChartAt_symm'' (mem_extChartAt_target x₀)) continuousAt_snd))
  have hS : Prod.snd ⁻¹' e.target ∩
      (fun q : unitInterval × E ↦ f (q.1, e.symm q.2)) ⁻¹' (extChartAt J (f (t₀, x₀))).source ∈
      𝓝 (t₀, e x₀) := by
    refine inter_mem ((continuous_snd.continuousAt (x := (t₀, e x₀))).preimage_mem_nhds htarget)
      (hc.preimage_mem_nhds ?_)
    simp only [e, extChartAt_to_inv]
    exact extChartAt_source_mem_nhds _
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hS
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hV
  have h₀ := t₀.property.1
  have h₁ := t₀.property.2
  refine ⟨max 0 (t₀ - δ / 2), min 1 (t₀ + δ / 2), interior W, le_max_left _ _, ?_,
    min_le_left _ _, isOpen_interior,
    mem_interior_iff_mem_nhds.2 hW, mem_of_superset (Metric.ball_mem_nhds t₀ (half_pos hδ)) ?_,
    fun s hs u hu ↦ hVW (mk_mem_prod (hδV ?_) (interior_subset hu))⟩
  · simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · intro s hs
    have h := abs_lt.1 (Real.dist_eq _ _ ▸ Subtype.dist_eq s t₀ ▸ Metric.mem_ball.1 hs)
    exact ⟨max_le s.property.1 (by linarith), le_min s.property.2 (by linarith)⟩
  · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    have := le_of_max_le_right hs.1
    have := le_min_iff.1 hs.2
    constructor <;> linarith

/-- A smooth map `f` on `unitInterval × M`, read in charts on `[a, b] × U` as in
`Continuous.exists_Icc_prod_extChartAt`, is smooth there. -/
theorem ContMDiff.contDiffOn_extChartAt_comp_projIcc [IsManifold I ∞ M] [IsManifold J ∞ N]
    {f : unitInterval × M → N} (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f) {x₀ : M} {y₀ : N}
    {a b : ℝ} {U : Set E} (hab : Icc a b ⊆ Icc 0 1)
    (hU : ∀ s : unitInterval, (s : ℝ) ∈ Icc a b → ∀ u ∈ U, u ∈ (extChartAt I x₀).target ∧
      f (s, (extChartAt I x₀).symm u) ∈ (extChartAt J y₀).source) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E ↦
      extChartAt J y₀ (f (projIcc 0 1 zero_le_one q.1, (extChartAt I x₀).symm q.2)))
      (Icc a b ×ˢ U) := by
  have hU' {q : ℝ × E} (hq : q ∈ Icc a b ×ˢ U) := hU (projIcc 0 1 zero_le_one q.1)
    (by rw [projIcc_of_mem _ (hab hq.1)]; exact hq.1) q.2 hq.2
  refine contMDiffOn_iff_contDiffOn.1 ?_
  have hP : ContMDiffOn 𝓘(ℝ, ℝ × E) ((𝓡∂ 1).prod I) ∞
      (fun q : ℝ × E ↦ (projIcc 0 1 zero_le_one q.1, (extChartAt I x₀).symm q.2))
      (Icc a b ×ˢ U) :=
    ((contMDiffOn_projIcc.mono hab).comp contDiff_fst.contMDiff.contMDiffOn
      fun q (hq : q ∈ Icc a b ×ˢ U) ↦ hq.1).prodMk ((contMDiffOn_extChartAt_symm x₀).comp
        contDiff_snd.contMDiff.contMDiffOn fun q (hq : q ∈ Icc a b ×ˢ U) ↦ (hU' hq).1)
  refine contMDiffOn_extChartAt.comp (hf.comp_contMDiffOn hP) fun q hq ↦ ?_
  rw [← extChartAt_source J]
  exact (hU' hq).2

end Charts

end
