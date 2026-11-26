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
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import TauCeti.Geometry.Manifold.TubularNeighborhood.Existence

/-!
# Time extension of maps

For a map `f : unitInterval × M → F` into a real normed space, `timeExtend f : ℝ × M → F`
extends `f` in the time variable by Seeley's operator from `[0, 1]`, applied at each point of
`M` separately: `timeExtend f (t, x) = seeleyIccExtend (fun s ↦ f (projIcc 0 1 _ s, x)) t`.
It agrees with `f` on `unitInterval × M`, is linear in `f`, commutes with linear maps, and
its value at a point of `M` depends only on the values of `f` at that point; in particular it
vanishes at every time at a point where `f` vanishes at every time.

The main result is that the extension of a map smooth on `univ ×ˢ U`, for `U` open in `M`, is
smooth on `univ ×ˢ U`, also when `M` has boundary. It is read in a chart of `M`, whose target
is the range of the model, which is convex, cut by an open set; there it is
`contDiffOn_seeleyIccExtend_of_convex`. The time coordinate needs only `projIcc`. For
`M = unitInterval × N` this extends a smooth map on `unitInterval × (unitInterval × N)` in the
first interval variable to one smooth on `ℝ × (unitInterval × N)`.

## Main definitions

* `SymplecticGeometry.timeExtend`: the extension of `f : unitInterval × M → F` to `ℝ × M`.
* `SymplecticGeometry.timeExtendLinearMap`: the same extension, as an `ℝ`-linear map.

## Main results

* `SymplecticGeometry.timeExtend_apply_coe`: the extension agrees with `f` on
  `unitInterval × M`.
* `SymplecticGeometry.timeExtend_comp_prodMap_id`: extending `f ∘ Prod.map id g` is extending
  `f` at the image under `g` of the point of space.
* `SymplecticGeometry.timeExtend_eq_zero`: the extension vanishes at a point where `f` vanishes
  at every time.
* `ContMDiffOn.timeExtend`, `ContMDiff.timeExtend`: the extension of a smooth map is smooth, on
  any manifold `M`, with or without boundary.
* `Continuous.exists_Icc_prod_extChartAt`: for a continuous `f : unitInterval × M → N`, a
  neighbourhood `[a, b] × U` of a point, read in the chart at a point of `M`, that `f` maps into
  the chart at the image point.
* `ContMDiffOn.comp_projIcc_extChartAt_symm`: a map smooth on `univ ×ˢ U`, read through
  `projIcc` in the time variable and the inverse chart of `M`, is smooth on `[a, b] × V`.
* `ContMDiff.contDiffOn_extChartAt_comp_projIcc`: a smooth `f` read in these charts, through
  `projIcc` in the time variable, is smooth on `[a, b] × U`, so that Seeley's extension applies.
* `ContMDiff.exists_contMDiffOn_extend_of_isCompact`: a smooth map on `unitInterval × P` into a
  finite-dimensional, Hausdorff boundaryless manifold `N` extends in time to a map smooth on an
  open set containing `[0, 1] ×ˢ A`, for a compact `A ⊆ P`. A neighbourhood of the compact image
  of `unitInterval ×ˢ A` embeds into a Euclidean space (Tau Ceti's
  `IsCompact.exists_opens_nonempty_smoothEmbedding_euclidean`), and the image has a smooth
  retraction on a neighbourhood (`TauCeti.SmoothEmbedding.exists_contMDiffOn_retraction`); the
  extension is the retraction applied to `timeExtend` of the composite with the embedding.

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

/-- Extending `f ∘ Prod.map id g` in time at `(t, x)` is extending `f` at `(t, g x)`. -/
theorem timeExtend_comp_prodMap_id {M' : Type*} (f : unitInterval × M' → F) (g : M → M')
    (p : ℝ × M) : timeExtend (f ∘ Prod.map id g) p = timeExtend f (p.1, g p.2) := by
  simp only [timeExtend_def, Function.comp_apply, Prod.map_apply, id_eq]

/-- If `f` vanishes at `x` at every time, so does its time extension. -/
theorem timeExtend_eq_zero {f : unitInterval × M → F} {x : M} (h : ∀ s, f (s, x) = 0) (t : ℝ) :
    timeExtend f (t, x) = 0 := by
  rw [timeExtend_congr (g := 0) h, timeExtend_zero, Pi.zero_apply]

section Smooth

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A map `f` on `unitInterval × M` that is smooth on `univ ×ˢ U`, read through `projIcc` in the
time variable and through the inverse chart of `M` at `x₀`, is smooth on `[a, b] × V`, for
`[a, b] ⊆ [0, 1]` and `V` a subset of the chart's target that the inverse chart maps into `U`. -/
theorem _root_.ContMDiffOn.comp_projIcc_extChartAt_symm {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I ∞ M]
    {f : unitInterval × M → N} {U : Set M} (hf : ContMDiffOn ((𝓡∂ 1).prod I) J ∞ f (univ ×ˢ U))
    {x₀ : M} {a b : ℝ} {V : Set E} (hab : Icc a b ⊆ Icc 0 1)
    (hV : ∀ u ∈ V, u ∈ (extChartAt I x₀).target ∧ (extChartAt I x₀).symm u ∈ U) :
    ContMDiffOn 𝓘(ℝ, ℝ × E) J ∞
      (fun q : ℝ × E ↦ f (projIcc 0 1 zero_le_one q.1, (extChartAt I x₀).symm q.2))
      (Icc a b ×ˢ V) :=
  hf.comp (((contMDiffOn_projIcc.mono hab).comp contDiff_fst.contMDiff.contMDiffOn
      fun q (hq : q ∈ Icc a b ×ˢ V) ↦ hq.1).prodMk ((contMDiffOn_extChartAt_symm x₀).comp
        contDiff_snd.contMDiff.contMDiffOn fun q (hq : q ∈ Icc a b ×ˢ V) ↦ (hV _ hq.2).1))
    fun _ hq ↦ ⟨trivial, (hV _ hq.2).2⟩

/-- The time extension of a map that is smooth on `univ ×ˢ U`, for an open `U`, is smooth on
`univ ×ˢ U`. The manifold `M` may have boundary. -/
theorem _root_.ContMDiffOn.timeExtend [IsManifold I ∞ M] {f : unitInterval × M → F} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn ((𝓡∂ 1).prod I) 𝓘(ℝ, F) ∞ f (univ ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ (timeExtend f) (univ ×ˢ U) := by
  refine contMDiffOn_of_locally_contMDiffOn fun z hz ↦ ?_
  set φ := extChartAt I z.2
  -- The chart's target is `range I ∩ T` for an open `T`, and the points of the target whose
  -- preimage lies in `U` are those of an open `O`.
  set T : Set E := I.symm ⁻¹' (chartAt H z.2).target
  have hT : IsOpen T := (chartAt H z.2).open_target.preimage I.continuous_symm
  have hφT : φ.target = range I ∩ T := by rw [extChartAt_target (I := I), inter_comm]
  obtain ⟨O, hO, hOU⟩ := continuousOn_iff'.1 (continuousOn_extChartAt_symm (I := I) z.2) U hU
  set V : Set E := range I ∩ (T ∩ O)
  have hV : ∀ u ∈ V, u ∈ φ.target ∧ φ.symm u ∈ U := fun u hu ↦ by
    have hu' : u ∈ φ.target := by rw [hφT]; exact ⟨hu.1, hu.2.1⟩
    have : u ∈ O ∩ φ.target := ⟨hu.2.2, hu'⟩
    rw [← hOU] at this
    exact ⟨hu', this.1⟩
  set W : Set M := φ.source ∩ φ ⁻¹' O
  have hW : IsOpen W := isOpen_extChartAt_preimage' z.2 hO
  have hzW : z.2 ∈ W := by
    have : φ z.2 ∈ φ.symm ⁻¹' U ∩ φ.target :=
      ⟨by simpa [φ, extChartAt_to_inv] using hz.2, mem_extChartAt_target z.2⟩
    rw [hOU] at this
    exact ⟨mem_extChartAt_source z.2, this.1⟩
  -- `f` read in the chart.
  set g : ℝ × E → F := fun q ↦ f (projIcc 0 1 zero_le_one q.1, φ.symm q.2)
  have hg : ContDiffOn ℝ ∞ g (Icc 0 1 ×ˢ V) :=
    contMDiffOn_iff_contDiffOn.1 <| hf.comp_projIcc_extChartAt_symm subset_rfl hV
  have hext := contMDiffOn_iff_contDiffOn.2
    (contDiffOn_seeleyIccExtend_of_convex I.convex_range I.uniqueDiffOn (hT.inter hO) hg)
  have hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ (fun p : ℝ × M ↦ (p.1, φ p.2))
      (univ ×ˢ W) :=
    contMDiffOn_fst.prodMk_space ((contMDiffOn_extChartAt (x := z.2)).comp contMDiffOn_snd
      fun p hp ↦ by simpa [φ] using hp.2.1)
  have hφV : ∀ p : ℝ × M, p ∈ univ ×ˢ W → (p.1, φ p.2) ∈ univ ×ˢ V := fun p hp ↦ by
    have ht : φ p.2 ∈ range I ∩ T := by rw [← hφT]; exact φ.map_source hp.2.1
    exact ⟨trivial, ht.1, ht.2, hp.2.2⟩
  refine ⟨univ ×ˢ W, isOpen_univ.prod hW, ⟨trivial, hzW⟩, ?_⟩
  refine ((hext.comp hφ hφV).mono inter_subset_right).congr ?_
  intro p hp
  simp only [timeExtend_def, Function.comp_apply, g, φ.left_inv hp.2.2.1]

/-- The time extension of a smooth map is smooth. The manifold `M` may have boundary; for
instance, for `M = unitInterval × N`, this extends a smooth map on
`unitInterval × (unitInterval × N)` to one smooth on `ℝ × (unitInterval × N)`. -/
theorem _root_.ContMDiff.timeExtend [IsManifold I ∞ M] {f : unitInterval × M → F}
    (hf : ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, F) ∞ f) :
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
  have hf' := (hf.contMDiffOn (s := univ ×ˢ univ)).comp_projIcc_extChartAt_symm (x₀ := x₀)
    (V := U ∩ (extChartAt I x₀).target) hab fun _ hu ↦ ⟨hu.2, trivial⟩
  refine contMDiffOn_iff_contDiffOn.1 (contMDiffOn_extChartAt.comp
    (hf'.mono fun q hq ↦ ⟨hq.1, hq.2, (hU' hq).1⟩) fun q hq ↦ ?_)
  rw [← extChartAt_source J]
  exact (hU' hq).2

end Charts

section Manifold

/-! ### Maps into a manifold -/

variable {E H P E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N]

/-- **Time extension of a map into a manifold, near a compact set.** A smooth map
`f : unitInterval × P → N` into a finite-dimensional, Hausdorff boundaryless manifold extends in
time near a compact `A ⊆ P`: there are an open `S ⊇ [0, 1] ×ˢ A` and a map `G : ℝ × P → N`,
smooth on `S`, with `G (t, x) = f (t, x)` whenever `t ∈ [0, 1]` and `(t, x) ∈ S`. The manifold
`P` may have boundary. -/
theorem ContMDiff.exists_contMDiffOn_extend_of_isCompact {f : unitInterval × P → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f) {A : Set P} (hA : IsCompact A) :
    ∃ S : Set (ℝ × P), IsOpen S ∧ Icc 0 1 ×ˢ A ⊆ S ∧ ∃ G : ℝ × P → N,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞ G S ∧
      ∀ t : unitInterval, ∀ x, ((t : ℝ), x) ∈ S → G (t, x) = f (t, x) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, isOpen_empty, by simp, fun p ↦ f (0, p.2), contMDiffOn_empty,
      fun _ _ h ↦ h.elim⟩
  -- A neighbourhood `W` of the compact track of `A` embeds into a Euclidean space by `e`, and
  -- `r` retracts a neighbourhood `O` of the image of `e`.
  have hT : IsCompact (f '' (univ ×ˢ A)) := (isCompact_univ.prod hA).image hf.continuous
  obtain ⟨W, hTW, -, n, ⟨e⟩⟩ := hT.exists_opens_nonempty_smoothEmbedding_euclidean (I := J)
  have : Nonempty W := ⟨⟨f (0, x₀), hTW ⟨(0, x₀), ⟨mem_univ _, hx₀⟩, rfl⟩⟩⟩
  obtain ⟨O, hO, heO, -, r, hr, hre⟩ := e.exists_contMDiffOn_retraction isOpen_univ (subset_univ _)
  -- `g` is `e` on `W`, extended by `0`.
  let g : N → EuclideanSpace ℝ (Fin n) := Function.extend Subtype.val e 0
  have hgW (y : W) : g y = e y := Subtype.val_injective.extend_apply _ _ y
  have hg : ContMDiffOn J 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g W :=
    ContMDiffMap.contMDiffOn_extend W ⟨e, e.contMDiff⟩ 0
  -- The tube lemma gives an open `U ⊇ A` whose track stays in `W`.
  obtain ⟨u, U, -, hU, hu, hAU, hUW⟩ := generalized_tube_lemma isCompact_univ hA
    (W.isOpen.preimage hf.continuous) (fun p hp ↦ hTW ⟨p, hp, rfl⟩)
  have hUW' : univ ×ˢ U ⊆ f ⁻¹' W := (prod_mono hu subset_rfl).trans hUW
  -- Seeley's extension in time of `g ∘ f`, followed by the retraction.
  let k : ℝ × P → EuclideanSpace ℝ (Fin n) := SymplecticGeometry.timeExtend fun p ↦ g (f p)
  have hk : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ k (univ ×ˢ U) :=
    (hg.comp hf.contMDiffOn hUW').timeExtend hU
  have hkf (t : unitInterval) (x : P) (hx : x ∈ U) :
      k (t, x) = e ⟨f (t, x), hUW' ⟨trivial, hx⟩⟩ :=
    (SymplecticGeometry.timeExtend_apply_coe _ t x).trans (hgW ⟨_, hUW' ⟨trivial, hx⟩⟩)
  refine ⟨univ ×ˢ U ∩ k ⁻¹' O, hk.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU) hO,
    fun p hp ↦ ⟨⟨trivial, hAU hp.2⟩, ?_⟩, fun p ↦ r (k p),
    contMDiff_subtypeVal.comp_contMDiffOn (hr.comp (hk.mono inter_subset_left) fun _ hp ↦ hp.2),
    fun t x hx ↦ by simp only [hkf t x hx.1.2, hre]⟩
  obtain ⟨t, x⟩ := p
  rw [mem_preimage, ← Subtype.coe_mk t hp.1, hkf ⟨t, hp.1⟩ x (hAU hp.2)]
  exact heO (mem_range_self _)

end Manifold

end
