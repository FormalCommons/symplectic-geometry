/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import SymplecticGeometry.Analysis.Calculus.ContDiff.Seeley.Extension
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Families of local diffeomorphisms over the unit interval

Let `f : unitInterval × M → N` be jointly smooth, with `M` and `N` finite-dimensional and
boundaryless. If every slice `f (t, ·)` is a local diffeomorphism, then so is the map
`(t, x) ↦ (t, f (t, x))` of the cylinders `unitInterval × M → unitInterval × N`, at the ends of
the interval as well. Since `unitInterval × M` has boundary, the inverse function theorem does not
apply to it directly.

## Main results

* `Continuous.exists_Icc_prod_extChartAt`: a neighbourhood `[a, b] × U` of a point of
  `unitInterval × M`, read in the chart at a point of `M`, that a continuous `f` maps into the
  chart at the image point.
* `ContMDiff.contDiffOn_extChartAt_comp_projIcc`: a smooth `f` read in these charts is smooth on
  `[a, b] × U`.
* `IsLocalDiffeomorphAt.restrict_unitInterval`: a local diffeomorphism `(s, u) ↦ (s, g (s, u))` of
  `ℝ × E → ℝ × F` restricts to a local diffeomorphism of `unitInterval × E → unitInterval × F`.
* `ContMDiff.isLocalDiffeomorph_prodMk_unitInterval`: a jointly smooth family of local
  diffeomorphisms over `[0, 1]` gives a local diffeomorphism `(t, x) ↦ (t, f (t, x))`.

## Implementation notes

Near `(t₀, x₀)`, in the charts at `x₀` and at `f (t₀, x₀)`, the family is a map smooth on
`[a, b] × U`, for an interval `[a, b]` that is a neighbourhood of `t₀` in `[0, 1]`. Seeley's
extension (`SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod`) extends it to a map `g` smooth on
`ℝ × U`. The map `(s, u) ↦ (s, g (s, u))` has a block triangular derivative at `(t₀, u₀)`, whose
diagonal blocks are the identity and the derivative of `f (t₀, ·)` in charts, so it is invertible
(Tau Ceti's `ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq`) and the inverse function
theorem (`TauCeti.isLocalDiffeomorphAt_of_fderiv_eq`) makes the map a local diffeomorphism. It
preserves the time, so it restricts to `unitInterval × U`; composing with the charts gives the
result. This adapts the proof of Tau Ceti's `TauCeti.isLocalDiffeomorph_fst_prodMk`, which works
on boundaryless parameter manifolds, to the parameter space `[0, 1]`.
`Diffeomorph.contMDiff_symm_eval_unitInterval`, on the inverses of a family of diffeomorphisms, is
a consequence.

## References

* R. T. Seeley, *Extension of $C^\infty$ functions defined in a half space*,
  Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

public section

open Set Filter Function
open scoped Manifold ContDiff Topology

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]

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

/-- A local diffeomorphism of `ℝ × E → ℝ × F` of the form `(s, u) ↦ (s, g (s, u))`, at a point of
time in `[0, 1]`, restricts to a local diffeomorphism `(t, u) ↦ (t, g (t, u))` of
`unitInterval × E → unitInterval × F` there. -/
theorem IsLocalDiffeomorphAt.restrict_unitInterval {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {n : WithTop ℕ∞} {g : ℝ × E → F} {t : unitInterval} {u : E}
    (hg : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) n (fun q ↦ (q.1, g q)) ((t : ℝ), u)) :
    IsLocalDiffeomorphAt ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, F)) n
      (fun p : unitInterval × E ↦ (p.1, g ((p.1 : ℝ), p.2))) (t, u) := by
  obtain ⟨Φ, hΦ, -, hgΦ⟩ := hg.exists_partialDiffeomorph_eqOn isOpen_univ (mem_univ _)
  -- The inverse of `Φ` preserves the time.
  have hfst {q : ℝ × F} (hq : q ∈ Φ.target) : (Φ.symm q).1 = q.1 :=
    congrArg Prod.fst ((hgΦ (Φ.map_target hq)).trans (Φ.right_inv hq))
  have hsymm {q : ℝ × F} (hq : q ∈ Φ.target) : (q.1, (Φ.symm q).2) = Φ.symm q :=
    Prod.ext (hfst hq).symm rfl
  have hιE : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ × E) n
      (fun p : unitInterval × E ↦ ((p.1 : ℝ), p.2)) :=
    fun _ ↦ ContMDiffAt.prodMk_space (contMDiff_subtypeVal_Icc.comp contMDiff_fst).contMDiffAt
      contMDiffAt_snd
  have hιF : ContMDiff ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × F) n
      (fun p : unitInterval × F ↦ ((p.1 : ℝ), p.2)) :=
    fun _ ↦ ContMDiffAt.prodMk_space (contMDiff_subtypeVal_Icc.comp contMDiff_fst).contMDiffAt
      contMDiffAt_snd
  let Ψ : PartialDiffeomorph ((𝓡∂ 1).prod 𝓘(ℝ, E)) ((𝓡∂ 1).prod 𝓘(ℝ, F))
      (unitInterval × E) (unitInterval × F) n :=
    { toFun := fun p ↦ (p.1, g ((p.1 : ℝ), p.2))
      invFun := fun p ↦ (p.1, (Φ.symm ((p.1 : ℝ), p.2)).2)
      source := (fun p : unitInterval × E ↦ ((p.1 : ℝ), p.2)) ⁻¹' Φ.source
      target := (fun p : unitInterval × F ↦ ((p.1 : ℝ), p.2)) ⁻¹' Φ.target
      map_source' := fun p hp ↦ by
        have h := Φ.map_source hp
        rw [← hgΦ hp] at h
        exact h
      map_target' := fun p hp ↦ by
        exact (congrArg (· ∈ Φ.source) (hsymm hp)).mpr (Φ.map_target hp)
      left_inv' := fun p hp ↦ by
        have h : Φ.symm (((p.1 : ℝ), g ((p.1 : ℝ), p.2))) = ((p.1 : ℝ), p.2) := by
          have h₂ : ((p.1 : ℝ), g ((p.1 : ℝ), p.2)) = Φ ((p.1 : ℝ), p.2) := hgΦ hp
          rw [h₂]
          exact Φ.left_inv hp
        have h' := congrArg Prod.snd h
        exact Prod.ext rfl h'
      right_inv' := fun p hp ↦ by
        have h := (hgΦ (Φ.map_target hp)).trans (Φ.right_inv hp)
        have h' := (congrArg g (hsymm hp)).trans (congrArg Prod.snd h)
        exact Prod.ext rfl h'
      open_source := Φ.open_source.preimage hιE.continuous
      open_target := Φ.open_target.preimage hιF.continuous
      contMDiffOn_toFun := by
        refine contMDiff_fst.contMDiffOn.prodMk ?_
        refine ((contDiff_snd.contMDiff.contMDiffOn (s := univ)).comp Φ.contMDiffOn_toFun
          (fun _ _ ↦ mem_univ _)).comp hιE.contMDiffOn (fun _ hp ↦ hp) |>.congr fun p hp ↦ ?_
        have h := congrArg Prod.snd (hgΦ hp)
        exact h
      contMDiffOn_invFun := contMDiff_fst.contMDiffOn.prodMk <|
        ((contDiff_snd.contMDiff.contMDiffOn (s := univ)).comp Φ.contMDiffOn_invFun
          (fun _ _ ↦ mem_univ _)).comp hιF.contMDiffOn (fun _ hp ↦ hp) }
  exact TauCeti.isLocalDiffeomorphAt_of_eqOn (Φ := Ψ) hΦ fun _ _ ↦ rfl

variable [CompleteSpace E] [IsManifold I ∞ M] [IsManifold J ∞ N] [BoundarylessManifold I M]
  [BoundarylessManifold J N]

/-- Let `f : unitInterval × M → N` be jointly smooth, with `M` and `N` boundaryless. If the slice
`f (t₀, ·)` is a local diffeomorphism at `x₀`, then `(t, x) ↦ (t, f (t, x))` is a local
diffeomorphism of `unitInterval × M → unitInterval × N` at `(t₀, x₀)`, also when `t₀` is `0`
or `1`. -/
theorem ContMDiff.isLocalDiffeomorphAt_prodMk_unitInterval {f : unitInterval × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f) {t₀ : unitInterval} {x₀ : M}
    (hd : IsLocalDiffeomorphAt I J ∞ (fun x ↦ f (t₀, x)) x₀) :
    IsLocalDiffeomorphAt ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) ∞
      (fun p : unitInterval × M ↦ (p.1, f p)) (t₀, x₀) := by
  set e := extChartAt I x₀
  set e' := extChartAt J (f (t₀, x₀))
  obtain ⟨a, b, U, ha, hab, hb, hU, hu₀, hnhds, hmaps⟩ :=
    hf.continuous.exists_Icc_prod_extChartAt (I := I) (J := J) t₀ x₀
  obtain ⟨g, hg, hgf⟩ := SymplecticGeometry.exists_contDiffOn_eqOn_Icc_prod hab hU
    (hf.contDiffOn_extChartAt_comp_projIcc (Icc_subset_Icc ha hb) hmaps)
  set u₀ := e x₀
  have ht₀ : (t₀ : ℝ) ∈ Icc a b := mem_ofPred_eq ▸ mem_of_mem_nhds hnhds
  have hgf' {s : unitInterval} (hs : (s : ℝ) ∈ Icc a b) {u : E} (hu : u ∈ U) :
      g (s, u) = e' (f (s, e.symm u)) := by
    rw [hgf ⟨hs, hu⟩]
    simp only [projIcc_val, e, e']
  have hgt₀ : (fun u ↦ g (t₀, u)) =ᶠ[𝓝 u₀] writtenInExtChartAt I J x₀ (fun x ↦ f (t₀, x)) := by
    filter_upwards [hU.mem_nhds hu₀] with u hu
    rw [hgf' ht₀ hu]
    simp only [writtenInExtChartAt, comp_apply, e, e']
  have hg₀ : g ((t₀ : ℝ), u₀) = e' (f (t₀, x₀)) := by
    rw [hgf' ht₀ hu₀]
    simp only [u₀, e, extChartAt_to_inv]
  -- The partial derivative of `g` in the space variable is the derivative of `f (t₀, ·)` in
  -- charts, which is invertible.
  have hgat : ContDiffAt ℝ ∞ g ((t₀ : ℝ), u₀) :=
    hg.contDiffAt (prod_mem_nhds univ_mem (hU.mem_nhds hu₀))
  have hgd := (hgat.differentiableAt (by simp)).hasFDerivAt
  have hfd : HasFDerivAt (writtenInExtChartAt I J x₀ (fun x ↦ f (t₀, x)))
      (mfderiv I J (fun x ↦ f (t₀, x)) x₀) u₀ :=
    (((hd.mdifferentiableAt (by simp)).hasMFDerivAt).2).hasFDerivAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)
  have hpartial : fderiv ℝ g ((t₀ : ℝ), u₀) ∘L ContinuousLinearMap.inr ℝ ℝ E =
      mfderiv I J (fun x ↦ f (t₀, x)) x₀ :=
    (hgd.comp u₀ (hasFDerivAt_prodMk_right (t₀ : ℝ) u₀)).congr_of_eventuallyEq hgt₀.symm
      |>.unique hfd
  -- So `(s, u) ↦ (s, g (s, u))` has a block triangular invertible derivative at `(t₀, u₀)`.
  set T := (ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ g ((t₀ : ℝ), u₀))
  have hT : T.IsInvertible := by
    refine (ContinuousLinearMap.isInvertible_iff_of_fst_comp_eq
      (ContinuousLinearMap.ext fun _ ↦ by simp [T])).2 ?_
    have hblock : ContinuousLinearMap.snd ℝ ℝ E' ∘L T ∘L ContinuousLinearMap.inr ℝ ℝ E =
        fderiv ℝ g ((t₀ : ℝ), u₀) ∘L ContinuousLinearMap.inr ℝ ℝ E :=
      ContinuousLinearMap.ext fun _ ↦ by simp [T]
    rw [hblock, hpartial]
    exact hd.isInvertible_mfderiv (by simp)
  obtain ⟨L, hL⟩ := hT
  have hK : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E') ∞ (fun q ↦ (q.1, g q))
      ((t₀ : ℝ), u₀) :=
    TauCeti.isLocalDiffeomorphAt_of_fderiv_eq (contDiffOn_fst.prodMk hg)
      (isOpen_univ.prod hU) ⟨mem_univ _, hu₀⟩ (by simp)
      (hL.trans (hasFDerivAt_fst.prodMk hgd).fderiv.symm)
  have hint : u₀ ∈ interior e.target :=
    (ModelWithCorners.isInteriorPoint_iff (I := I)).mp BoundarylessManifold.isInteriorPoint
  have hint' : g ((t₀ : ℝ), u₀) ∈ interior e'.target :=
    hg₀ ▸ (ModelWithCorners.isInteriorPoint_iff (I := J)).mp BoundarylessManifold.isInteriorPoint
  have hE : IsLocalDiffeomorphAt ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod 𝓘(ℝ, E)) ∞ (Prod.map id e)
      (t₀, x₀) :=
    (SymplecticGeometry.isLocalDiffeomorph_id t₀).prodMap
      (TauCeti.isLocalDiffeomorphAt_extChartAt (mem_extChartAt_source x₀) hint)
  have hE' : IsLocalDiffeomorphAt ((𝓡∂ 1).prod 𝓘(ℝ, E')) ((𝓡∂ 1).prod J) ∞
      (Prod.map id e'.symm) (t₀, g ((t₀ : ℝ), u₀)) :=
    (SymplecticGeometry.isLocalDiffeomorph_id t₀).prodMap
      (TauCeti.isLocalDiffeomorphAt_extChartAt_symm hint')
  refine ((hE.comp (hg := hK.restrict_unitInterval)).comp (hg := hE')).congr_of_eventuallyEq ?_
  -- Near `(t₀, x₀)` the composite of the charts with `(s, u) ↦ (s, g (s, u))` is the map.
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnhds,
    continuous_snd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) x₀),
    continuous_snd.continuousAt.preimage_mem_nhds
      ((continuousAt_extChartAt x₀).preimage_mem_nhds (hU.mem_nhds hu₀))] with p hpab hpe hpU
  have hpU' : e p.2 ∈ U := hpU
  have hpe' : f (p.1, e.symm (e p.2)) ∈ e'.source := (hmaps p.1 hpab _ hpU').2
  rw [e.left_inv hpe] at hpe'
  simp only [comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [hgf' hpab hpU', e.left_inv hpe, Prod.map_apply, e'.left_inv hpe']
  rfl

/-- A jointly smooth family `f : unitInterval × M → N` of local diffeomorphisms of boundaryless
manifolds gives a local diffeomorphism `(t, x) ↦ (t, f (t, x))` of
`unitInterval × M → unitInterval × N`. -/
theorem ContMDiff.isLocalDiffeomorph_prodMk_unitInterval {f : unitInterval × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod I) J ∞ f)
    (hd : ∀ t, IsLocalDiffeomorph I J ∞ (fun x ↦ f (t, x))) :
    IsLocalDiffeomorph ((𝓡∂ 1).prod I) ((𝓡∂ 1).prod J) ∞
      (fun p : unitInterval × M ↦ (p.1, f p)) :=
  fun p ↦ hf.isLocalDiffeomorphAt_prodMk_unitInterval (hd p.1 p.2)
