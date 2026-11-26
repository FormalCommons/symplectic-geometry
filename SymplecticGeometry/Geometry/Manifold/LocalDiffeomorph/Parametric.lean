/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import SymplecticGeometry.Topology.MetricSpace.Tube
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Parametric
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Jointly smooth inverses of a family of immersions with a fixed point

Let `e : unitInterval × F → M` be a smooth family of injective maps from an open set `U` of a
finite-dimensional real normed space `F` into a manifold `M` of the same dimension, each of
which sends the point `x₀ ∈ U` to the same point `e (0, x₀)` with injective derivative there.
Then near `x₀` the maps `e (t, ·)` can be inverted against `e (0, ·)` jointly smoothly in `t`
and the point: there is a smooth `κ` defined on a neighbourhood `V` of `x₀` with
`e (t, κ (t, x)) = e (0, x)`, and `κ (t, x) = x` wherever `e (t, x) = e (0, x)`
(`SymplecticGeometry.exists_contMDiffOn_apply_eq_apply_zero`).

The proof reads `e` in the chart of `M` at `e (0, x₀)` and extends it in time to `ℝ` by
`SymplecticGeometry.timeExtend`. The graph `Φ (t, x) = (t, G (t, x))` of the extension `G` has
injective derivative along `[0, 1] × {x₀}` (Tau Ceti's
`MDifferentiableAt.injective_mfderiv_fst_prod_iff`), so it is a local diffeomorphism there
(`TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv`), and also injective and a local
diffeomorphism on an open neighbourhood `S` of that compact set
(`Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn`). Tau Ceti's parametric inverse
function theorem `ContDiffOn.parametric_invFunOn_of_injective_fderiv` inverts `G` on `S`
jointly smoothly over the open image `Φ '' S` (`Set.MapsTo.interior_of_contDiffOn`), and the
tube lemma `IsCompact.exists_prod_ball_subset` gives the neighbourhood `V`.

## Main results

* `SymplecticGeometry.exists_contMDiffOn_apply_eq_apply_zero`: the jointly smooth inverse.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22, whose transition germs of a family of ball embeddings use this inverse.
-/

public section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **A jointly smooth inverse of a family of immersions with a fixed point.** Let `M` be a
manifold modelled on a finite-dimensional `E`, `F` a real normed space of the same dimension,
`U ⊆ F` open with `x₀ ∈ U`, and `e : unitInterval × F → M` smooth on `univ ×ˢ U`, such that
each `e (t, ·)` is injective on `U`, has injective derivative at `x₀` (the derivative is
assumed injective only there), and sends `x₀` to `e (0, x₀)`. Then for every `ε > 0` there
are `0 < δ ≤ ε`, an open `V ⊆ U` containing `closedBall x₀ δ`, and `κ : unitInterval × F → F`
smooth on `univ ×ˢ V`, such that for every `t` and `x ∈ V`, `κ (t, x) ∈ U`,
`e (t, κ (t, x)) = e (0, x)`, and `κ (t, x) = x` when `e (t, x) = e (0, x)`. -/
theorem exists_contMDiffOn_apply_eq_apply_zero {e : unitInterval × F → M} {U : Set F} {x₀ : F}
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (he : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) I ∞ e (univ ×ˢ U))
    (hinj : ∀ t, InjOn (fun x ↦ e (t, x)) U)
    (hd : ∀ t, Injective (mfderiv 𝓘(ℝ, F) I (fun x ↦ e (t, x)) x₀))
    (hfix : ∀ t, e (t, x₀) = e (0, x₀)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ ∃ V : Set F, IsOpen V ∧ V ⊆ U ∧ closedBall x₀ δ ⊆ V ∧
      ∃ κ : unitInterval × F → F,
        ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ κ (univ ×ˢ V) ∧
        ∀ t, ∀ x ∈ V, κ (t, x) ∈ U ∧ e (t, κ (t, x)) = e (0, x) ∧
          (e (t, x) = e (0, x) → κ (t, x) = x) := by
  set p₀ := e (0, x₀)
  set φ := extChartAt I p₀
  -- A ball `B` about `x₀` in `U` that every `e (t, ·)` maps into the chart's source.
  obtain ⟨r, hr, hrW⟩ := isCompact_univ.exists_prod_ball_subset (y := x₀)
    (he.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU)
      (isOpen_extChartAt_source (I := I) p₀)) (by
        rintro ⟨t, x⟩ ⟨-, hx⟩
        rw [show x = x₀ from mem_singleton_iff.1 hx]
        exact ⟨⟨trivial, hx₀⟩, by simp [hfix t]⟩)
  set B := ball x₀ r
  have hBo : IsOpen B := isOpen_ball
  have hx₀B : x₀ ∈ B := mem_ball_self hr
  have hB (t : unitInterval) (x : F) (hx : x ∈ B) : x ∈ U ∧ e (t, x) ∈ φ.source :=
    ⟨(hrW (mk_mem_prod (mem_univ t) hx)).1.2, (hrW (mk_mem_prod (mem_univ t) hx)).2⟩
  -- `e` read in the chart, and its extension `G` in time.
  set f : unitInterval × F → E := fun q ↦ φ (e q)
  have hf : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, E) ∞ f (univ ×ˢ B) :=
    contMDiffOn_extChartAt.comp (he.mono fun q hq ↦ ⟨trivial, (hB q.1 q.2 hq.2).1⟩)
      fun q hq ↦ by simpa [φ] using (hB q.1 q.2 hq.2).2
  set G := timeExtend f
  have hO : IsOpen (univ ×ˢ B : Set (ℝ × F)) := isOpen_univ.prod hBo
  have hG : ContDiffOn ℝ ∞ G (univ ×ˢ B) := hf.contDiffOn_timeExtend hBo
  have hGcoe (t : unitInterval) (x : F) : G (t, x) = f (t, x) := timeExtend_apply_coe f t x
  have hGslice (t : unitInterval) : (fun x ↦ G (t, x)) = fun x ↦ φ (e (t, x)) := by
    funext x
    exact timeExtend_apply_coe f t x
  -- The graph `Φ` of `G` over the time coordinate.
  set Φ : ℝ × F → ℝ × E := fun q ↦ (q.1, G q)
  have hΦ : ContDiffOn ℝ ∞ Φ (univ ×ˢ B) := contDiffOn_fst.prodMk hG
  have hgraph {q : ℝ × F} (hq : q ∈ univ ×ˢ B) :
      Injective (mfderiv 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ × E) Φ q) ↔
        Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (fun x ↦ G (q.1, x)) q.2) := by
    have hGd : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) 𝓘(ℝ, E) G q :=
      (contMDiffAt_prod_modelWithCornersSelf_iff.2
        (hG.contDiffAt (hO.mem_nhds hq)).contMDiffAt).mdifferentiableAt (by simp)
    have := hGd.injective_mfderiv_fst_prod_iff
    rwa [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
      chartedSpaceSelf_prod] at this
  have hfin : Module.finrank ℝ (ℝ × F) = Module.finrank ℝ (ℝ × E) := by
    simp [Module.finrank_prod, hdim]
  -- `Φ` is a local diffeomorphism at each point of `[0, 1] × {x₀}`.
  have hloc : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ {x₀},
      IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × F) 𝓘(ℝ, ℝ × E) ∞ Φ q := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    rw [show x = x₀ from mem_singleton_iff.1 hx]
    refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hΦ.contMDiffOn hO
      ⟨trivial, hx₀B⟩ (BoundarylessManifold.isInteriorPoint) (by simp) ?_ hfin
    rw [hgraph ⟨trivial, hx₀B⟩]
    -- see `t` as the coercion of a point of `unitInterval`, to use `hGslice`
    change Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (fun x ↦ G ((⟨t, ht⟩ : unitInterval), x)) x₀)
    rw [hGslice]
    have hφ : MDifferentiableAt I 𝓘(ℝ, E) φ (e (⟨t, ht⟩, x₀)) :=
      mdifferentiableAt_extChartAt (by simpa [φ] using (hB ⟨t, ht⟩ x₀ hx₀B).2)
    have het : MDifferentiableAt 𝓘(ℝ, F) I (fun x ↦ e (⟨t, ht⟩, x)) x₀ :=
      ((he.contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨trivial, hx₀⟩)).comp x₀
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    rw [show (fun x ↦ φ (e (⟨t, ht⟩, x))) = φ ∘ fun x ↦ e (⟨t, ht⟩, x) from rfl,
      mfderiv_comp x₀ hφ het]
    exact (isInvertible_mfderiv_extChartAt
      (by simpa [φ] using (hB ⟨t, ht⟩ x₀ hx₀B).2)).injective.comp (hd _)
  -- An open `T ⊇ [0, 1] × {x₀}` on which `Φ` is injective and a local diffeomorphism.
  obtain ⟨T, hT, hKT, hTinj, hTloc⟩ := Set.InjOn.exists_isOpen_superset_isLocalDiffeomorphOn
    (f := Φ) (K := Icc (0 : ℝ) 1 ×ˢ {x₀}) (fun p hp q hq h ↦
      Prod.ext (by simpa [Φ] using congrArg Prod.fst h)
        ((mem_singleton_iff.1 hp.2).trans (mem_singleton_iff.1 hq.2).symm))
    (isCompact_Icc.prod isCompact_singleton) hloc
  set S := T ∩ univ ×ˢ B
  have hS : IsOpen S := hT.inter hO
  have hKS : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ S := subset_inter hKT fun q hq ↦
    ⟨trivial, (mem_singleton_iff.1 hq.2) ▸ hx₀B⟩
  -- Read the derivatives of `Φ` and of the slices of `G` on `S` as Fréchet derivatives.
  have hinjΦ {q} (hq : q ∈ S) : Injective (fderiv ℝ Φ q) := by
    have := ((hTloc ⟨q, hq.1⟩).isInvertible_mfderiv (by simp)).injective
    rw [mfderiv_eq_fderiv] at this
    simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp] using this
  have hinjG {q} (hq : q ∈ S) : Injective (fderiv ℝ (fun x ↦ G (q.1, x)) q.2) := by
    have := (hgraph hq.2).1 ((hTloc ⟨q, hq.1⟩).isInvertible_mfderiv (by simp)).injective
    rw [mfderiv_eq_fderiv] at this
    simpa only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      EquivLike.comp_injective, EquivLike.injective_comp] using this
  -- The parametric inverse, defined on the open image `Φ '' S`.
  have hκ := (hG.mono inter_subset_right).parametric_invFunOn_of_injective_fderiv hS (by simp)
    (fun p x hx y hy hxy ↦ (Prod.ext_iff.1 (hTinj hx.1 hy.1 (Prod.ext rfl hxy))).2)
    (fun q hq ↦ hinjG hq) hdim
  have hΦS : IsOpen (Φ '' S) := by
    have := (mapsTo_image Φ S).interior_of_contDiffOn (hΦ.mono inter_subset_right) (by simp)
      fun q hq ↦ (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hfin).2
        (hinjΦ (interior_subset hq))
    rw [hS.interior_eq] at this
    exact subset_interior_iff_isOpen.1 this.image_subset
  -- A ball `V` about `x₀` on which `(t, f (0, x))` stays in `Φ '' S`.
  have hf0 : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (fun x ↦ f (0, x)) B :=
    hf.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ ⟨trivial, hx⟩
  obtain ⟨ρ, hρ, hρV⟩ := isCompact_Icc.exists_prod_ball_subset (y := x₀)
    ((continuousOn_fst.prodMk (hf0.continuousOn.comp continuousOn_snd
      fun q (hq : q ∈ univ ×ˢ B) ↦ hq.2)).isOpen_inter_preimage hO hΦS) (by
        rintro ⟨t, x⟩ ⟨ht, hx⟩
        rw [show x = x₀ from mem_singleton_iff.1 hx]
        refine ⟨⟨trivial, hx₀B⟩, (t, x₀), hKS ⟨ht, rfl⟩, Prod.ext rfl ?_⟩
        -- see `t` as the coercion of a point of `unitInterval`, to use `hGcoe`
        change G ((⟨t, ht⟩ : unitInterval), x₀) = f (0, x₀)
        rw [hGcoe]
        exact congrArg φ (hfix _))
  set V := ball x₀ ρ
  have hVB : V ⊆ B := fun x hx ↦ (hρV (mk_mem_prod (left_mem_Icc.2 zero_le_one) hx)).1.2
  have hVmem {t : unitInterval} {x : F} (hx : x ∈ V) : ((t : ℝ), f (0, x)) ∈ Φ '' S :=
    (hρV (mk_mem_prod t.property hx)).2
  set Ψ := fun q : ℝ × E ↦ invFunOn (fun x ↦ G (q.1, x)) (Prod.mk q.1 ⁻¹' S) q.2
  refine ⟨min ε (ρ / 2), lt_min hε (half_pos hρ), min_le_left _ _, V, isOpen_ball,
    fun x hx ↦ (hB 0 x (hVB hx)).1,
    closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hρ)),
    fun q ↦ Ψ ((q.1 : ℝ), f (0, q.2)), ?_, fun t x hx ↦ ?_⟩
  · have hΨ : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) ∞ Ψ (Φ '' S) := hκ.contMDiffOn
    have hin : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ × E) ∞
        (fun q : unitInterval × F ↦ ((q.1 : ℝ), f (0, q.2))) (univ ×ˢ V) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)).comp
        contMDiff_fst).contMDiffOn.prodMk
        ((hf0.mono hVB).comp contMDiffOn_snd fun q (hq : q ∈ univ ×ˢ V) ↦ hq.2)
    exact hΨ.comp hin fun q (hq : q ∈ univ ×ˢ V) ↦ hVmem hq.2
  · obtain ⟨y, hy, hGy⟩ : ∃ y ∈ Prod.mk (t : ℝ) ⁻¹' S, G (t, y) = f (0, x) := by
      obtain ⟨⟨s, y⟩, hy, hsy⟩ := hVmem (t := t) hx
      obtain ⟨rfl, h⟩ := Prod.ext_iff.1 hsy
      exact ⟨y, hy, h⟩
    have hmem : Ψ (t, f (0, x)) ∈ Prod.mk (t : ℝ) ⁻¹' S := invFunOn_mem ⟨y, hy, hGy⟩
    have heq : G (t, Ψ (t, f (0, x))) = f (0, x) := invFunOn_eq (f := fun y ↦ G ((t : ℝ), y))
      ⟨y, hy, hGy⟩
    have hκB : Ψ (t, f (0, x)) ∈ B := hmem.2.2
    rw [hGcoe] at heq
    have hκe : e (t, Ψ (t, f (0, x))) = e (0, x) :=
      φ.injOn (hB t _ hκB).2 (hB 0 x (hVB hx)).2 heq
    refine ⟨(hB t _ hκB).1, hκe, fun hx' ↦ ?_⟩
    exact hinj t (hB t _ hκB).1 (hB t x (hVB hx)).1 (hκe.trans hx'.symm)

end SymplecticGeometry

end
