/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import SymplecticGeometry.Geometry.Manifold.ContMDiff.TimeExtension
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Parametric
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

The proof reads `e` in the chart of `M` at `e (0, x₀)`, extends it in time to `ℝ` by
`SymplecticGeometry.timeExtend`, and applies Tau Ceti's parametric inverse function theorem
`ContDiffOn.parametric_invFunOn_of_injective_fderiv` to the extension on an open neighbourhood
of `[0, 1] × {x₀}` on which the map `(t, x) ↦ (t, e (t, x))`, read in the chart, is injective
with invertible derivative. Such a neighbourhood exists by compactness of `[0, 1]`
(`Set.InjOn.exists_isOpen_superset`).

## Main results

* `DifferentiableAt.injective_fderiv_fst_prodMk_iff`: the derivative of `q ↦ (q.1, g q)` is
  injective exactly when the derivative of the slice of `g` in the second variable is.
* `SymplecticGeometry.exists_contMDiffOn_apply_eq_apply_zero`: the jointly smooth inverse.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 7.1.22, whose transition germs of a family of ball embeddings use this inverse.
-/

public section

open Function Set Metric
open scoped Manifold ContDiff Topology

section FDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {P E F : Type*} [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

/-- For `g : P × E → F` differentiable at `q`, the derivative at `q` of `p ↦ (p.1, g p)` is
injective exactly when the derivative at `q.2` of the slice `x ↦ g (q.1, x)` is. -/
theorem DifferentiableAt.injective_fderiv_fst_prodMk_iff {g : P × E → F} {q : P × E}
    (hg : DifferentiableAt 𝕜 g q) :
    Injective (fderiv 𝕜 (fun p ↦ (p.1, g p)) q) ↔
      Injective (fderiv 𝕜 (fun x ↦ g (q.1, x)) q.2) := by
  obtain ⟨a, b⟩ := q
  rw [differentiableAt_fst.fderiv_prodMk hg, fderiv_fst, TauCeti.fderiv_slice_right hg,
    injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  constructor
  · intro h v hv
    have := h (0, v) (by simpa using hv)
    simpa using this
  · rintro h ⟨s, v⟩ hv
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.mk_eq_zero]
      at hv
    obtain ⟨rfl, hv⟩ := hv
    simpa using h v (by simpa using hv)

end FDeriv

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
  obtain ⟨B, hBo, hx₀B, hB⟩ : ∃ B : Set F, IsOpen B ∧ x₀ ∈ B ∧
      ∀ t, ∀ x ∈ B, x ∈ U ∧ e (t, x) ∈ φ.source := by
    have hW := he.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU)
      (isOpen_extChartAt_source (I := I) p₀)
    obtain ⟨u, v, -, hv, hu, hxv, huv⟩ := generalized_tube_lemma isCompact_univ
      isCompact_singleton hW (s := univ) (t := {x₀}) (by
        rintro ⟨t, x⟩ ⟨-, hx⟩
        have hx' : x = x₀ := hx
        rw [hx']
        exact ⟨⟨trivial, hx₀⟩, by simp [hfix t]⟩)
    exact ⟨v, hv, hxv rfl, fun t x hx ↦ by
      have := huv (mk_mem_prod (hu (mem_univ t)) hx)
      exact ⟨this.1.2, this.2⟩⟩
  -- `e` read in the chart, and its extension `G` in time.
  set f : unitInterval × F → E := fun q ↦ φ (e q)
  have hf : ContMDiffOn ((𝓡∂ 1).prod 𝓘(ℝ, F)) 𝓘(ℝ, E) ∞ f (univ ×ˢ B) :=
    contMDiffOn_extChartAt.comp (he.mono fun q hq ↦ ⟨trivial, (hB q.1 q.2 hq.2).1⟩)
      fun q hq ↦ by simpa [φ] using (hB q.1 q.2 hq.2).2
  set G := timeExtend f
  have hO : IsOpen (univ ×ˢ B : Set (ℝ × F)) := isOpen_univ.prod hBo
  have hG : ContDiffOn ℝ ∞ G (univ ×ˢ B) := by
    have := hf.timeExtend hBo
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at this
    exact contMDiffOn_iff_contDiffOn.1 this
  have hGcoe (t : unitInterval) (x : F) : G (t, x) = f (t, x) := timeExtend_apply_coe f t x
  have hGslice (t : unitInterval) : (fun x ↦ G (t, x)) = fun x ↦ φ (e (t, x)) := by
    funext x
    exact timeExtend_apply_coe f t x
  set Φ : ℝ × F → ℝ × E := fun q ↦ (q.1, G q)
  have hΦ : ContDiffOn ℝ ∞ Φ (univ ×ˢ B) := contDiffOn_fst.prodMk hG
  have hGd {q : ℝ × F} (hq : q ∈ univ ×ˢ B) : DifferentiableAt ℝ G q :=
    (hG.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hΦd {q : ℝ × F} (hq : q ∈ univ ×ˢ B) : DifferentiableAt ℝ Φ q :=
    (hΦ.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hfin : Module.finrank ℝ (ℝ × F) = Module.finrank ℝ (ℝ × E) := by
    simp [Module.finrank_prod, hdim]
  -- The open set `A` where the derivative of `Φ` is invertible contains `[0, 1] × {x₀}`.
  set A := univ ×ˢ B ∩
    (fderiv ℝ Φ) ⁻¹' range ((↑) : ((ℝ × F) ≃L[ℝ] (ℝ × E)) → (ℝ × F) →L[ℝ] (ℝ × E))
  have hA : IsOpen A := (hΦ.continuousOn_fderiv_of_isOpen hO (by simp)).isOpen_inter_preimage hO
    ContinuousLinearEquiv.isOpen
  have hAinj {q} (hq : q ∈ A) : Injective (fderiv ℝ (fun x ↦ G (q.1, x)) q.2) := by
    obtain ⟨L, hL⟩ := hq.2
    rw [← DifferentiableAt.injective_fderiv_fst_prodMk_iff (hGd hq.1)]
    -- fold the local definition of `Φ`
    change Injective (fderiv ℝ Φ q)
    rw [← hL]
    exact L.injective
  have hKA : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ A := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have hx' : x = x₀ := hx
    rw [hx']
    refine ⟨⟨trivial, hx₀B⟩, ?_⟩
    have hinjΦ : Injective (fderiv ℝ Φ (t, x₀)) := by
      rw [DifferentiableAt.injective_fderiv_fst_prodMk_iff (hGd ⟨trivial, hx₀B⟩)]
      -- see `t` as the coercion of a point of `unitInterval`, to use `hGslice`
      change Injective (fderiv ℝ (fun x ↦ G ((⟨t, ht⟩ : unitInterval), x)) x₀)
      rw [hGslice]
      have hφ : MDifferentiableAt I 𝓘(ℝ, E) φ (e (⟨t, ht⟩, x₀)) :=
        mdifferentiableAt_extChartAt (by simpa [φ] using (hB ⟨t, ht⟩ x₀ hx₀B).2)
      have het : MDifferentiableAt 𝓘(ℝ, F) I (fun x ↦ e (⟨t, ht⟩, x)) x₀ :=
        ((he.contMDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨trivial, hx₀⟩)).comp x₀
          (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
      have hm : Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) (fun x ↦ φ (e (⟨t, ht⟩, x))) x₀) := by
        rw [show (fun x ↦ φ (e (⟨t, ht⟩, x))) = φ ∘ fun x ↦ e (⟨t, ht⟩, x) from rfl,
          mfderiv_comp x₀ hφ het]
        exact (isInvertible_mfderiv_extChartAt
          (by simpa [φ] using (hB ⟨t, ht⟩ x₀ hx₀B).2)).injective.comp (hd _)
      rw [mfderiv_eq_fderiv] at hm
      exact fun a b hab ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) x₀).symm.injective
        (hm (by simp [hab]))
    obtain ⟨L, hL⟩ := (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hfin).2
      hinjΦ
    exact ⟨L, hL⟩
  have hstrict {q} (hq : q ∈ A) :
      ∃ L : (ℝ × F) ≃L[ℝ] (ℝ × E), HasStrictFDerivAt Φ (L : (ℝ × F) →L[ℝ] (ℝ × E)) q := by
    obtain ⟨L, hL⟩ := hq.2
    refine ⟨L, ?_⟩
    rw [hL]
    exact (hΦ.contDiffAt (hO.mem_nhds hq.1)).hasStrictFDerivAt_fderiv (by simp)
  -- An open neighbourhood `T` of `[0, 1] × {x₀}` on which `Φ` is injective.
  obtain ⟨T, hT, hKT, hTinj⟩ := Set.InjOn.exists_isOpen_superset (f := Φ)
    (s := Icc (0 : ℝ) 1 ×ˢ {x₀})
    (by
      intro p hp q hq h
      exact Prod.ext (by simpa [Φ] using congrArg Prod.fst h)
        ((mem_singleton_iff.1 hp.2).trans (mem_singleton_iff.1 hq.2).symm))
    (isCompact_Icc.prod isCompact_singleton) (fun q hq ↦ (hΦd (hKA hq).1).continuousAt)
    fun q hq ↦ by
      obtain ⟨L, hL⟩ := hstrict (hKA hq)
      have hinj' := (hL.toOpenPartialHomeomorph Φ).injOn
      rw [hL.toOpenPartialHomeomorph_coe] at hinj'
      exact ⟨_, (hL.toOpenPartialHomeomorph Φ).open_source.mem_nhds
        hL.mem_toOpenPartialHomeomorph_source, hinj'⟩
  set S := T ∩ A
  have hS : IsOpen S := hT.inter hA
  have hKS : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ S := subset_inter hKT hKA
  -- The parametric inverse.
  have hGS : ContDiffOn ℝ ∞ G S := hG.mono (inter_subset_right.trans inter_subset_left)
  have hκ := hGS.parametric_invFunOn_of_injective_fderiv hS (by simp)
    (fun p x hx y hy hxy ↦ (Prod.ext_iff.1 (hTinj hx.1 hy.1 (Prod.ext rfl hxy))).2)
    (fun q hq ↦ hAinj hq.2) hdim
  have hΦS : IsOpen (Φ '' S) := by
    refine isOpen_iff_mem_nhds.2 ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨L, hL⟩ := hstrict hq.2
    rw [← hL.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hS.mem_nhds hq)
  -- A ball `V` about `x₀` on which `(t, f (0, x))` stays in `Φ '' S`.
  obtain ⟨u, v, -, hv, hu, hφv, huv⟩ := generalized_tube_lemma (isCompact_Icc (a := (0 : ℝ))
    (b := 1)) (isCompact_singleton (x := φ p₀)) hΦS (by
      rintro ⟨t, y⟩ ⟨ht, rfl⟩
      refine ⟨(t, x₀), hKS ⟨ht, rfl⟩, Prod.ext rfl ?_⟩
      -- see `t` as the coercion of a point of `unitInterval`, to use `hGcoe`
      change G ((⟨t, ht⟩ : unitInterval), x₀) = φ p₀
      rw [hGcoe]
      exact congrArg φ (hfix _))
  have hf0 : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (fun x ↦ f (0, x)) B :=
    hf.comp (contMDiffOn_const.prodMk contMDiffOn_id) fun x hx ↦ ⟨trivial, hx⟩
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1
    (hf0.continuousOn.isOpen_inter_preimage hBo hv) x₀ ⟨hx₀B, by simpa [f] using hφv rfl⟩
  set V := ball x₀ ρ
  have hVB : V ⊆ B := fun x hx ↦ (hρV hx).1
  have hVmem {t : unitInterval} {x : F} (hx : x ∈ V) : ((t : ℝ), f (0, x)) ∈ Φ '' S :=
    huv ⟨hu t.property, (hρV hx).2⟩
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
    have hκB : Ψ (t, f (0, x)) ∈ B := (hmem.2.1).2
    rw [hGcoe] at heq
    have hκe : e (t, Ψ (t, f (0, x))) = e (0, x) :=
      φ.injOn (hB t _ hκB).2 (hB 0 x (hVB hx)).2 heq
    refine ⟨(hB t _ hκB).1, hκe, fun hx' ↦ ?_⟩
    exact hinj t (hB t _ hκB).1 (hB t x (hVB hx)).1 (hκe.trans hx'.symm)

end SymplecticGeometry

end
