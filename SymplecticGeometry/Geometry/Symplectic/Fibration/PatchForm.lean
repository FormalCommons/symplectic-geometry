/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Fibration.Curvature
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Opens
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import SymplecticGeometry.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# A two-form on `EB × F` that reads a two-form on `M` near a point of a patch

Let `A` be a smooth atlas of `proj : M → B` with fibre `F`, over a base without boundary, and
let `τ` be a two-form on `M` that is vertically closed and restricts to `σ` on the fibres of `A`.
For a chart `e = A.trivAt b'` and the extended chart `φ` of `B` at `b₀`, the map
`ψ q = e⁻¹ (φ⁻¹ q.1, q.2)` reads `τ` as the two-form `ψ^* τ` on `EB × F`, but only over the
patch `W` of the points `x` of the target of `φ` with `φ⁻¹ x` in the base set of `e`.

This file builds, near a point `x₀` of `W`, a two-form `τ'` on all of `EB × F` that is
`ψ^* τ` near the fibre over `x₀` and has the properties that the curvature computations of
`Fibration/Curvature.lean` ask of a form on `EB × F`: its fibre components are all `σ`, and it is
vertically closed for `Prod.fst`. With a bump function `χ` on `EB`, equal to `1` near `x₀` and
supported in `W`, it is

`τ' = χ • ψ^* τ + (1 - χ) • pr₂^* σ`,

the first term being extended by zero off `W`.

## Main results

* `TauCeti.MapFiber.Atlas.IsContMDiff.exists_isVerticallyClosed_eq_mpullback_patchMap`:
  the existence of such a `τ'`, together with an open neighbourhood `U` of `x₀` over which it is
  `ψ^* τ`, and such that its pull-back by `p ↦ (φ (proj p), (e p).2)` is `τ` near every point
  of `M` over a point `c` of the patch with `φ c ∈ U`.

## Implementation notes

The smoothness of the first term is `TauCeti.isSmoothForm_fun_smul_of_mpullback_subtypeVal`.
Vertical closedness is the blending lemma
`TauCeti.RoughForm.IsVerticallyClosedOn.smul_add_one_sub_smul_of_tsupport_subset`, for the
weight `χ` supported in `W`. Its hypotheses hold: over `W`, `ψ^* τ` is vertically closed by
`TauCeti.SmoothTwoForm.IsVerticallyClosed.isVerticallyClosedOn_mpullback_patchMap`;
`pr₂^* σ` is closed, since `σ` is closed by
`TauCeti.SmoothTwoForm.IsVerticallyClosed.isClosed_of_restrictsTo`; and the two agree on
vertical pairs over `W`, both having fibre components `σ`, by
`TauCeti.MapFiber.Atlas.RestrictsTo.fiberComponent_mpullback_patchMap` and
`TauCeti.SmoothForm.mpullback_prodMk_mpullback_snd`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §6.3–6.4.
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*}
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] {B : Type*}
  [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type*} [TopologicalSpace F]
  [ChartedSpace HF F] [IsManifold IF ∞ F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M]
  {proj : M → B} {A : MapFiber.Atlas F proj}

/-- **A two-form on `EB × F` reading `τ` near a point of a patch.** Let `A` be a smooth atlas
of `proj : M → B` with fibre `F`, over a base without boundary modelled on a finite-dimensional
space `EB`, and `τ` a vertically closed two-form on `M` that restricts to `σ` on the fibres of
`A`. Take a chart `e = A.trivAt b'`, the extended chart `φ` of `B` at `b₀`, the map
`ψ q = e⁻¹ (φ⁻¹ q.1, q.2)`, and a point `b` of the base set of `e` in the source of the chart of
`B` at `b₀`. Then there are an open neighbourhood `U` of `φ b` in `EB` and a two-form `τ'` on
`EB × F` such that
1. the fibre component of `τ'` over every `x : EB` is `σ`;
2. `τ'` is vertically closed for `Prod.fst`;
3. `τ'` is `ψ^* τ` at the points of `U ×ˢ univ`;
4. for every point `c` of the base set of `e` in the source of the chart at `b₀` with `φ c ∈ U`,
   and every `y : F`, the pull-back of `τ'` by `p ↦ (φ (proj p), (e p).2)` is `τ` near
   `e⁻¹ (c, y)`. -/
theorem MapFiber.Atlas.IsContMDiff.exists_isVerticallyClosed_eq_mpullback_patchMap
    [FiniteDimensional ℝ EB] [IsManifold IB ∞ B] (hA : A.IsContMDiff ∞ IB IF IM)
    {σ : SmoothTwoForm IF F} {τ : SmoothTwoForm IM M}
    (hτ : SmoothTwoForm.IsVerticallyClosed IB proj τ) (hτσ : A.RestrictsTo σ τ) {b' b₀ b : B}
    (hb : b ∈ (A.trivAt b').baseSet ∩ (chartAt HB b₀).source) :
    ∃ U : Set EB, IsOpen U ∧ extChartAt IB b₀ b ∈ U ∧
      ∃ τ' : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F),
        (∀ x, τ'.smoothFiberComponent x = σ) ∧
        SmoothTwoForm.IsVerticallyClosed 𝓘(ℝ, EB) Prod.fst τ' ∧
        (∀ z ∈ U ×ˢ (univ : Set F),
          τ'.val z = mpullback (𝓘(ℝ, EB).prod IF) IM (A.patchMap IB b' b₀) τ.val z) ∧
        ∀ c ∈ (A.trivAt b').baseSet ∩ (chartAt HB b₀).source, extChartAt IB b₀ c ∈ U →
          ∀ y : F, ∀ᶠ p in 𝓝 ((A.trivAt b').toOpenPartialHomeomorph.symm (c, y)),
            mpullback IM (𝓘(ℝ, EB).prod IF)
              (fun p ↦ (extChartAt IB b₀ (proj p), (A.trivAt b' p).2)) τ'.val p = τ.val p := by
  set e := A.trivAt b'
  set φ := extChartAt IB b₀
  set W := φ.target ∩ φ.symm ⁻¹' e.baseSet
  set ψ := A.patchMap IB b' b₀
  set μ := mpullback (𝓘(ℝ, EB).prod IF) IM ψ τ.val
  set νs : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F) :=
    SmoothForm.mpullback Prod.snd contMDiff_snd σ
  set ν := νs.val
  have hWo : IsOpen W := e.isOpen_extChartAt_target_inter_symm_preimage_baseSet b₀
  have hbφ : b ∈ φ.source := by rw [extChartAt_source]; exact hb.2
  have hbW : φ b ∈ W := ⟨φ.map_source hbφ, by
    rw [mem_preimage, φ.left_inv hbφ]; exact hb.1⟩
  -- A bump function `χ` on `EB`, equal to `1` near `φ b` and supported in `W`.
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo _ hbW
  let χ : ContDiffBump (φ b) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hχW : tsupport χ ⊆ W := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simp [χ]; linarith)).trans hεW
  have hχ : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ) ∞ χ := χ.contDiff.contMDiff
  have hg : ContMDiff (𝓘(ℝ, EB).prod IF) 𝓘(ℝ) ∞ fun z : EB × F ↦ χ z.1 :=
    hχ.comp contMDiff_fst
  have hgW : tsupport (fun z : EB × F ↦ χ z.1) ⊆ W ×ˢ univ := by
    rw [prod_univ]
    exact (tsupport_comp_subset_preimage χ continuous_fst).trans (preimage_mono hχW)
  -- The facts about the two forms that are blended.
  set WU : TopologicalSpace.Opens (EB × F) := ⟨W ×ˢ univ, hWo.prod isOpen_univ⟩
  have hμ := hA.contMDiffOn_mpullback_patchMap b' b₀ τ
  have h₁ := isSmoothForm_fun_smul_of_mpullback_subtypeVal (W := WU) hg hgW
    (isSmoothForm_mpullback_subtypeVal_of_contMDiffOn hμ)
  have h₂ := νs.isSmoothForm.fun_smul ((contMDiff_const (c := (1 : ℝ))).sub hg)
  let τ' : SmoothTwoForm (𝓘(ℝ, EB).prod IF) (EB × F) :=
    ⟨fun z ↦ χ z.1 • μ z + (1 - χ z.1) • ν z, (h₁.add h₂).mem_smoothBundleForms⟩
  have hτ' (z : EB × F) : τ'.val z = χ z.1 • μ z + (1 - χ z.1) • ν z := rfl
  have : Nonempty B := ⟨b⟩
  have hσc : σ.IsClosed := hτ.isClosed_of_restrictsTo hA hτσ
  have hνc : RoughForm.IsVerticallyClosedOn 𝓘(ℝ, EB) Prod.fst ν univ :=
    SmoothTwoForm.isVerticallyClosedOn_univ_iff.2 (hσc.mpullback _ contMDiff_snd).isVerticallyClosed
  have hfibμ {x : EB} (hx : x ∈ W) : RoughForm.fiberComponent μ x = σ.val :=
    hτσ.fiberComponent_mpullback_patchMap hA (by simp) hx
  have hfibν (x : EB) : RoughForm.fiberComponent ν x = σ.val := by
    rw [← SmoothTwoForm.coe_smoothFiberComponent, SmoothTwoForm.smoothFiberComponent_def,
      SmoothForm.mpullback_prodMk_mpullback_snd]
  -- On a pair of vectors tangent to a fibre, the two forms take the value of `σ`.
  have hvert {x : EB} {y : F} (w₁ w₂ : TangentSpace IF y) :
      ν (x, y) ![((0 : EB), w₁), ((0 : EB), w₂)] = σ.val y ![w₁, w₂] ∧
        (x ∈ W → μ (x, y) ![((0 : EB), w₁), ((0 : EB), w₂)] = σ.val y ![w₁, w₂]) :=
    ⟨by rw [← RoughForm.fiberComponent_apply, hfibν],
      fun hx ↦ by rw [← RoughForm.fiberComponent_apply, hfibμ hx]⟩
  have hχ0 {x : EB} (hx : x ∉ W) : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχW h)
  -- Over `U`, `χ = 1`, so `τ'` is `ψ^* τ`.
  have hU {z : EB × F} (hz : z.1 ∈ Metric.ball (φ b) (ε / 4)) : τ'.val z = μ z := by
    rw [hτ', χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul, sub_self,
      zero_smul, add_zero]
  refine ⟨Metric.ball (φ b) (ε / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    τ', fun x ↦ ?_, ?_, fun z hz ↦ hU hz.1, fun c hc hcU y ↦ ?_⟩
  · -- The fibre components.
    have hval : τ'.val = (fun z ↦ χ z.1 • μ z) + fun z ↦ (1 - χ z.1) • ν z :=
      funext fun z ↦ by rw [Pi.add_apply, hτ']
    refine Subtype.ext ?_
    rw [SmoothTwoForm.coe_smoothFiberComponent, hval, RoughForm.fiberComponent_add,
      RoughForm.fiberComponent_fun_smul_fst,
      RoughForm.fiberComponent_fun_smul_fst (f := fun x ↦ 1 - χ x), hfibν]
    by_cases hx : x ∈ W
    · rw [hfibμ hx, ← add_smul, add_sub_cancel, one_smul]
    · rw [hχ0 hx, zero_smul, zero_add, sub_zero, one_smul]
  · -- Vertical closedness.
    rw [← SmoothTwoForm.isVerticallyClosedOn_univ_iff, show τ'.val = _ from funext hτ']
    refine RoughForm.IsVerticallyClosedOn.smul_add_one_sub_smul_of_tsupport_subset (f := χ)
      (proj := Prod.fst) hχW continuous_fst
      (prod_univ (s := W) ▸
        hτ.isVerticallyClosedOn_mpullback_patchMap hA (by simp) b' b₀) hνc
      (fun _ _ ↦ mdifferentiableAt_fst) (fun _ _ ↦ (hχ _).mdifferentiableAt (by simp))
      (fun q hq ↦ (hμ.contMDiffAt ((hWo.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)
        ).mdifferentiableAt (by simp))
      (fun q _ ↦ (νs.contMDiff q).mdifferentiableAt (by simp)) ?_
    rintro ⟨x, y⟩ hq u₁ hu₁ u₂ hu₂
    rw [mem_ker_mfderiv_fst_iff] at hu₁ hu₂
    have hu₁' : u₁ = ((0 : EB), u₁.2) := Prod.ext hu₁ rfl
    have hu₂' : u₂ = ((0 : EB), u₂.2) := Prod.ext hu₂ rfl
    rw [hu₁', hu₂', (hvert u₁.2 u₂.2).1, (hvert u₁.2 u₂.2).2 hq]
  · -- The pull-back by `Φ`.
    set Φ : M → EB × F := fun p ↦ (φ (proj p), (e p).2) with hΦdef
    set p₀ := e.toOpenPartialHomeomorph.symm (c, y)
    have hp₀ : proj p₀ = c := e.proj_symm_apply' hc.1
    have hep₀ : e p₀ = (c, y) := e.apply_symm_apply' hc.1
    have hproj := hA.contMDiff_proj (n := ∞)
    set S := e.source ∩ proj ⁻¹' (chartAt HB b₀).source
    have hS : IsOpen S :=
      e.open_source.inter ((chartAt HB b₀).open_source.preimage hproj.continuous)
    have hp₀S : p₀ ∈ S := ⟨e.mem_source.2 (by rw [hp₀]; exact hc.1),
      by rw [mem_preimage, hp₀]; exact hc.2⟩
    have hΦ {p : M} (hp : p ∈ S) : ContMDiffAt IM (𝓘(ℝ, EB).prod IF) ∞ Φ p :=
      hA.contMDiffAt_extChartAt_proj_prodMk_snd le_rfl (e.mem_source.1 hp.1) hp.2
    have hΦp₀ : Φ p₀ = (φ c, y) := by simp only [hΦdef, hp₀, hep₀]
    have hUo : IsOpen (Metric.ball (φ b) (ε / 4) ×ˢ (univ : Set F)) :=
      Metric.isOpen_ball.prod isOpen_univ
    filter_upwards [hS.mem_nhds hp₀S, (hΦ hp₀S).continuousAt.preimage_mem_nhds
      (hUo.mem_nhds (by rw [hΦp₀]; exact ⟨hcU, mem_univ _⟩))] with p hp hpU
    -- `ψ ∘ Φ` is the identity near `p`.
    have hid : ψ ∘ Φ =ᶠ[𝓝 p] id := Filter.eventually_of_mem (hS.mem_nhds hp) fun q hq ↦
      A.patchMap_extChartAt_proj_snd hq.1 hq.2
    have hpW : (Φ p).1 ∈ W :=
      hεW (Metric.ball_subset_ball (by linarith) (show (Φ p).1 ∈ _ from hpU.1))
    have hψ : MDifferentiableAt (𝓘(ℝ, EB).prod IF) IM ψ (Φ p) :=
      (hA.contMDiffAt_patchMap (q := Φ p) hpW).mdifferentiableAt (by simp)
    rw [mpullback_apply_congr (hU hpU.1),
      ← mpullback_comp_at ((hΦ hp).mdifferentiableAt (by simp)) hψ, hid.mpullback_apply_eq_self]

end TauCeti

end
