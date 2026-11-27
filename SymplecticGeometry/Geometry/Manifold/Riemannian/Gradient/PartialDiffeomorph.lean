/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The Riemannian gradient read through a partial diffeomorphism

Let `M` be a finite-dimensional manifold without boundary with a continuous Riemannian metric, and
let `e` be a `C¹` partial diffeomorphism from `M` to a normed space `F`, with `p` in its source.
If a function `f : M → ℝ` is `g ∘ e` on the source of `e`, then near `p` the Fréchet derivative of
`g` at `e y` is bounded by a fixed multiple of the Riemannian length of the gradient of `f` at `y`
(`PartialDiffeomorph.eventually_norm_fderiv_le_mul_norm_mgradient`). The constant and the
neighbourhood do not depend on `f` and `g`. So a Łojasiewicz gradient inequality for `g` near
`e p`, stated with the Fréchet derivative, gives one for `f` near `p`, stated with the Riemannian
gradient, with the same exponent
(`PartialDiffeomorph.exists_mul_abs_sub_rpow_le_norm_mgradient`).

The proof reads `g` in the preferred extended chart `φ` at `p`: near `e y`, `g` is
`(f ∘ φ.symm) ∘ (φ ∘ e.symm)`, whose second factor is `C¹`, so its derivative is locally
bounded, and the first factor is controlled by the gradient of `f` through Tau Ceti's
`TauCeti.Manifold.eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient`. The passage
from the derivative to the gradient in the second result follows Tau Ceti's
`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`, which does
this for the extended chart at `p` and the exponent `1 / 2`.

## Main results

* `PartialDiffeomorph.eventually_norm_fderiv_le_mul_norm_mgradient`: the derivative of `g` at
  `e y` is controlled by the gradient of `g ∘ e` at `y`, uniformly near `p`.
* `PartialDiffeomorph.exists_mul_abs_sub_rpow_le_norm_mgradient`: a Łojasiewicz inequality for
  `g` near `e p` gives one for `f` near `p`.

## References

* E. Lerman, *Gradient flow of the norm squared of a moment map*, Enseign. Math. 51 (2005),
  117–127, proof of Theorem 1.1.
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- **The derivative through a partial diffeomorphism is controlled by the gradient.** Let `e` be
a `C¹` partial diffeomorphism from a boundaryless manifold `M` with a continuous Riemannian metric
to a normed space `F`, with `p` in its source. Then there is a constant `C > 0` such that for `y`
near `p`, and for all functions `f : M → ℝ` and `g : F → ℝ` with `f = g ∘ e` on the source of `e`,
the Fréchet derivative of `g` at `e y` has norm at most `C` times the Riemannian length of the
gradient of `f` at `y`. -/
theorem eventually_norm_fderiv_le_mul_norm_mgradient (e : PartialDiffeomorph I 𝓘(ℝ, F) M F n)
    (hn : 1 ≤ n) {p : M} (hp : p ∈ e.source) :
    ∃ C > 0, ∀ᶠ y in 𝓝 p, ∀ (f : M → ℝ) (g : F → ℝ), (∀ z ∈ e.source, f z = g (e z)) →
      ‖fderiv ℝ g (e y)‖ ≤ C * ‖mgradient I f y‖ := by
  set φ := extChartAt I p
  have hl : ∀ y ∈ e.source, e.symm (e y) = y := fun _ hy ↦ e.left_inv hy
  have hr : ∀ z ∈ e.target, e (e.symm z) = z := fun _ hz ↦ e.right_inv hz
  have hm : ∀ z ∈ e.target, e.symm z ∈ e.source := fun _ hz ↦ e.map_target hz
  obtain ⟨C, hC, hbd⟩ := eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient
    (I := I) p
  -- The transition map `φ ∘ e.symm` is `C¹` on the open set `U`.
  set U := e.target ∩ e.symm ⁻¹' (chartAt H p).source
  have hU : IsOpen U :=
    e.symm.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_target
      (chartAt H p).open_source
  have hψ : ContDiffOn ℝ 1 (φ ∘ e.symm) U := contMDiffOn_iff_contDiffOn.1 <|
    (contMDiffOn_extChartAt (n := 1)).comp ((e.symm.contMDiffOn.of_le hn).mono
      inter_subset_left) fun _ hz ↦ hz.2
  -- The transition map `e ∘ φ.symm` is `C¹` on the open set `V`.
  set V := φ.target ∩ φ.symm ⁻¹' e.source
  have hV : IsOpen V := (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) e.open_source
  have hχ : ContDiffOn ℝ 1 (e ∘ φ.symm) V := contMDiffOn_iff_contDiffOn.1 <|
    ((e.contMDiffOn.of_le hn).comp ((contMDiffOn_extChartAt_symm (n := 1) p).mono
      inter_subset_left) fun _ hw ↦ hw.2)
  have hep : e p ∈ U := ⟨e.map_source hp, by
    simpa only [mem_preimage, hl _ hp] using mem_chart_source H p⟩
  -- The derivative of `φ ∘ e.symm` is bounded by `K` near `e p`.
  set K := ‖fderiv ℝ (φ ∘ e.symm) (e p)‖ + 1
  have hK : ∀ᶠ z in 𝓝 (e p), ‖fderiv ℝ (φ ∘ e.symm) z‖ < K :=
    ((hψ.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt
      (hU.mem_nhds hep)).norm.eventually (gt_mem_nhds (lt_add_one _))
  have he : ContinuousAt e p :=
    e.contMDiffOn.continuousOn.continuousAt (e.open_source.mem_nhds hp)
  refine ⟨C * K, by positivity, ?_⟩
  filter_upwards [hbd, he.eventually hK, e.open_source.mem_nhds hp,
    (chartAt H p).open_source.mem_nhds (mem_chart_source H p)] with y hy hyK hys hyc f g hfg
  have hyφ : y ∈ φ.source := by rwa [extChartAt_source]
  have hey : e y ∈ U := ⟨e.map_source hys, by simpa only [mem_preimage, hl _ hys]⟩
  have hφy : φ y ∈ V := ⟨φ.map_source hyφ, by simpa only [mem_preimage, φ.left_inv hyφ]⟩
  have hg : g =ᶠ[𝓝 (e y)] (f ∘ φ.symm) ∘ (φ ∘ e.symm) := by
    filter_upwards [hU.mem_nhds hey] with z hz
    have hzφ : e.symm z ∈ φ.source := by rw [extChartAt_source]; exact hz.2
    simp only [Function.comp_apply, φ.left_inv hzφ, hfg _ (hm _ hz.1), hr _ hz.1]
  have hF : f ∘ φ.symm =ᶠ[𝓝 (φ y)] g ∘ (e ∘ φ.symm) := by
    filter_upwards [hV.mem_nhds hφy] with w hw
    simp only [Function.comp_apply, hfg _ hw.2]
  have hψy : (φ ∘ e.symm) (e y) = φ y := congrArg φ (hl _ hys)
  by_cases hd : DifferentiableAt ℝ (f ∘ φ.symm) (φ y)
  · rw [hg.fderiv_eq, fderiv_comp _ (hψy ▸ hd)
      ((hψ.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hey)), hψy]
    calc _ ≤ ‖fderiv ℝ (f ∘ φ.symm) (φ y)‖ * ‖fderiv ℝ (φ ∘ e.symm) (e y)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * ‖mgradient I f y‖) * K := by gcongr; exact hy f
      _ = _ := by ring
  · -- Otherwise `g` is not differentiable at `e y` either, since `f ∘ φ.symm = g ∘ (e ∘ φ.symm)`
    -- near `φ y`.
    have hgd : ¬ DifferentiableAt ℝ g (e y) := fun h ↦ hd <| hF.differentiableAt_iff.2 <|
      (show e (φ.symm (φ y)) = e y by rw [φ.left_inv hyφ]) ▸ h |>.comp (φ y)
        ((hχ.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hφy))
    rw [fderiv_zero_of_not_differentiableAt hgd, norm_zero]
    positivity

/-- **A Łojasiewicz inequality passes through a partial diffeomorphism.** Let `e` be a `C¹`
partial diffeomorphism from a boundaryless manifold `M` with a continuous Riemannian metric to a
normed space `F`, with `p` in its source, and let `f = g ∘ e` on the source of `e`. If near `e p`
the inequality `|g z - g (e p)| ^ θ ≤ c * ‖Dg z‖` holds with `c > 0`, then near `p` the
inequality `c' * |f y - f p| ^ θ ≤ ‖grad f y‖` holds for some `c' > 0`. -/
theorem exists_mul_abs_sub_rpow_le_norm_mgradient (e : PartialDiffeomorph I 𝓘(ℝ, F) M F n)
    (hn : 1 ≤ n) {p : M} (hp : p ∈ e.source) {f : M → ℝ} {g : F → ℝ}
    (hfg : ∀ y ∈ e.source, f y = g (e y)) {c θ : ℝ} (hc : 0 < c)
    (hL : ∀ᶠ z in 𝓝 (e p), |g z - g (e p)| ^ θ ≤ c * ‖fderiv ℝ g z‖) :
    ∃ c' > 0, ∀ᶠ y in 𝓝 p, c' * |f y - f p| ^ θ ≤ ‖mgradient I f y‖ := by
  obtain ⟨C, hC, hbd⟩ := e.eventually_norm_fderiv_le_mul_norm_mgradient hn hp
  have he : ContinuousAt e p :=
    e.contMDiffOn.continuousOn.continuousAt (e.open_source.mem_nhds hp)
  refine ⟨(c * C)⁻¹, by positivity, ?_⟩
  filter_upwards [hbd, he.eventually hL, e.open_source.mem_nhds hp] with y hy hyL hys
  rw [hfg y hys, hfg p hp, inv_mul_le_iff₀ (by positivity)]
  calc |g (e y) - g (e p)| ^ θ ≤ c * ‖fderiv ℝ g (e y)‖ := hyL
    _ ≤ c * (C * ‖mgradient I f y‖) := by gcongr; exact hy f g hfg
    _ = c * C * ‖mgradient I f y‖ := by ring

end PartialDiffeomorph

end
