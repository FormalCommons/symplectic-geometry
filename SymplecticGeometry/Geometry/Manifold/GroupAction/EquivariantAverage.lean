/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.RepresentationTheory.Continuous.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.ContMDiff.PartialDeriv
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Smoothness of the equivariant average of a map

Let a compact Lie group `G` act smoothly on a manifold `M` without boundary, let `σ` be a
continuous representation of `G` on a real normed space `F`, `μ` a finite measure on `G`, and
`φ : M → F` a `C^n` map on an open set `U`. The *equivariant average* of `φ` is
`A y = ∫ k, σ k (φ (k⁻¹ • y)) ∂μ`. For a left-invariant `μ` it intertwines the action on `M`
with `σ` (this is Tau Ceti's `ContRepresentation.integral_apply_inv_smul_smul`). This file shows
that `A` is `C^n` on the set of `y` whose whole orbit lies in `U`, which is open by Tau Ceti's
`TauCeti.isOpen_setOf_forall_smul_mem`, computes its derivative there as the integral of the
derivatives of the maps `y ↦ σ k (φ (k⁻¹ • y))`, and specializes this at a fixed point `x` of
the action, with `σ` the isotropy representation at `x`: if `φ` has derivative the identity at
`x`, so has `A`. (If moreover `φ x = 0`, then `A x = 0`, since the integrand vanishes at `x`.)

The proofs read `A` in the chart `extChartAt I y` at each point `y` and differentiate under the
integral sign there; since `σ` is only continuous in `k`, they use that the derivatives in the
chart variable of the integrand are jointly continuous in that variable and in `k`
(Tau Ceti's `ContMDiffOn.continuousOn_iteratedFDeriv_partial` and
`TauCeti.contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv`). This follows the analytic
step of Tau Ceti's `TauCeti.exists_equivariant_contMDiff_chart_of_compactSpace`, which does it
for `φ = extChartAt I x - extChartAt I x x` at the fixed point `x` only.

## Main results

* `ContMDiffOn.integral_apply_inv_smul`: the equivariant average of a `C^n` map on `U` is `C^n`
  on the points whose orbit lies in `U`.
* `ContMDiffOn.hasMFDerivAt_integral_apply_inv_smul`: its derivative there.
* `ContMDiffOn.hasMFDerivAt_integral_apply_inv_smul_of_smul_eq`: at a fixed point `x`, with `σ`
  the derivative of the action at `x`, the average of a map with derivative the identity at `x`
  has derivative the identity at `x`.

## References

* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46 (1945),
  372–381.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Universitext, Springer, 2000, Section 2.2.
-/

public section

noncomputable section

open Set Filter MeasureTheory Function TauCeti
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [IG.Boundaryless]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [ChartedSpace HG G] [MeasurableSpace G] [BorelSpace G] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞}
  [IsManifold I n M] [IsManifold IG n G] [ContMDiffSMul IG I n G M]
  {μ : Measure G} [IsFiniteMeasure μ] {σ : ContRepresentation ℝ G F} {φ : M → F} {U : Set M}

include IG in
/-- The equivariant average read in the chart `extChartAt I y₀`: on the open set of chart points
whose orbit lies in `U`, it is `C^n`, and it has there the derivative obtained by differentiating
under the integral sign. -/
private theorem integral_apply_inv_smul_extChartAt
    (hσ : Continuous σ) (hU : IsOpen U) (hφ : ContMDiffOn I 𝓘(ℝ, F) n φ U) (y₀ : M) :
    IsOpen ((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U}) ∧
    (∀ k : G, ContDiffOn ℝ n (fun w ↦ σ k (φ (k⁻¹ • (extChartAt I y₀).symm w)))
      ((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U})) ∧
    ContDiffOn ℝ n (fun w ↦ ∫ k, σ k (φ (k⁻¹ • (extChartAt I y₀).symm w)) ∂μ)
      ((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U}) ∧
    (1 ≤ n → ContinuousOn
      (fun p : E × G ↦ fderiv ℝ (fun w ↦ σ p.2 (φ (p.2⁻¹ • (extChartAt I y₀).symm w))) p.1)
      (((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U}) ×ˢ
        univ)) ∧
    (1 ≤ n → ∀ w ∈ (extChartAt I y₀).target ∩
        (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U},
      HasFDerivAt (fun w ↦ ∫ k, σ k (φ (k⁻¹ • (extChartAt I y₀).symm w)) ∂μ)
        (∫ k, fderiv ℝ (fun w ↦ σ k (φ (k⁻¹ • (extChartAt I y₀).symm w))) w ∂μ) w) := by
  have hsmul := ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := n) (G := G) (M := M)
  have : ContinuousSMul G M := ⟨hsmul.continuous⟩
  set χ := extChartAt I y₀
  -- The action in the chart variable, `Ψ (w, k) = φ (k • χ.symm w)`, is jointly `C^n` on the
  -- open set `W` where it is defined.
  let Ψ : E × G → F := fun p ↦ φ (p.2 • χ.symm p.1)
  let W : Set (E × G) := {p | p.1 ∈ χ.target ∧ p.2 • χ.symm p.1 ∈ U}
  have hact : ContMDiffOn (𝓘(ℝ, E).prod IG) I n (fun p : E × G ↦ p.2 • χ.symm p.1)
      (χ.target ×ˢ univ) :=
    hsmul.comp_contMDiffOn (contMDiffOn_snd.prodMk
      ((contMDiffOn_extChartAt_symm y₀).comp contMDiffOn_fst fun _ hp ↦ (mem_prod.1 hp).1))
  have hW : IsOpen W := by
    have := hact.continuousOn.isOpen_inter_preimage
      ((isOpen_extChartAt_target y₀).prod isOpen_univ) hU
    convert this using 1
    ext p
    simp [W]
  have hΨ : ContMDiffOn (𝓘(ℝ, E).prod IG) 𝓘(ℝ, F) n Ψ W :=
    hφ.comp (hact.mono fun p hp ↦ ⟨hp.1, mem_univ _⟩) fun p hp ↦ hp.2
  -- The set `V` of chart points whose orbit lies in `U`.
  let V : Set E := χ.target ∩ χ.symm ⁻¹' {y | ∀ k : G, k • y ∈ U}
  have hV : IsOpen V := (continuousOn_extChartAt_symm y₀).isOpen_inter_preimage
    (isOpen_extChartAt_target y₀) (isOpen_setOf_forall_smul_mem hU)
  have hVW {w : E} (hw : w ∈ V) (k : G) : (w, k) ∈ W := ⟨hw.1, hw.2 k⟩
  have hΨV (k : G) : ContDiffOn ℝ n (fun w ↦ Ψ (w, k)) V := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hΨ.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun w hw ↦ hVW hw k
  -- The integrand `Φ (w, k) = σ k (Ψ (w, k⁻¹))`.
  let Φ : E × G → F := fun p ↦ σ p.2 (Ψ (p.1, p.2⁻¹))
  have hΦV (k : G) : ContDiffOn ℝ n (fun w ↦ Φ (w, k)) V :=
    (σ k).contDiff.comp_contDiffOn (hΨV k⁻¹)
  have hΦcont (m : ℕ) (hm : (m : ℕ∞) ≤ n) : ContinuousOn
      (fun p : E × G ↦ iteratedFDeriv ℝ m (fun w ↦ Φ (w, p.2)) p.1) (V ×ˢ univ) :=
    continuousOn_iteratedFDeriv_partial_clm_apply (F := fun p ↦ Ψ (p.1, p.2⁻¹))
      (L := fun k ↦ σ k) (hσ.comp continuous_snd).continuousOn
      (fun p hp ↦ ((hΨV p.2⁻¹).contDiffAt (hV.mem_nhds hp.1)).of_le (by exact_mod_cast hm))
      ((hΨ.continuousOn_iteratedFDeriv_partial hW (by exact_mod_cast hm)).comp
        (continuous_fst.prodMk continuous_snd.inv).continuousOn fun p hp ↦ hVW hp.1 p.2⁻¹)
  have hDcont (hn : 1 ≤ n) : ContinuousOn
      (fun p : E × G ↦ fderiv ℝ (fun w ↦ Φ (w, p.2)) p.1) (V ×ˢ univ) :=
    continuousOn_iteratedFDeriv_zero_partial_iff.1
      (continuousOn_iteratedFDeriv_fderiv_partial (hΦcont 1 hn))
  refine ⟨hV, hΦV, ?_, hDcont, fun hn w hw ↦ ?_⟩
  · simpa only [one_smul] using contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv
      (g := fun _ ↦ (1 : ℝ)) (integrable_const (1 : ℝ)) (μ := μ) hV hΦV hΦcont
  · have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
    simpa only [one_smul] using hasFDerivAt_integral_smul_of_continuousOn_fderiv
      (g := fun _ ↦ (1 : ℝ)) (integrable_const (1 : ℝ)) (μ := μ) hV
      (continuousOn_iteratedFDeriv_zero_partial_iff.1 (hΦcont 0 (by simp)))
      (fun k ↦ (hΦV k).differentiableOn (zero_lt_one.trans_le hn').ne') (hDcont hn) hw

omit [I.Boundaryless] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G]
  [IsFiniteMeasure μ] in
/-- Near a point `y₀`, the equivariant average agrees with its reading in the chart at `y₀`. -/
private theorem integral_apply_inv_smul_eventuallyEq_extChartAt (y₀ : M) :
    (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) =ᶠ[𝓝 y₀]
      (fun w ↦ ∫ k, σ k (φ (k⁻¹ • (extChartAt I y₀).symm w)) ∂μ) ∘ extChartAt I y₀ := by
  filter_upwards [extChartAt_source_mem_nhds (I := I) y₀] with y hy
  simp only [Function.comp_apply, (extChartAt I y₀).left_inv hy]

include IG in
/-- **Smoothness of the equivariant average.** Let a compact Lie group `G` act smoothly on a
manifold `M` without boundary, `σ` be a continuous representation of `G` on `F`, `μ` a finite
measure on `G`, and `φ : M → F` be `C^n` on an open set `U`. Then
`y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ` is `C^n` on the set of points whose orbit lies in `U`. -/
theorem ContMDiffOn.integral_apply_inv_smul (hσ : Continuous σ) (hU : IsOpen U)
    (hφ : ContMDiffOn I 𝓘(ℝ, F) n φ U) :
    ContMDiffOn I 𝓘(ℝ, F) n (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) {y | ∀ k : G, k • y ∈ U} := by
  intro y₀ hy₀
  have : ContinuousSMul G M :=
    ⟨(ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := n) (G := G) (M := M)).continuous⟩
  obtain ⟨hV, -, hA, -, -⟩ := integral_apply_inv_smul_extChartAt (IG := IG)
    (μ := μ) hσ hU hφ y₀
  have hmem : extChartAt I y₀ y₀ ∈
      (extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' {y | ∀ k : G, k • y ∈ U} :=
    ⟨mem_extChartAt_target y₀, by simpa [extChartAt_to_inv] using hy₀⟩
  refine (ContMDiffAt.congr_of_eventuallyEq ?_
    (integral_apply_inv_smul_eventuallyEq_extChartAt (I := I) y₀)).contMDiffWithinAt
  exact ((hA.contDiffAt (hV.mem_nhds hmem)).contMDiffAt).comp y₀ contMDiffAt_extChartAt

include IG in
/-- **The derivative of the equivariant average.** Under the hypotheses of
`ContMDiffOn.integral_apply_inv_smul`, with `1 ≤ n`, at a point `y` whose orbit lies in `U`, the
derivative of `y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ` is the integral over `k` of the derivatives
`σ k ∘ dφ_{k⁻¹ • y} ∘ d(k⁻¹ • ·)_y` of the integrands. -/
theorem ContMDiffOn.hasMFDerivAt_integral_apply_inv_smul (hσ : Continuous σ) (hU : IsOpen U)
    (hφ : ContMDiffOn I 𝓘(ℝ, F) n φ U) (hn : 1 ≤ n) {y : M} (hy : ∀ k : G, k • y ∈ U) :
    HasMFDerivAt I 𝓘(ℝ, F) (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) y
      ((∫ k, (σ k).comp ((mfderiv I 𝓘(ℝ, F) φ (k⁻¹ • y)).comp
        (mfderiv I I (fun z : M ↦ k⁻¹ • z) y)) ∂μ : E →L[ℝ] F)) := by
  have hsmul := ContMDiffSMul.contMDiff_smul (I := IG) (I' := I) (n := n) (G := G) (M := M)
  have : ContinuousSMul G M := ⟨hsmul.continuous⟩
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le hn').ne'
  have : IsManifold I 1 M := .of_le hn'
  obtain ⟨hV, hΦ, -, hDcont, hA⟩ := integral_apply_inv_smul_extChartAt
    (IG := IG) (μ := μ) hσ hU hφ y
  set χ := extChartAt I y
  have hmem : χ y ∈ χ.target ∩ χ.symm ⁻¹' {y | ∀ k : G, k • y ∈ U} :=
    ⟨mem_extChartAt_target y, by simpa [χ, extChartAt_to_inv] using hy⟩
  have hχ : HasMFDerivAt I 𝓘(ℝ, E) χ y (mfderiv I 𝓘(ℝ, E) χ y) :=
    (mdifferentiableAt_extChartAt (mem_chart_source H y)).hasMFDerivAt
  -- The derivative of each integrand, read in the chart, composed with the derivative of `χ`.
  let D : G → E →L[ℝ] F := fun k ↦ fderiv ℝ (fun w ↦ σ k (φ (k⁻¹ • χ.symm w))) (χ y)
  have hD (k : G) : (D k).comp (mfderiv I 𝓘(ℝ, E) χ y) =
      (σ k).comp ((mfderiv I 𝓘(ℝ, F) φ (k⁻¹ • y)).comp
        (mfderiv I I (fun z : M ↦ k⁻¹ • z) y)) := by
    have hdiff : HasFDerivAt (fun w ↦ σ k (φ (k⁻¹ • χ.symm w))) (D k) (χ y) :=
      (((hΦ k).differentiableOn hn0).differentiableAt (hV.mem_nhds hmem)).hasFDerivAt
    have h₁ : HasMFDerivAt I 𝓘(ℝ, F) (fun z ↦ σ k (φ (k⁻¹ • z))) y
        ((D k).comp (mfderiv I 𝓘(ℝ, E) χ y)) := by
      refine (hdiff.hasMFDerivAt.comp y hχ).congr_of_eventuallyEq ?_
      filter_upwards [extChartAt_source_mem_nhds (I := I) y] with z hz
      simp only [Function.comp_apply, χ.left_inv hz]
    have hφk : MDifferentiableAt I 𝓘(ℝ, F) φ (k⁻¹ • y) :=
      ((hφ.contMDiffAt (hU.mem_nhds (by simpa using hy k⁻¹))).mdifferentiableAt hn0)
    have hk : MDifferentiableAt I I (fun z : M ↦ k⁻¹ • z) y :=
      ((ContMDiffSMul.contMDiff_const_smul (I := IG) (n := n) k⁻¹) y).mdifferentiableAt hn0
    have h₂ : HasMFDerivAt I 𝓘(ℝ, F) (fun z ↦ σ k (φ (k⁻¹ • z))) y
        ((σ k).comp ((mfderiv I 𝓘(ℝ, F) φ (k⁻¹ • y)).comp
          (mfderiv I I (fun z : M ↦ k⁻¹ • z) y))) :=
      (σ k).hasFDerivAt.hasMFDerivAt.comp y (hφk.hasMFDerivAt.comp y hk.hasMFDerivAt)
    exact h₁.mfderiv.symm.trans h₂.mfderiv
  have hDint : Integrable D μ :=
    integrableOn_univ.1 <| ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ <|
      (hDcont hn).comp (continuousOn_const.prodMk continuousOn_id) fun k _ ↦ ⟨hmem, mem_univ k⟩
  have h := (HasMFDerivAt.comp y (hA hn _ hmem).hasMFDerivAt hχ)
    |>.congr_of_eventuallyEq_abuse (integral_apply_inv_smul_eventuallyEq_extChartAt (I := I) y)
  have heq : (∫ k, (σ k).comp ((mfderiv I 𝓘(ℝ, F) φ (k⁻¹ • y)).comp
      (mfderiv I I (fun z : M ↦ k⁻¹ • z) y)) ∂μ : E →L[ℝ] F) =
      (∫ k, D k ∂μ).comp (mfderiv I 𝓘(ℝ, E) χ y) := by
    by_cases hc : CompleteSpace (E →L[ℝ] F)
    · have h' : ∫ k, ((D k).comp (mfderiv I 𝓘(ℝ, E) χ y) : E →L[ℝ] F) ∂μ =
          (∫ k, D k ∂μ).comp (mfderiv I 𝓘(ℝ, E) χ y) :=
        ((ContinuousLinearMap.compL ℝ E E F).flip
          (mfderiv I 𝓘(ℝ, E) χ y)).integral_comp_comm hDint
      refine .trans (integral_congr_ae (μ := μ)
        (f := fun k ↦ ((σ k).comp ((mfderiv I 𝓘(ℝ, F) φ (k⁻¹ • y)).comp
          (mfderiv I I (fun z : M ↦ k⁻¹ • z) y)) : E →L[ℝ] F))
        (g := fun k ↦ ((D k).comp (mfderiv I 𝓘(ℝ, E) χ y) : E →L[ℝ] F))
        (.of_forall fun k ↦ (hD k).symm)) h'
    · rw [integral_of_not_completeSpace hc, integral_of_not_completeSpace hc]
      exact (ContinuousLinearMap.zero_comp _).symm
  rw [heq]
  exact h

include IG in
/-- **The equivariant average of a chart at a fixed point.** Let `x` be a fixed point of the
action, `σ` a continuous representation on the model space `E`, a Banach space, with `σ k` the
derivative of `k • ·` at `x`, `μ` a probability measure on `G`, and `φ : M → E` a `C^n` map,
`1 ≤ n`, on an open neighbourhood `U` of `x`, with derivative the identity at `x`. Then
`y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ` also has derivative the identity at `x`. -/
theorem ContMDiffOn.hasMFDerivAt_integral_apply_inv_smul_of_smul_eq [CompleteSpace E]
    [IsProbabilityMeasure μ]
    {σ : ContRepresentation ℝ G E} {φ : M → E} (hσ : Continuous σ) (hU : IsOpen U)
    (hφ : ContMDiffOn I 𝓘(ℝ, E) n φ U) (hn : 1 ≤ n) {x : M} (hx : ∀ k : G, k • x = x)
    (hxU : x ∈ U) (hσx : ∀ k : G, mfderiv I I (fun z : M ↦ k • z) x = σ k)
    (hφx : mfderiv I 𝓘(ℝ, E) φ x = ContinuousLinearMap.id ℝ E) :
    HasMFDerivAt I 𝓘(ℝ, E) (fun y ↦ ∫ k, σ k (φ (k⁻¹ • y)) ∂μ) x
      (ContinuousLinearMap.id ℝ E) := by
  have h := hφ.hasMFDerivAt_integral_apply_inv_smul (IG := IG) (μ := μ) hσ hU hn
    (y := x) fun k ↦ by rwa [hx]
  have hk (k : G) : ((σ k).comp ((mfderiv I 𝓘(ℝ, E) φ (k⁻¹ • x)).comp
      (mfderiv I I (fun z : M ↦ k⁻¹ • z) x)) : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    rw [hσx, hx, hφx]
    ext v
    exact DFunLike.congr_fun (σ.comp_inv_self k) v
  have hI : (∫ k, ((σ k).comp ((mfderiv I 𝓘(ℝ, E) φ (k⁻¹ • x)).comp
      (mfderiv I I (fun z : M ↦ k⁻¹ • z) x)) : E →L[ℝ] E) ∂μ) = ContinuousLinearMap.id ℝ E := by
    simp only [hk]
    exact (integral_const _).trans (by simp)
  rw [hI] at h
  exact h

end
