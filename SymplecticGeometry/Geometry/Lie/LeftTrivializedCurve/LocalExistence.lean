/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
import SymplecticGeometry.Analysis.ODE.TimeDependentUniformTime
import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Local curves with a prescribed left-trivialized derivative

Let `G` be a real Lie group of class `C²` modelled on a complete space with a boundaryless model,
and let `ξ : ℝ → 𝔤` be a continuous curve in its Lie algebra `𝔤 = GroupLieAlgebra I G`. This file
shows that the equation `d(L_{g⁻¹}) g' = ξ`, i.e. `g' = d(L_g)_1 (ξ t)`, has local solutions
through the identity, defined on intervals of one length around every initial time of a compact
interval.

In the extended chart at `1`, the equation reads `y' = W y (ξ t)`, where `W y` is the derivative
at the chart image of `1` of left translation by the point with coordinate `y`, read in the
chart. Since multiplication is `C²`, `W` is `C¹` near that point, so
`ContDiffAt.exists_pos_forall_mem_Icc_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem` gives solutions
in the chart on a uniform time interval; they are read back on `G` through the inverse chart, as in
Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt`. Tau Ceti's
`exists_isMIntegralCurve_mulInvariantVectorField` treats the autonomous case, where `ξ` is
constant.

## Main results

* `SymplecticGeometry.exists_pos_forall_mem_Icc_exists_hasMFDerivAt_mfderiv_inv_mul_eq`: for a
  continuous `ξ` and a compact interval `[a, b]` there is `ε > 0` such that for every
  `t₀ ∈ [a, b]` some curve `γ` with `γ t₀ = 1` has, at every `t ∈ (t₀ - ε, t₀ + ε)`, a manifold
  derivative `v` with `d(L_{(γ t)⁻¹}) v = ξ t`.
-/

public section

noncomputable section

open Function Manifold Set
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (I G) in
/-- Multiplication of `G`, read in the extended chart at `1`: `chartMulLeft I G y z` is the
coordinate of the product of the points with coordinates `y` and `z`. -/
private def chartMulLeft (y z : E) : E :=
  extChartAt I (1 : G) ((extChartAt I (1 : G)).symm y * (extChartAt I (1 : G)).symm z)

variable (I G) in
/-- `chartMulLeft I G y` is left translation by the point with coordinate `y`, read in the chart. -/
private theorem chartMulLeft_eq (y : E) :
    chartMulLeft I G y = extChartAt I (1 : G) ∘ ((extChartAt I (1 : G)).symm y * ·) ∘
      (extChartAt I (1 : G)).symm :=
  rfl

/-- Multiplication read in the chart at `1` is `C²` near the chart image of `(1, 1)`. -/
private theorem contDiffAt_uncurry_chartMulLeft [LieGroup I (2 : ℕ∞ω) G] [I.Boundaryless] :
    ContDiffAt ℝ 2 (uncurry (chartMulLeft I G))
      (extChartAt I (1 : G) 1, extChartAt I (1 : G) 1) := by
  set c := extChartAt I (1 : G) 1
  rw [← contMDiffAt_iff_contDiffAt]
  have hψ : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I (1 : G)).symm c := by
    have := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) (1 : G)
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at this
  have hmul : ContMDiffAt 𝓘(ℝ, E × E) I 2
      (fun p : E × E ↦ (extChartAt I (1 : G)).symm p.1 * (extChartAt I (1 : G)).symm p.2)
      (c, c) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (hψ.comp (c, c) contMDiffAt_fst).mul (hψ.comp (c, c) contMDiffAt_snd)
  have hφ : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (1 : G))
      ((extChartAt I (1 : G)).symm c * (extChartAt I (1 : G)).symm c) := by
    rw [extChartAt_to_inv, mul_one]
    exact contMDiffAt_extChartAt
  exact hφ.comp (c, c) hmul

/-- At a point `y` of the chart target, the inverse chart carries the derivative of
`chartMulLeft I G y` at the chart image of `1` to the derivative at `1` of left translation by the
point with coordinate `y`. -/
private theorem mfderiv_extChartAt_symm_fderiv_chartMulLeft [LieGroup I (2 : ℕ∞ω) G]
    [I.Boundaryless] {y : E} (hy : y ∈ (extChartAt I (1 : G)).target) (v : E) :
    mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm y
        (fderiv ℝ (chartMulLeft I G y) (extChartAt I (1 : G) 1) v) =
      mfderiv I I ((extChartAt I (1 : G)).symm y * ·) 1 v := by
  have : IsManifold I 1 G := IsManifold.of_le (n := 2) (by norm_num)
  have : ContMDiffMul I 1 G := ContMDiffMul.of_le (n := 2) (by norm_num)
  set c := extChartAt I (1 : G) 1
  set g := (extChartAt I (1 : G)).symm y
  have hmul : HasMFDerivAt I I (g * ·) ((extChartAt I (1 : G)).symm c)
      (mfderiv I I (g * ·) 1) := by
    rw [extChartAt_to_inv]
    exact mdifferentiableAt_mul_left.hasMFDerivAt
  have hL := (hmul.comp c (TauCeti.hasMFDerivAt_extChartAt_symm_self (1 : G))).congr_mfderiv
    (ContinuousLinearMap.comp_id _)
  have hz : ((g * ·) ∘ (extChartAt I (1 : G)).symm) c ∈ (extChartAt I (1 : G)).source := by
    rw [comp_apply, extChartAt_to_inv, mul_one]
    exact (extChartAt I (1 : G)).map_target hy
  rw [chartMulLeft_eq, ContinuousAt.fderiv_extChartAt_comp_apply hL.continuousAt hz, hL.mfderiv,
    comp_apply, extChartAt_to_inv, mul_one]
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy
  rw [I.range_eq_univ, mfderivWithin_univ] at h
  -- the two sides agree once the compositions of continuous linear maps are applied
  exact congr($h (mfderiv I I (g * ·) 1 v))

/-- Let `G` be a real Lie group of class `C²` (or more) modelled on a complete space with a
boundaryless model, and let `ξ : ℝ → 𝔤` be continuous. For every compact interval `[a, b]` there
is `ε > 0` such that, for every `t₀ ∈ [a, b]`, some curve `γ : ℝ → G` with `γ t₀ = 1` has at
every `t ∈ (t₀ - ε, t₀ + ε)` a manifold derivative `v` whose left translate back to the
identity, `d(L_{(γ t)⁻¹})_{γ t} v`, is `ξ t`. -/
theorem exists_pos_forall_mem_Icc_exists_hasMFDerivAt_mfderiv_inv_mul_eq [CompleteSpace E]
    [I.Boundaryless] {n : ℕ∞ω} [LieGroup I n G] (hn : 2 ≤ n) {ξ : ℝ → GroupLieAlgebra I G}
    (hξ : Continuous ξ) (a b : ℝ) :
    ∃ ε > 0, ∀ t₀ ∈ Icc a b, ∃ γ : ℝ → G, γ t₀ = 1 ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      ∃ v : TangentSpace I (γ t),
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
          mfderiv I I ((γ t)⁻¹ * ·) (γ t) v = ξ t := by
  have : LieGroup I 2 G := LieGroup.of_le hn
  have hξE : Continuous fun t ↦ (ξ t : E) := hξ
  have hW : ContDiffAt ℝ 1 (fun y ↦ fderiv ℝ (chartMulLeft I G y) (extChartAt I (1 : G) 1))
      (extChartAt I (1 : G) 1) :=
    contDiffAt_uncurry_chartMulLeft.fderiv contDiffAt_const (by norm_num)
  obtain ⟨ε, hε, hsol⟩ := hW.exists_pos_forall_mem_Icc_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem
    hξE a b (extChartAt_target_mem_nhds (I := I) (1 : G))
  refine ⟨ε, hε, fun t₀ ht₀ ↦ ?_⟩
  obtain ⟨y, hy₀, hy⟩ := hsol t₀ ht₀
  refine ⟨fun t ↦ (extChartAt I (1 : G)).symm (y t), by simp only [hy₀, extChartAt_to_inv],
    fun t ht ↦ ?_⟩
  obtain ⟨hy', hyt⟩ := hy t ht
  refine ⟨mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (y t)
    (fderiv ℝ (chartMulLeft I G (y t)) (extChartAt I (1 : G) 1) (ξ t)), ?_, ?_⟩
  · have h := TauCeti.Manifold.hasMFDerivWithinAt_extChartAt_symm_comp (J := univ) hyt
      (by simp [I.range_eq_univ]) hy'.hasDerivWithinAt
    rw [I.range_eq_univ, mfderivWithin_univ] at h
    exact hasMFDerivWithinAt_univ.mp h
  · have h := congrArg (mfderiv I I (((extChartAt I (1 : G)).symm (y t))⁻¹ * ·)
      ((extChartAt I (1 : G)).symm (y t)))
      (mfderiv_extChartAt_symm_fderiv_chartMulLeft hyt (ξ t))
    rw [← GroupLieAlgebra.mulInvariantVectorField_apply,
      TauCeti.mfderiv_inv_mul_mulInvariantVectorField] at h
    exact h

end SymplecticGeometry

end
