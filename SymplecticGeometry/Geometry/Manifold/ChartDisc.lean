/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Small discs through a point in a chart

Fix a point `b` of a manifold `M` modelled on `E`, and vectors `w₁ w₂ : E`. For `r : ℝ`, the map
`chartDisc I b w₁ w₂ r : ℝ × ℝ → M` reads, in the extended chart at `b`, as

`(s, t) ↦ extChartAt I b b + (r sin (πs/2)) • ((cos (2πt) - 1) • w₁ + sin (2πt) • w₂)`

(`chartDiscCoord`), followed by the inverse of that chart. For fixed `s`, its loop in `t` runs
around an ellipse through `b`, in the plane of `w₁` and `w₂`, scaled by `r sin (πs/2)`. At `s = 0`
and along the seam `t = 0` it is the point `b`.

All values of `chartDiscCoord` lie within `|r| (2‖w₁‖ + ‖w₂‖)` of the chart point of `b`. So, on a
manifold without boundary, for `|r|` small the map stays inside any given neighbourhood of `b` and
inside the chart, and it is then a smooth disc of Tau Ceti (`TauCeti.IsSmoothDisc`) with centre
`b` (`exists_pos_forall_isSmoothDisc_chartDisc`). Its derivatives in `s` and in `t` are the images,
under the derivative of the inverse chart, of the derivatives of `chartDiscCoord`
(`mfderiv_chartDisc_apply_fst`, `mfderiv_chartDisc_apply_snd`). An alternating bilinear map on
the tangent space takes on these two derivatives an explicit multiple of its value on the images
of `w₁` and `w₂` (`LinearMap.IsAlt.apply_mfderiv_chartDisc_fst_snd`).

The discs serve the converse direction of [McDuffSalamon2017], Exercise 6.4.9 (see
[McDuffSalamon2019Errata]), which reads the curvature of a connection off its holonomy.

## Main definitions

* `SymplecticGeometry.chartDiscCoord`: the disc read in the chart at `b`.
* `SymplecticGeometry.chartDisc`: the disc in `M`.

## Main results

* `SymplecticGeometry.exists_pos_forall_isSmoothDisc_chartDisc`: for every neighbourhood `U` of
  `b`, the discs of small radius lie in `U` and in the chart at `b`, and are smooth discs with
  centre `b`.
* `SymplecticGeometry.mfderiv_chartDisc_apply_fst` and
  `SymplecticGeometry.mfderiv_chartDisc_apply_snd`: the derivatives of the disc in `s` and in `t`.
* `LinearMap.IsAlt.apply_mfderiv_chartDisc_fst_snd`: an alternating bilinear map on the two
  derivatives of the disc.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Exercise 6.4.9 and Proposition 10.2.12.
* [D. McDuff and D. Salamon, *Errata*][McDuffSalamon2019Errata]
* [V. Guillemin, E. Lerman, S. Sternberg, *Symplectic Fibrations and Multiplicity
  Diagrams*][GuilleminLermanSternberg1996], §1.4.
-/

public section

noncomputable section

open Real Set Filter
open scoped Manifold ContDiff Topology

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- The disc through `b` of radius `r` in the plane of `w₁` and `w₂`, read in the extended chart
at `b`: `(s, t) ↦ extChartAt I b b + (r sin (πs/2)) • ((cos (2πt) - 1) • w₁ + sin (2πt) • w₂)`. -/
def chartDiscCoord (b : M) (w₁ w₂ : E) (r : ℝ) (z : ℝ × ℝ) : E :=
  extChartAt I b b + (r * sin (π * z.1 / 2)) •
    ((cos (2 * π * z.2) - 1) • w₁ + sin (2 * π * z.2) • w₂)

theorem chartDiscCoord_def (b : M) (w₁ w₂ : E) (r : ℝ) (z : ℝ × ℝ) :
    chartDiscCoord I b w₁ w₂ r z = extChartAt I b b + (r * sin (π * z.1 / 2)) •
      ((cos (2 * π * z.2) - 1) • w₁ + sin (2 * π * z.2) • w₂) :=
  (rfl)

/-- The disc through `b` of radius `r` in the plane of `w₁` and `w₂`: the inverse of the extended
chart at `b` applied to `chartDiscCoord I b w₁ w₂ r`. -/
def chartDisc (b : M) (w₁ w₂ : E) (r : ℝ) (z : ℝ × ℝ) : M :=
  (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r z)

theorem chartDisc_def (b : M) (w₁ w₂ : E) (r : ℝ) (z : ℝ × ℝ) :
    chartDisc I b w₁ w₂ r z = (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r z) :=
  (rfl)

variable {I} {b : M} {w₁ w₂ : E} {r : ℝ}

/-- The disc in the chart is `1`-periodic in its second coordinate. -/
theorem chartDiscCoord_add_one (z : ℝ × ℝ) :
    chartDiscCoord I b w₁ w₂ r (z.1, z.2 + 1) = chartDiscCoord I b w₁ w₂ r z := by
  simp only [chartDiscCoord_def, mul_add, mul_one, cos_add_two_pi, sin_add_two_pi]

/-- The disc in the chart is the chart point of `b` along `s = 0`. -/
@[simp]
theorem chartDiscCoord_zero_left (t : ℝ) :
    chartDiscCoord I b w₁ w₂ r (0, t) = extChartAt I b b := by
  simp [chartDiscCoord_def]

/-- The disc in the chart is the chart point of `b` along the seam `t = 0`. -/
@[simp]
theorem chartDiscCoord_zero_right (s : ℝ) :
    chartDiscCoord I b w₁ w₂ r (s, 0) = extChartAt I b b := by
  simp [chartDiscCoord_def]

/-- The disc in the chart lies within `|r| (2‖w₁‖ + ‖w₂‖)` of the chart point of `b`. -/
theorem norm_chartDiscCoord_sub_le (z : ℝ × ℝ) :
    ‖chartDiscCoord I b w₁ w₂ r z - extChartAt I b b‖ ≤ |r| * (2 * ‖w₁‖ + ‖w₂‖) := by
  rw [chartDiscCoord_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul]
  have hs : |sin (π * z.1 / 2)| ≤ 1 := abs_sin_le_one _
  have hu : ‖(cos (2 * π * z.2) - 1) • w₁ + sin (2 * π * z.2) • w₂‖ ≤ 2 * ‖w₁‖ + ‖w₂‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := abs_cos_le_one (2 * π * z.2)
      rw [abs_le] at this ⊢
      constructor <;> linarith
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
  calc |r| * |sin (π * z.1 / 2)| * ‖(cos (2 * π * z.2) - 1) • w₁ + sin (2 * π * z.2) • w₂‖
      ≤ |r| * 1 * (2 * ‖w₁‖ + ‖w₂‖) := by gcongr
    _ = |r| * (2 * ‖w₁‖ + ‖w₂‖) := by rw [mul_one]

/-- The disc in the chart is smooth. -/
theorem contDiff_chartDiscCoord : ContDiff ℝ ∞ (chartDiscCoord I b w₁ w₂ r) := by
  unfold chartDiscCoord
  fun_prop

/-- **Small discs stay near `b`.** For every neighbourhood `U` of `b` on a manifold without
boundary, there is `ε > 0` such that, for `|r| < ε`, all values of the disc in the chart lie in
the target of the extended chart at `b`, and all values of the disc lie in `U`. -/
theorem exists_pos_forall_chartDiscCoord_mem [I.Boundaryless] (b : M) (w₁ w₂ : E) {U : Set M}
    (hU : U ∈ 𝓝 b) :
    ∃ ε > 0, ∀ r : ℝ, |r| < ε → ∀ z : ℝ × ℝ,
      chartDiscCoord I b w₁ w₂ r z ∈ (extChartAt I b).target ∧ chartDisc I b w₁ w₂ r z ∈ U := by
  have hV : (extChartAt I b).target ∩ (extChartAt I b).symm ⁻¹' U ∈ 𝓝 (extChartAt I b b) :=
    inter_mem (extChartAt_target_mem_nhds b)
      (continuousAt_extChartAt_symm b (by rwa [extChartAt_to_inv]))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  set C := 2 * ‖w₁‖ + ‖w₂‖
  have hC : 0 < C + 1 := by positivity
  refine ⟨δ / (C + 1), div_pos hδ hC, fun r hr z ↦ hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖chartDiscCoord I b w₁ w₂ r z - extChartAt I b b‖ ≤ |r| * C :=
        norm_chartDiscCoord_sub_le z
    _ ≤ |r| * (C + 1) := by gcongr; linarith
    _ < δ / (C + 1) * (C + 1) := by gcongr
    _ = δ := div_mul_cancel₀ δ hC.ne'

/-- Where the disc in the chart lies in the target of the chart, the chart at `b` sends the disc
to it. -/
theorem extChartAt_chartDisc {z : ℝ × ℝ}
    (hz : chartDiscCoord I b w₁ w₂ r z ∈ (extChartAt I b).target) :
    extChartAt I b (chartDisc I b w₁ w₂ r z) = chartDiscCoord I b w₁ w₂ r z := by
  rw [chartDisc_def, (extChartAt I b).right_inv hz]

/-- The disc is `b` along `s = 0`. -/
@[simp]
theorem chartDisc_zero_left (t : ℝ) : chartDisc I b w₁ w₂ r (0, t) = b := by
  rw [chartDisc_def, chartDiscCoord_zero_left, extChartAt_to_inv]

/-- The disc is `b` along the seam `t = 0`. -/
@[simp]
theorem chartDisc_zero_right (s : ℝ) : chartDisc I b w₁ w₂ r (s, 0) = b := by
  rw [chartDisc_def, chartDiscCoord_zero_right, extChartAt_to_inv]

/-- The disc is `1`-periodic in its second coordinate. -/
theorem chartDisc_add_one (z : ℝ × ℝ) :
    chartDisc I b w₁ w₂ r (z.1, z.2 + 1) = chartDisc I b w₁ w₂ r z := by
  rw [chartDisc_def, chartDiscCoord_add_one, chartDisc_def]

/-- The derivative in `s` of the disc in the chart. -/
theorem hasDerivAt_chartDiscCoord_fst (s t : ℝ) :
    HasDerivAt (fun s' ↦ chartDiscCoord I b w₁ w₂ r (s', t))
      ((r * (π / 2 * cos (π * s / 2))) •
        ((cos (2 * π * t) - 1) • w₁ + sin (2 * π * t) • w₂)) s := by
  have h : HasDerivAt (fun s' : ℝ ↦ r * sin (π * s' / 2)) (r * (cos (π * s / 2) * (π / 2))) s :=
    ((hasDerivAt_sin _).comp s ((hasDerivAt_id s).const_mul π |>.div_const 2)
      |>.congr_deriv (by simp)).const_mul r
  simp only [chartDiscCoord_def]
  exact ((h.smul_const ((cos (2 * π * t) - 1) • w₁ + sin (2 * π * t) • w₂)).const_add
    (extChartAt I b b)).congr_deriv (by module)

/-- The derivative in `t` of the disc in the chart. -/
theorem hasDerivAt_chartDiscCoord_snd (s t : ℝ) :
    HasDerivAt (fun t' ↦ chartDiscCoord I b w₁ w₂ r (s, t'))
      ((2 * π * r * sin (π * s / 2)) • (-sin (2 * π * t) • w₁ + cos (2 * π * t) • w₂)) t := by
  have hl : HasDerivAt (fun t' : ℝ ↦ 2 * π * t') (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hc := ((hasDerivAt_cos _).comp t hl).sub_const 1
  have hs := (hasDerivAt_sin _).comp t hl
  simp only [chartDiscCoord_def]
  exact (((hc.smul_const w₁).add (hs.smul_const w₂)).const_smul (r * sin (π * s / 2))
    |>.const_add (extChartAt I b b)).congr_deriv (by module)

/-- The derivative of the disc in the chart sends `(1, 0)` to its derivative in `s`. -/
theorem fderiv_chartDiscCoord_apply_fst (s t : ℝ) :
    fderiv ℝ (chartDiscCoord I b w₁ w₂ r) (s, t) (1, 0) =
      (r * (π / 2 * cos (π * s / 2))) • ((cos (2 * π * t) - 1) • w₁ + sin (2 * π * t) • w₂) :=
  have hf : HasFDerivAt (chartDiscCoord I b w₁ w₂ r)
      (fderiv ℝ (chartDiscCoord I b w₁ w₂ r) (s, t)) (s, t) :=
    (contDiff_chartDiscCoord.differentiable (by simp) _).hasFDerivAt
  (hf.comp_hasDerivAt (f := fun s' ↦ (s', t)) s
    ((hasDerivAt_id' s).prodMk (hasDerivAt_const s t))).unique
    (hasDerivAt_chartDiscCoord_fst s t)

/-- The derivative of the disc in the chart sends `(0, 1)` to its derivative in `t`. -/
theorem fderiv_chartDiscCoord_apply_snd (s t : ℝ) :
    fderiv ℝ (chartDiscCoord I b w₁ w₂ r) (s, t) (0, 1) =
      (2 * π * r * sin (π * s / 2)) • (-sin (2 * π * t) • w₁ + cos (2 * π * t) • w₂) :=
  have hf : HasFDerivAt (chartDiscCoord I b w₁ w₂ r)
      (fderiv ℝ (chartDiscCoord I b w₁ w₂ r) (s, t)) (s, t) :=
    (contDiff_chartDiscCoord.differentiable (by simp) _).hasFDerivAt
  (hf.comp_hasDerivAt (f := fun t' ↦ (s, t')) t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id' t))).unique
    (hasDerivAt_chartDiscCoord_snd s t)

variable [IsManifold I ∞ M]

/-- Where the disc in the chart lies in the target of the chart, the disc is smooth. -/
theorem contMDiff_chartDisc [I.Boundaryless]
    (h : ∀ z, chartDiscCoord I b w₁ w₂ r z ∈ (extChartAt I b).target) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (chartDisc I b w₁ w₂ r) := fun z ↦
  ((contMDiffOn_extChartAt_symm b).contMDiffAt
    ((isOpen_extChartAt_target b).mem_nhds (h z))).comp z
    contDiff_chartDiscCoord.contMDiff.contMDiffAt

/-- **The disc is a smooth disc.** Where the disc in the chart lies in the target of the chart,
the disc is a smooth disc of Tau Ceti with centre `b`, bounding its loop at `s = 1`. -/
theorem exists_isSmoothDisc_chartDisc [I.Boundaryless]
    (h : ∀ z, chartDiscCoord I b w₁ w₂ r z ∈ (extChartAt I b).target) :
    ∃ γ : Path b b, (∀ t : unitInterval, γ t = chartDisc I b w₁ w₂ r (1, t)) ∧
      TauCeti.IsSmoothDisc I γ (chartDisc I b w₁ w₂ r) := by
  have hD := contMDiff_chartDisc h
  let γ : Path b b :=
    { toFun := fun t ↦ chartDisc I b w₁ w₂ r (1, t)
      continuous_toFun := hD.continuous.comp (by fun_prop)
      source' := by simp
      target' := by
        simpa using (chartDisc_add_one (I := I) (w₁ := w₁) (w₂ := w₂) (r := r) (b := b)
          (1, 0)).trans (chartDisc_zero_right 1) }
  exact ⟨γ, fun _ ↦ rfl, hD, fun z ↦ chartDisc_add_one z, fun t ↦ chartDisc_zero_left _,
    fun _ ↦ rfl, fun s ↦ chartDisc_zero_right _⟩

/-- **Small discs through `b` in a chart.** For every neighbourhood `U` of `b` on a manifold
without boundary, there is `ε > 0` such that, for `|r| < ε`, the disc `chartDisc I b w₁ w₂ r`
takes its values in `U` and in the source of the chart at `b`, and is a smooth disc of Tau Ceti
with centre `b`, bounding its loop at `s = 1`. -/
theorem exists_pos_forall_isSmoothDisc_chartDisc [I.Boundaryless] (b : M) (w₁ w₂ : E)
    {U : Set M} (hU : U ∈ 𝓝 b) :
    ∃ ε > 0, ∀ r : ℝ, |r| < ε →
      (∀ z, chartDisc I b w₁ w₂ r z ∈ U ∩ (chartAt H b).source) ∧
      ∃ γ : Path b b, (∀ t : unitInterval, γ t = chartDisc I b w₁ w₂ r (1, t)) ∧
        TauCeti.IsSmoothDisc I γ (chartDisc I b w₁ w₂ r) := by
  obtain ⟨ε, hε, h⟩ := exists_pos_forall_chartDiscCoord_mem (I := I) b w₁ w₂ hU
  refine ⟨ε, hε, fun r hr ↦ ⟨fun z ↦ ⟨(h r hr z).2, ?_⟩,
    exists_isSmoothDisc_chartDisc fun z ↦ (h r hr z).1⟩⟩
  rw [← extChartAt_source (I := I)]
  exact (extChartAt I b).map_target (h r hr z).1

/-- Where the disc in the chart lies in the target of the chart, the derivative of the disc is
the derivative of the disc in the chart followed by that of the inverse chart. -/
theorem mfderiv_chartDisc_apply [I.Boundaryless] {z : ℝ × ℝ}
    (hz : chartDiscCoord I b w₁ w₂ r z ∈ (extChartAt I b).target) (v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (chartDisc I b w₁ w₂ r) z v =
      mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r z)
        (fderiv ℝ (chartDiscCoord I b w₁ w₂ r) z v) := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r z) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) b).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hz)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (chartDiscCoord I b w₁ w₂ r) z :=
    (contDiff_chartDiscCoord.differentiable (by simp) z).mdifferentiableAt
  have h : chartDisc I b w₁ w₂ r = (extChartAt I b).symm ∘ chartDiscCoord I b w₁ w₂ r :=
    funext (chartDisc_def I b w₁ w₂ r)
  rw [h, mfderiv_comp z hsymm hc, mfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace` is the identity of `ℝ × ℝ` and of `E` by definition.
  rfl

/-- **The derivative in `s` of the disc.** Where the disc in the chart lies in the target of
the chart, the derivative of the disc sends `(1, 0)` to the image, under the derivative of the
inverse chart, of `r φ'(s) u(t)`, for `φ s = sin (πs/2)` and
`u t = (cos (2πt) - 1) • w₁ + sin (2πt) • w₂`. -/
theorem mfderiv_chartDisc_apply_fst [I.Boundaryless] {s t : ℝ}
    (hz : chartDiscCoord I b w₁ w₂ r (s, t) ∈ (extChartAt I b).target) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (chartDisc I b w₁ w₂ r) (s, t) (1, 0) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r (s, t))
        ((r * (π / 2 * cos (π * s / 2))) •
          ((cos (2 * π * t) - 1) • w₁ + sin (2 * π * t) • w₂)) := by
  rw [mfderiv_chartDisc_apply hz, fderiv_chartDiscCoord_apply_fst]

/-- **The derivative in `t` of the disc.** Where the disc in the chart lies in the target of
the chart, the derivative of the disc sends `(0, 1)` to the image, under the derivative of the
inverse chart, of `2π r φ(s) u'(t)`, for `φ s = sin (πs/2)` and
`u' t = -sin (2πt) • w₁ + cos (2πt) • w₂`. -/
theorem mfderiv_chartDisc_apply_snd [I.Boundaryless] {s t : ℝ}
    (hz : chartDiscCoord I b w₁ w₂ r (s, t) ∈ (extChartAt I b).target) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (chartDisc I b w₁ w₂ r) (s, t) (0, 1) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r (s, t))
        ((2 * π * r * sin (π * s / 2)) •
          (-sin (2 * π * t) • w₁ + cos (2 * π * t) • w₂)) := by
  rw [mfderiv_chartDisc_apply hz, fderiv_chartDiscCoord_apply_snd]

end SymplecticGeometry

namespace LinearMap.IsAlt

open SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] {F : Type*} [AddCommGroup F] [Module ℝ F] {b : M} {w₁ w₂ : E} {r s t : ℝ}

/-- **An alternating bilinear map on the derivatives of a small disc in a chart.** Let `Ω` be an
alternating bilinear map on the tangent space at `D_r (s, t)`, for `D_r = chartDisc I b w₁ w₂ r`
with `D_r (s, t)` read in the target of the chart at `b`. With `W₁` and `W₂` the images of `w₁`
and `w₂` under the derivative of the inverse chart there,
`Ω(∂ₛD_r, ∂ₜD_r) = 2π r² φ(s) φ'(s) (1 - cos (2πt)) • Ω(W₁, W₂)`, for the profile
`φ s = sin (πs/2)`. -/
theorem apply_mfderiv_chartDisc_fst_snd
    {Ω : TangentSpace I (chartDisc I b w₁ w₂ r (s, t)) →ₗ[ℝ]
      TangentSpace I (chartDisc I b w₁ w₂ r (s, t)) →ₗ[ℝ] F} (hΩ : Ω.IsAlt)
    (hz : chartDiscCoord I b w₁ w₂ r (s, t) ∈ (extChartAt I b).target) :
    Ω (mfderiv 𝓘(ℝ, ℝ × ℝ) I (chartDisc I b w₁ w₂ r) (s, t) (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (chartDisc I b w₁ w₂ r) (s, t) (0, 1)) =
      (2 * π * r ^ 2 * (sin (π * s / 2) * (π / 2 * cos (π * s / 2))) *
          (1 - cos (2 * π * t))) •
        Ω (mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r (s, t)) w₁)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r (s, t)) w₂) := by
  set L := mfderiv 𝓘(ℝ, E) I (extChartAt I b).symm (chartDiscCoord I b w₁ w₂ r (s, t))
  -- The images under `L` of the derivatives of the disc in the chart, as combinations of
  -- `L w₁` and `L w₂`.
  have hL (α c d : ℝ) : L (α • (c • w₁ + d • w₂)) = (α * c) • L w₁ + (α * d) • L w₂ := by
    have h := (L.map_smul α (c • w₁ + d • w₂)).trans (congrArg (α • ·)
      ((L.map_add (c • w₁) (d • w₂)).trans (congrArg₂ (· + ·) (L.map_smul c w₁)
        (L.map_smul d w₂))))
    rwa [smul_add, smul_smul, smul_smul] at h
  rw [mfderiv_chartDisc_apply_fst hz, mfderiv_chartDisc_apply_snd hz, hL, hL]
  refine (hΩ.apply_smul_add_smul _ _ _ _ _ _).trans ?_
  congr 1
  linear_combination (2 * π * r ^ 2 * (sin (π * s / 2) * (π / 2 * cos (π * s / 2)))) *
    sin_sq_add_cos_sq (2 * π * t)

end LinearMap.IsAlt
