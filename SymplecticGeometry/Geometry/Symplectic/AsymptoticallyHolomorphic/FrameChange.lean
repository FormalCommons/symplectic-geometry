/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.Basic
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ChartTransition

/-!
# The change of frame between rescaled unitary charts

Let `D` be rescaled unitary charts, `k` a power, `x` and `y` two points, and
`τ = D.chartTransition k x y` the transition from the chart centred at `y` to the chart centred at
`x`. At the point `p = (D.chart k y)⁻¹ w`, the frames `D.frame k x p` and `D.frame k y p` of `P`
differ by an element of `Circle`, their division. Its `k`-th power, as a complex number, is the
**change of frame** `D.frameChange k x y w`. It compares the readings of a section `s` of
`PowerBundle P k` in the two charts: for `w` in the source of `τ`,
`D.reading k y s w = D.frameChange k x y w * D.reading k x s (τ w)`
(`SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`).

On the set `D.chartTransitionDomain k x y` of `ChartTransition.lean`, the points `w` of the ball
`B` of radius `ρ₀ * √k` in the source of `τ` with `τ w ∈ B`, both frames are smooth at
`(D.chart k y)⁻¹ w`, so the change of frame is smooth there
(`SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_frameChange`), by Tau Ceti's
`ContMDiffOn.division`. It has norm one everywhere.

## Main definitions

* `SymplecticGeometry.RescaledUnitaryCharts.frameChange`: the change of frame.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.norm_frameChange`: `‖D.frameChange k x y w‖ = 1`.
* `SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_frameChange`: the change of frame is smooth
  on `D.chartTransitionDomain k x y`.
* `SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`: the readings of a section
  in the two charts differ by the change of frame.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff
open TauCeti Metric Bundle MulOpposite

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-! ### The change of frame -/

/-- The **change of frame** between the chart centred at `y` and the chart centred at `x`, for the
power `k`: at `w`, the `k`-th power of the element of `Circle` that carries the frame
`D.frame k y` to the frame `D.frame k x` at the point `(D.chart k y)⁻¹ w`, as a complex number. -/
noncomputable def frameChange (k : ℕ) (x y : M) (w : StdSpace ι) : ℂ :=
  ((PrincipalBundle.division Circle (D.frame k y ((D.chart k y).symm w))
    (D.frame k x ((D.chart k y).symm w)) ^ k : Circle) : ℂ)

theorem frameChange_def (k : ℕ) (x y : M) (w : StdSpace ι) :
    D.frameChange k x y w = ((PrincipalBundle.division Circle (D.frame k y ((D.chart k y).symm w))
      (D.frame k x ((D.chart k y).symm w)) ^ k : Circle) : ℂ) :=
  (rfl)

/-- The change of frame has values in the unit circle. -/
@[simp]
theorem norm_frameChange (k : ℕ) (x y : M) (w : StdSpace ι) : ‖D.frameChange k x y w‖ = 1 := by
  rw [frameChange_def, Circle.norm_coe]

/-- The change of frame does not vanish. -/
theorem frameChange_ne_zero (k : ℕ) (x y : M) (w : StdSpace ι) : D.frameChange k x y w ≠ 0 := by
  rw [frameChange_def]
  exact Circle.coe_ne_zero _

variable [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]

attribute [local instance] finrank_real_complex_fact' in
/-- **The change of frame is smooth.** For `k ≥ k₀`, it is smooth on the set of points of the ball
of radius `ρ₀ * √k` that the transition from the chart centred at `y` to the chart centred at `x`
sends into that ball. -/
theorem contDiffOn_frameChange {k : ℕ} (hk : k₀ ≤ k) (x y : M) :
    ContDiffOn ℝ ∞ (D.frameChange k x y) (D.chartTransitionDomain k x y) := by
  set W := D.chartTransitionDomain k x y
  have hsymm : ContMDiffOn 𝓘(ℝ, StdSpace ι) I ∞ (D.chart k y).symm W :=
    (D.chart k y).symm.contMDiffOn.mono fun w hw ↦
      (D.mem_chartTransition_source_iff.1 (D.chartTransitionDomain_subset_source k x y hw)).1
  -- Both frames are smooth along `(D.chart k y)⁻¹` on `W`.
  have hy : ContMDiffOn 𝓘(ℝ, StdSpace ι) (I.prod (𝓡 1)) ∞ (fun w ↦
      ManifoldTotalSpace.homeomorph Circle P
        ⟨(D.chart k y).symm w, D.frame k y ((D.chart k y).symm w)⟩) W :=
    (D.contMDiffOn_frame hk y).comp hsymm fun w hw ↦
      Set.mem_image_of_mem _ (D.mem_chartTransitionDomain_iff.1 hw).1
  have hx : ContMDiffOn 𝓘(ℝ, StdSpace ι) (I.prod (𝓡 1)) ∞ (fun w ↦
      ManifoldTotalSpace.homeomorph Circle P
        ⟨(D.chart k y).symm w, D.frame k x ((D.chart k y).symm w)⟩) W :=
    (D.contMDiffOn_frame hk x).comp hsymm fun w hw ↦
      ⟨_, (D.mem_chartTransitionDomain_iff.1 hw).2.2,
        D.chart_symm_chartTransition (D.mem_chartTransitionDomain_iff.1 hw).2.1⟩
  have hg := ((hy.division hx).pow k)
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiff_coe_sphere.comp_contMDiffOn hg).congr fun w _ ↦ (frameChange_def ..).symm

/-- **The readings in two charts differ by the change of frame.** For `w` in the source of the
transition `τ` from the chart centred at `y` to the chart centred at `x`, the reading of a section
`s` of `PowerBundle P k` in the chart at `y` is, at `w`, the change of frame times its reading in
the chart at `x` at `τ w`. -/
theorem reading_eq_frameChange_mul {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (s : Π y, PowerBundle P k y) :
    D.reading k y s w = D.frameChange k x y w * D.reading k x s (D.chartTransition k x y w) := by
  have h := D.apply_chart_symm_eq_mk k x s (D.chartTransition k x y w)
  rw [D.chart_symm_chartTransition hw] at h
  rw [reading_def, h, AssociatedBundle.mkLinearIsometryEquiv_symm_apply_mk,
    PowerModel.toComplex_smul, frameChange_def, Circle.coe_pow, zpow_natCast,
    LinearIsometryEquiv.apply_symm_apply]

end RescaledUnitaryCharts

end SymplecticGeometry

end
