/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Differentials of maps into normed spaces, read in a chart

For a map `f : M → F` into a normed space and a point `y` of the source of the extended chart at
`x`, which need not be centred at `y`, the differential `mvfderiv I f y` is the Fréchet derivative
of the coordinate expression `f ∘ (extChartAt I x).symm` at the chart image of `y`, after the
differential of the chart. These are the `mvfderiv` and off-centre forms of Tau Ceti's
`TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt` and
`TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`.

## Main results

* `mvfderiv_eq_fderiv_comp_mfderiv_extChartAt`: `mvfderiv I f y` in the chart at `x`.
* `range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source`: the range of
  `mvfderiv I f y` is that of the coordinate derivative at the chart image of `y`.
* `ContMDiff.contDiffOn_comp_extChartAt_symm`: a `C^n` map into a normed space is `C^n` in every
  chart.
-/

public section

open Set Function
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x y : M}

/-- At a point `y` of the source of the extended chart at `x`, the differential of a map into a
normed space is the Fréchet derivative of its coordinate expression `f ∘ (extChartAt I x).symm`
at the chart image of `y`, composed with the differential of the chart, provided the coordinate
expression is differentiable there. -/
theorem mvfderiv_eq_fderiv_comp_mfderiv_extChartAt [IsManifold I 1 M]
    (hy : y ∈ (extChartAt I x).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    mvfderiv I f y = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).comp
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) := by
  ext v
  rw [mvfderiv_apply_eq_mfderiv_apply, TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hf]
  -- The two sides differ only in their codomain, `TangentSpace 𝓘(𝕜, F) (f y)` or `F`.
  rfl

/-- At a point `y` of the source of the extended chart at `x`, the range of the differential of a
map into a normed space is the range of the Fréchet derivative of its coordinate expression at the
chart image of `y`, provided the coordinate expression is differentiable there. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source [IsManifold I 1 M]
    (hy : y ∈ (extChartAt I x).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    (mvfderiv I f y).range = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).range := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mvfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hf, ← hL]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr L.surjective)

/-- A `C^n` map into a normed space is `C^n` in every chart: its coordinate expression
`f ∘ (extChartAt I x).symm` is `C^n` on the target of the extended chart. -/
theorem ContMDiff.contDiffOn_comp_extChartAt_symm {n : WithTop ℕ∞} [IsManifold I n M]
    (hf : ContMDiff I 𝓘(𝕜, F) n f) (x : M) :
    ContDiffOn 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
  contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))

end
