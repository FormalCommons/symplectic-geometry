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
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Differentials read in a chart

This file reads differentials in an extended chart, in both directions: for maps from a manifold
into a normed space, and for maps from a normed space into a manifold through the inverse chart.

For a map `f : M → F` into a normed space and a point `y` of the source of the extended chart at
`x`, which need not be centred at `y`, the range of `mvfderiv I f y` is the range of the Fréchet
derivative of the coordinate expression `f ∘ (extChartAt I x).symm` at the chart image of `y`.
This is the off-centre form of Tau Ceti's
`TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`, and its proof reads `mvfderiv I f y`
in the chart by Tau Ceti's `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt`.

For a map `h` from a normed space into the target of the extended chart at `x`, the differential
of `(extChartAt I x).symm ∘ h` is the derivative of `h` followed by the differential of the
inverse chart, which is invertible by Tau Ceti's `TauCeti.isInvertible_mfderiv_extChartAt_symm`;
so it is injective where the derivative of `h` is.

## Main results

* `SymplecticGeometry.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source`: the
  range of `mvfderiv I f y` is that of the coordinate derivative at the chart image of `y`.
* `ContMDiff.contDiffOn_comp_extChartAt_symm`: a `C^n` map into a normed space is `C^n` in every
  chart.
* `ContMDiffOn.contDiffOn_extChartAt_comp`: a map from a normed space into a manifold, `C^n` on a
  set, is `C^n` in every chart where its reading is defined.
* `writtenInExtChartAt_model_space_left`: the reading of a map from a normed space in extended
  charts.
* `SymplecticGeometry.injective_mfderiv_extChartAt_symm_comp`: a map into the chart target with
  injective derivative, composed with the inverse chart, has injective differential.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x y : M}

namespace SymplecticGeometry

/-- At a point `y` of the source of the extended chart at `x`, the range of the differential of a
map into a normed space is the range of the Fréchet derivative of its coordinate expression at the
chart image of `y`, provided the coordinate expression is differentiable there. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source [IsManifold I 1 M]
    (hy : y ∈ (extChartAt I x).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    (mvfderiv I f y).range = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).range := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  -- `show` reads Tau Ceti's `mfderiv` equation, whose codomain is the tangent space
  -- `TangentSpace 𝓘(𝕜, F) (f y)`, as one about `mvfderiv`, whose codomain is `F`.
  rw [show mvfderiv I f y = _ from
    TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hf, ← hL]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr L.surjective)

/-- On a boundaryless model, let `h` map a normed space `F` into the target of the extended chart
at `x`. If `h` is differentiable at `z` with injective derivative, then the map
`w ↦ (extChartAt I x).symm (h w)` into `M` has injective differential at `z`. -/
theorem injective_mfderiv_extChartAt_symm_comp [I.Boundaryless] [IsManifold I 1 M] {h : F → E}
    {z : F} (hz : h z ∈ (extChartAt I x).target) (hh : DifferentiableAt 𝕜 h z)
    (hinj : Function.Injective (fderiv 𝕜 h z)) :
    Function.Injective (mfderiv 𝓘(𝕜, F) I (fun w ↦ (extChartAt I x).symm (h w)) z) := by
  obtain ⟨L, hL⟩ := TauCeti.isInvertible_mfderiv_extChartAt_symm (I := I) hz
  -- `show` puts the map in the form `(extChartAt I x).symm ∘ h`, the composite for which
  -- `mfderiv_comp` is stated.
  rw [show (fun w ↦ (extChartAt I x).symm (h w)) = (extChartAt I x).symm ∘ h from rfl,
    mfderiv_comp z (mdifferentiableAt_of_isInvertible_mfderiv ⟨L, hL⟩) hh.mdifferentiableAt,
    mfderiv_eq_fderiv, ← hL]
  exact L.injective.comp hinj

end SymplecticGeometry

/-- A `C^n` map into a normed space is `C^n` in every chart: its coordinate expression
`f ∘ (extChartAt I x).symm` is `C^n` on the target of the extended chart. -/
theorem ContMDiff.contDiffOn_comp_extChartAt_symm {n : WithTop ℕ∞} [IsManifold I n M]
    (hf : ContMDiff I 𝓘(𝕜, F) n f) (x : M) :
    ContDiffOn 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
  contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))

/-- A map from a normed space into `M` that is `C^n` on a set `s` is `C^n` in every chart: its
reading `extChartAt I x ∘ g` is `C^n` on the points of `s` that `g` maps into the source of the
chart at `x`. -/
theorem ContMDiffOn.contDiffOn_extChartAt_comp {n : WithTop ℕ∞} [IsManifold I n M] {g : F → M}
    {s : Set F} (hg : ContMDiffOn 𝓘(𝕜, F) I n g s) (x : M) :
    ContDiffOn 𝕜 n (extChartAt I x ∘ g) (s ∩ g ⁻¹' (chartAt H x).source) :=
  (contMDiffOn_extChartAt.comp (hg.mono Set.inter_subset_left) fun _ hy ↦ hy.2).contDiffOn

/-- The reading of a map `g` from a normed space into `M` in extended charts at `x` and at
`g x` is `extChartAt I (g x) ∘ g`: the chart of the normed space is the identity. -/
@[simp, mfld_simps]
theorem writtenInExtChartAt_model_space_left (g : F → M) (x : F) :
    writtenInExtChartAt 𝓘(𝕜, F) I x g = extChartAt I (g x) ∘ g :=
  rfl

end
