/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Differentials of maps into normed spaces, read in a chart

For a map `f : M → F` into a normed space and a point `y` of the source of the extended chart at
`x`, which need not be centred at `y`, the range of `mvfderiv I f y` is the range of the Fréchet
derivative of the coordinate expression `f ∘ (extChartAt I x).symm` at the chart image of `y`.
This is the off-centre form of Tau Ceti's
`TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`, and its proof reads `mvfderiv I f y`
in the chart by Tau Ceti's `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt`.

## Main results

* `SymplecticGeometry.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm_of_mem_source`: the
  range of `mvfderiv I f y` is that of the coordinate derivative at the chart image of `y`.
* `ContMDiff.contDiffOn_comp_extChartAt_symm`: a `C^n` map into a normed space is `C^n` in every
  chart.
* `ContMDiff.contDiffOn_mpullbackWithin_extChartAt_symm`: a `C^m` vector field on a `C^n`
  manifold, `m + 1 ≤ n`, is `C^m` in every chart: its coordinate expression
  `mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)` is `C^m` on the target of the
  extended chart. This is the `mpullbackWithin` form of Tau Ceti's
  `ContMDiffOn.contDiffOn_mpullback_extChartAt_symm`.
* `VectorField.mfderivWithin_extChartAt_symm_mpullbackWithin`: the differential of the inverse
  chart sends the coordinate expression of a vector field back to the field.
-/

public section

open Set Function
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

end SymplecticGeometry

/-- A `C^n` map into a normed space is `C^n` in every chart: its coordinate expression
`f ∘ (extChartAt I x).symm` is `C^n` on the target of the extended chart. -/
theorem ContMDiff.contDiffOn_comp_extChartAt_symm {n : WithTop ℕ∞} [IsManifold I n M]
    (hf : ContMDiff I 𝓘(𝕜, F) n f) (x : M) :
    ContDiffOn 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x).target :=
  contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x))

section VectorField

open VectorField

variable {V : (x : M) → TangentSpace I x}

/-- A `C^m` vector field on a `C^n` manifold, with `m + 1 ≤ n`, read in an extended chart, is
`C^m` on the chart target. -/
theorem ContMDiff.contDiffOn_mpullbackWithin_extChartAt_symm {m n : WithTop ℕ∞} [CompleteSpace E]
    [IsManifold I 1 M] [IsManifold I n M]
    (hV : ContMDiff I I.tangent m (fun y ↦ (⟨y, V y⟩ : TangentBundle I M))) (hmn : m + 1 ≤ n)
    (x : M) :
    ContDiffOn 𝕜 m (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
      (extChartAt I x).target := fun y hy ↦
  contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 <|
    ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' (t := univ)
      (hV _).contMDiffWithinAt (contMDiffWithinAt_extChartAt_symm_range x hy)
      (isInvertible_mfderivWithin_extChartAt_symm hy) hy
      (uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_extChartAt_target x)) hmn (by simp)
      (extChartAt_target_subset_range x) rfl

namespace VectorField

/-- The derivative of the inverse chart sends the coordinate expression of a vector field back to
the field. -/
theorem mfderivWithin_extChartAt_symm_mpullbackWithin [IsManifold I 1 M] {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) y) =
        V ((extChartAt I x).symm y) := by
  rw [mpullbackWithin_apply]
  exact ((isInvertible_mfderivWithin_extChartAt_symm hy).inverse_apply_eq.1 rfl).symm

end VectorField

end VectorField

end
