/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Chart data of one-forms over a general model space

Let `M` be a `C¹` manifold modelled on a real normed space `E`, and `A` a finite bundle atlas of
a real vector bundle `V → M`. The `V`-valued one-forms `x ↦ (T_x M →L[ℝ] V x)` carry the atlas
`A.tangentHom` on the same chart domains, and the Sobolev sections
`TauCeti.SobolevSection A.tangentHom μ p k` are built on its section chart data. This file
identifies the chart images, overlaps and transitions of that section chart data with those of
`A`, and computes its coordinate change on an overlap: `η ↦ g ∘ η ∘ dτ`, for the coordinate
change `g` of `V` and the derivative of the chart transition `τ`.

These are the lemmas `TauCeti.FiniteBundleAtlas.sectionChartData_image_tangentHom`,
`TauCeti.FiniteBundleAtlas.sectionChartData_overlap_tangentHom`,
`TauCeti.FiniteBundleAtlas.sectionChartData_transition_tangentHom`,
`TauCeti.FiniteBundleAtlas.ae_image_tangentHom_iff`,
`TauCeti.FiniteBundleAtlas.ae_overlap_tangentHom_iff` and
`TauCeti.FiniteBundleAtlas.sectionChartData_coordChange_tangentHom_apply` of Tau Ceti's
`Geometry/Manifold/VectorBundle/Sobolev/ZeroOneForm.lean`, which are stated there for a complex
curve, modelled on `ℂ`. Their proofs, followed here, use nothing of `ℂ`, so this file states them
for any model `E`; the primed names avoid a clash with Tau Ceti's.

## Main results

* `TauCeti.FiniteBundleAtlas.sectionChartData_image_tangentHom'`,
  `TauCeti.FiniteBundleAtlas.sectionChartData_overlap_tangentHom'`,
  `TauCeti.FiniteBundleAtlas.sectionChartData_transition_tangentHom'`: the chart images, overlaps
  and transitions of the section chart data of one-forms are those of `A`.
* `TauCeti.FiniteBundleAtlas.ae_image_tangentHom_iff'`,
  `TauCeti.FiniteBundleAtlas.ae_overlap_tangentHom_iff'`: the corresponding statements for
  almost everywhere on chart images and overlaps.
* `TauCeti.FiniteBundleAtlas.sectionChartData_coordChange_tangentHom_apply'`: the coordinate
  change of the chart data of one-forms.
-/

public section

open Bundle MeasureTheory Set

open scoped Manifold

universe u

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  (A : FiniteBundleAtlas E M F V)

/-- The chart images of the section chart data of `V`-valued one-forms are those of `A`. -/
@[simp]
theorem sectionChartData_image_tangentHom' (i : Fin A.n) :
    (A.tangentHom.sectionChartData.image i : Set E) = A.image i :=
  congrArg SetLike.coe ((A.tangentHom.sectionChartData_image i).trans (image_tangentHom A i))

/-- The chart overlaps of the section chart data of `V`-valued one-forms are those of `A`. -/
@[simp]
theorem sectionChartData_overlap_tangentHom' (i i' : Fin A.n) :
    A.tangentHom.sectionChartData.overlap i i' = A.overlap i i' :=
  (A.tangentHom.sectionChartData_overlap i i').trans (overlap_tangentHom A i i')

/-- On an overlap, the chart transitions of the section chart data of `V`-valued one-forms are
those of `A`. -/
@[simp]
theorem sectionChartData_transition_tangentHom' {i i' : Fin A.n} {y : E}
    (hy : y ∈ A.overlap i i') :
    A.tangentHom.sectionChartData.transition i i' y = A.transition i i' y :=
  (A.tangentHom.sectionChartData_transition_of_mem (by rwa [overlap_tangentHom])).trans
    (congrFun (transition_tangentHom A i i') y)

/-- A property holds almost everywhere on a chart image of the section chart data of one-forms
exactly when it holds almost everywhere on the corresponding chart image of `A`. -/
theorem ae_image_tangentHom_iff' [MeasurableSpace E] (μ : Measure E) (i : Fin A.n)
    {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i : Set E), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [sectionChartData_image_tangentHom']

/-- A property holds almost everywhere on an overlap of the section chart data of one-forms
exactly when it holds almost everywhere on the corresponding overlap of `A`. -/
theorem ae_overlap_tangentHom_iff' [MeasurableSpace E] (μ : Measure E) (i i' : Fin A.n)
    {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.overlap i i'), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.overlap i i'), P y := by
  rw [sectionChartData_overlap_tangentHom']

/-- On the overlap of charts `i` and `i'`, the coordinate change of the chart data of `V`-valued
one-forms is `η ↦ g ∘ η ∘ dτ`, for the coordinate change `g` of `V` and the chart transition `τ`. -/
theorem sectionChartData_coordChange_tangentHom_apply' {i i' : Fin A.n} {y : E}
    (hy : y ∈ A.overlap i i') (η : E →L[ℝ] F) :
    A.tangentHom.sectionChartData.coordChange i i' y η =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        (η.comp (fderiv ℝ (A.transition i i') y)) := by
  have hy' : y ∈ A.tangentHom.overlap i i' := by rwa [overlap_tangentHom]
  have hτ : A.tangentHom.transition i i' y ∈ A.tangentHom.image i := by
    rw [transition_tangentHom, image_tangentHom]
    exact A.overlap_subset_image i' i (A.transition_mem_overlap hy)
  have h := A.tangentHom.coord_eq_coordChange (fun x ↦ (A.tangentHom.triv i).symm x η) hy'
  rw [A.tangentHom.coord_triv_symm η hτ, A.coord_tangentHom_eq_coordChange _ hy,
    ← transition_tangentHom, A.tangentHom.coord_triv_symm η hτ, transition_tangentHom] at h
  rw [A.tangentHom.sectionChartData_coordChange_of_mem hy']
  exact h.symm

end FiniteBundleAtlas

end TauCeti

end
