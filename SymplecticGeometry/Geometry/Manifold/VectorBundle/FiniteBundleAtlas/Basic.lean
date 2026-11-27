/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import SymplecticGeometry.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Finite bundle atlases: chart readings

Three facts about Tau Ceti's finite bundle atlases `TauCeti.FiniteBundleAtlas`.

* `TauCeti.FiniteBundleAtlas.coord_sub`: on the image of a chart, the chart reading of a
  difference of sections is the difference of their readings, next to Tau Ceti's
  `TauCeti.FiniteBundleAtlas.coord_add` and `TauCeti.FiniteBundleAtlas.coord_smul`.
* `TauCeti.FiniteBundleAtlas.iteratedFDeriv_coord_sub`: the same for the iterated derivatives of
  the readings at points of the chart image, for sections whose readings are `Cʲ` there.
* `TauCeti.FiniteBundleAtlas.coord_hom_apply_self`: Tau Ceti's
  `TauCeti.FiniteBundleAtlas.coord_hom_apply` for a section of the endomorphism bundle of `V`,
  with the result read in `A` itself rather than in `A.ofBaseSet A.closure_dom_subset_baseSet`.
-/

public section

namespace TauCeti

namespace FiniteBundleAtlas

open Bundle

section Linear

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- On the image of chart `i`, the chart reading of `s - t` is the difference of the readings of
`s` and `t`. -/
theorem coord_sub (i : Fin A.n) (s t : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (s - t) y = A.coord i s y - A.coord i t y := by
  rw [eq_sub_iff_add_eq, ← A.coord_add i _ _ hy, sub_add_cancel]

end Linear

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- At a point of the image of chart `i`, the derivative of order `j` of the chart reading of
`s - t` is the difference of those of `s` and `t`, when both readings are `Cʲ` on the image. -/
theorem iteratedFDeriv_coord_sub (i : Fin A.n) {s t : ∀ x, V x} {j : ℕ}
    (hs : ContDiffOn ℝ j (A.coord i s) (A.image i))
    (ht : ContDiffOn ℝ j (A.coord i t) (A.image i)) {y : E} (hy : y ∈ A.image i) :
    iteratedFDeriv ℝ j (A.coord i (s - t)) y =
      iteratedFDeriv ℝ j (A.coord i s) y - iteratedFDeriv ℝ j (A.coord i t) y := by
  have hU := (A.image i).isOpen.mem_nhds hy
  rw [Set.EqOn.iteratedFDeriv_of_isOpen (g := A.coord i s - A.coord i t)
      (fun z hz ↦ by rw [Pi.sub_apply, A.coord_sub i s t hz]) (A.image i).isOpen j hy,
    iteratedFDeriv_sub_apply (hs.contDiffAt hU) (ht.contDiffAt hU)]

end Deriv

section Hom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  (A : FiniteBundleAtlas E M F V)

/-- Tau Ceti's `TauCeti.FiniteBundleAtlas.coord_hom_apply` for a section `φ` of the bundle of
endomorphisms of `V`: on the image of chart `i`, the reading of `φ` applied to the reading of a
section `s` is the reading in `A` of the section `x ↦ φ x (s x)`. -/
theorem coord_hom_apply_self (i : Fin A.n) (φ : ∀ x, V x →L[𝕜] V x) (s : ∀ x, V x) {y : E}
    (hy : y ∈ A.image i) :
    (A.hom A.closure_dom_subset_baseSet).coord i φ y (A.coord i s y) =
      A.coord i (fun x ↦ φ x (s x)) y :=
  -- `A.ofBaseSet A.closure_dom_subset_baseSet` is `A` by the eta rule for structures. A rewrite
  -- cannot replace it, since the type `Fin _` of the chart index depends on the atlas.
  coord_hom_apply _ _ i φ s hy

end Hom

end FiniteBundleAtlas

end TauCeti

end
