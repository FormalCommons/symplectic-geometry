/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import SymplecticGeometry.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Restricting the scalars of `C^n` maps to the trivial models

Let `𝕜'` be a normed algebra over `𝕜`, and let `E` and `E'` be normed spaces over both fields,
compatibly. Tau Ceti's `ContMDiff.restrictScalars` turns a map that is `C^n` for the models
`𝓘(𝕜', E)` and `𝓘(𝕜', E')` into one that is `C^n` for `𝓘(𝕜', E).restrictScalars 𝕜` and
`𝓘(𝕜', E').restrictScalars 𝕜`. These models equal `𝓘(𝕜, E)` and `𝓘(𝕜, E')` only
propositionally (`modelWithCornersSelf_restrictScalars`). This file states the results directly
for `𝓘(𝕜, E)` and `𝓘(𝕜, E')`, so that no cast is needed at their uses.

The main example is a holomorphic map between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`, which is smooth for the models `𝓘(ℝ, E)` and `𝓘(ℝ, E')` of the underlying real
manifolds.

Conversely, a family of continuous `𝕜'`-linear maps between spaces that are finite-dimensional
over the complete field `𝕜` is `C^n` over `𝕜` if and only if the family of continuous `𝕜`-linear
maps obtained by restricting their scalars is: restricting scalars is injective
(`ContinuousLinearMap.restrictScalars_injective`), so in finite dimension it has a continuous
linear left inverse (`ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`).

## Main results

* `ContMDiffWithinAt.restrictScalars'`, `ContMDiffAt.restrictScalars'`,
  `ContMDiffOn.restrictScalars'`, `ContMDiff.restrictScalars'`: a map that is `C^n` for the
  trivial models over `𝕜'` (within a set, at a point, on a set, globally) is `C^n` for the
  trivial models over `𝕜`.
* `contMDiffWithinAt_clm_restrictScalars_iff`, `contMDiffAt_clm_restrictScalars_iff`,
  `contMDiffOn_clm_restrictScalars_iff`, `contMDiff_clm_restrictScalars_iff`: a family of
  continuous `𝕜'`-linear maps between spaces finite-dimensional over `𝕜` is `C^n` over `𝕜`
  (within a set, at a point, on a set, globally) if and only if its scalar restriction is.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Chapter 1.
-/

public section

open scoped Manifold

section TrivialModels

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {n : WithTop ℕ∞} {f : M → N} {s : Set M} {x : M}

/-- A map which is `C^n` within a set at a point for the trivial models over `𝕜'` is `C^n` within
that set at that point for the trivial models over the smaller field `𝕜`. -/
theorem ContMDiffWithinAt.restrictScalars' (h : ContMDiffWithinAt 𝓘(𝕜', E) 𝓘(𝕜', E') n f s x) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x := by
  simpa only [modelWithCornersSelf_restrictScalars] using h.restrictScalars 𝕜

/-- A map which is `C^n` at a point for the trivial models over `𝕜'` is `C^n` at that point for
the trivial models over the smaller field `𝕜`. -/
theorem ContMDiffAt.restrictScalars' (h : ContMDiffAt 𝓘(𝕜', E) 𝓘(𝕜', E') n f x) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x :=
  ContMDiffWithinAt.restrictScalars' 𝕜 h

/-- A map which is `C^n` on a set for the trivial models over `𝕜'` is `C^n` on that set for the
trivial models over the smaller field `𝕜`. -/
theorem ContMDiffOn.restrictScalars' (h : ContMDiffOn 𝓘(𝕜', E) 𝓘(𝕜', E') n f s) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s :=
  fun x hx ↦ (h x hx).restrictScalars' 𝕜

/-- A `C^n` map for the trivial models over `𝕜'` is `C^n` for the trivial models over the smaller
field `𝕜`. For instance, a holomorphic map between complex manifolds is smooth for the underlying
real manifolds. -/
theorem ContMDiff.restrictScalars' (h : ContMDiff 𝓘(𝕜', E) 𝓘(𝕜', E') n f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f :=
  fun x ↦ (h x).restrictScalars' 𝕜

end TrivialModels

section ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M] {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜 F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
  [NormedSpace 𝕜 F'] [IsScalarTower 𝕜 𝕜' F'] [FiniteDimensional 𝕜 F']
  {f : M → F →L[𝕜'] F'} {s : Set M} {x : M}

/-- Let `F` and `F'` be finite-dimensional over the complete field `𝕜`. A family of continuous
`𝕜'`-linear maps `F → F'` is `C^n` over `𝕜` within a set at a point if and only if the family of
continuous `𝕜`-linear maps obtained by restricting their scalars is. -/
theorem contMDiffWithinAt_clm_restrictScalars_iff :
    ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜] F') n (fun y ↦ (f y).restrictScalars 𝕜) s x ↔
      ContMDiffWithinAt I 𝓘(𝕜, F →L[𝕜'] F') n f s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- Restricting the scalars to `𝕜` has a continuous `𝕜`-linear left inverse `P`.
    obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
      (f := ContinuousLinearMap.restrictScalarsL 𝕜' F F' 𝕜 𝕜)
      (ContinuousLinearMap.restrictScalars_injective 𝕜)
    simp only [ContinuousLinearMap.coe_restrict_scalarsL'] at hP
    exact (P.contMDiff.contMDiffAt.comp_contMDiffWithinAt x h).congr (fun y _ ↦ (hP _).symm)
      (hP _).symm
  · simpa only [Function.comp_def, ContinuousLinearMap.coe_restrict_scalarsL'] using
      ContMDiffAt.comp_contMDiffWithinAt x
        (ContinuousLinearMap.restrictScalarsL 𝕜' F F' 𝕜 𝕜).contMDiff.contMDiffAt h

/-- Let `F` and `F'` be finite-dimensional over the complete field `𝕜`. A family of continuous
`𝕜'`-linear maps `F → F'` is `C^n` over `𝕜` at a point if and only if the family of continuous
`𝕜`-linear maps obtained by restricting their scalars is. -/
theorem contMDiffAt_clm_restrictScalars_iff :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] F') n (fun y ↦ (f y).restrictScalars 𝕜) x ↔
      ContMDiffAt I 𝓘(𝕜, F →L[𝕜'] F') n f x :=
  contMDiffWithinAt_clm_restrictScalars_iff

/-- Let `F` and `F'` be finite-dimensional over the complete field `𝕜`. A family of continuous
`𝕜'`-linear maps `F → F'` is `C^n` over `𝕜` on a set if and only if the family of continuous
`𝕜`-linear maps obtained by restricting their scalars is. -/
theorem contMDiffOn_clm_restrictScalars_iff :
    ContMDiffOn I 𝓘(𝕜, F →L[𝕜] F') n (fun y ↦ (f y).restrictScalars 𝕜) s ↔
      ContMDiffOn I 𝓘(𝕜, F →L[𝕜'] F') n f s :=
  forall₂_congr fun _ _ ↦ contMDiffWithinAt_clm_restrictScalars_iff

/-- Let `F` and `F'` be finite-dimensional over the complete field `𝕜`. A family of continuous
`𝕜'`-linear maps `F → F'` is `C^n` over `𝕜` if and only if the family of continuous `𝕜`-linear
maps obtained by restricting their scalars is. -/
theorem contMDiff_clm_restrictScalars_iff :
    ContMDiff I 𝓘(𝕜, F →L[𝕜] F') n (fun y ↦ (f y).restrictScalars 𝕜) ↔
      ContMDiff I 𝓘(𝕜, F →L[𝕜'] F') n f :=
  forall_congr' fun _ ↦ contMDiffAt_clm_restrictScalars_iff

end ContinuousLinearMap

end
