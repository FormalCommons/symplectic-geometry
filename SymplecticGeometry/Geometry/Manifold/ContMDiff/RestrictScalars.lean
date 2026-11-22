/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

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

## Main results

* `ContMDiffWithinAt.restrictScalars'`, `ContMDiffAt.restrictScalars'`,
  `ContMDiffOn.restrictScalars'`, `ContMDiff.restrictScalars'`: a map that is `C^n` for the
  trivial models over `𝕜'` (within a set, at a point, on a set, globally) is `C^n` for the
  trivial models over `𝕜`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Chapter 1.
-/

public section

open scoped Manifold

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

end
