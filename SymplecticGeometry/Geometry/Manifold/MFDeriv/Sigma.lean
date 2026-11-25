/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Geometry.Manifold.ContMDiff.Sigma

/-!
# Derivatives of maps out of a disjoint union

Tau Ceti's `TauCeti/Geometry/Manifold/ContMDiff/Sigma.lean` shows that, in the charts of
`ChartedSpace.sigma`, a map out of `Σ i, M i` is near `⟨i, x⟩` the same as its restriction to `M i`
near `x`, and deduces that smoothness is checked componentwise (`TauCeti.contMDiffAt_sigma_iff`).
This file draws the same conclusion for differentiability and for the derivative.

## Main results

* `TauCeti.mdifferentiableAt_sigma_iff`: a map out of `Σ i, M i` is differentiable at `⟨i, x⟩`
  exactly when its restriction to `M i` is differentiable at `x`.
* `TauCeti.mfderiv_sigma`: the derivative at `⟨i, x⟩` is that of the restriction at `x`.

The proofs follow that of Tau Ceti's `TauCeti.contMDiffAt_sigma_iff`.
-/

public section

open Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {ι : Type*} {M : ι → Type*}
  [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

namespace TauCeti

/-- In coordinates, a map out of a disjoint union at `⟨i, x⟩` is its restriction to `M i` at
`x`. -/
theorem writtenInExtChartAt_sigma {F : (Σ i, M i) → N} {i : ι} (x : M i) :
    writtenInExtChartAt I I' (Sigma.mk i x) F = writtenInExtChartAt I I' x (F ∘ Sigma.mk i) := by
  simp only [writtenInExtChartAt, extChartAt_sigmaMk_symm]
  -- Both sides are the same composite, bracketed differently.
  rfl

/-- A map out of a disjoint union is differentiable at `⟨i, x⟩` exactly when its restriction to
`M i` is differentiable at `x`. -/
theorem mdifferentiableAt_sigma_iff {F : (Σ i, M i) → N} {i : ι} {x : M i} :
    MDifferentiableAt I I' F ⟨i, x⟩ ↔ MDifferentiableAt I I' (F ∘ Sigma.mk i) x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff, writtenInExtChartAt_sigma,
    extChartAt_sigmaMk_apply, ← IsOpenEmbedding.sigmaMk.continuousAt_iff]

/-- The derivative of a map out of a disjoint union at `⟨i, x⟩` is the derivative of its
restriction to `M i` at `x`. -/
theorem mfderiv_sigma (F : (Σ i, M i) → N) {i : ι} (x : M i) :
    mfderiv I I' F ⟨i, x⟩ = mfderiv I I' (F ∘ Sigma.mk i) x := by
  by_cases h : MDifferentiableAt I I' (F ∘ Sigma.mk i) x
  · simp only [mfderiv, mdifferentiableAt_sigma_iff.2 h, h, ↓reduceIte,
      writtenInExtChartAt_sigma, extChartAt_sigmaMk_apply]
    -- The two sides differ only in `tangentSpaceCastModel` at `⟨i, x⟩` and at `x`, which are
    -- both the identity of `E`.
    rfl
  · simp only [mfderiv, mt mdifferentiableAt_sigma_iff.1 h, h, ↓reduceIte]
    -- Both sides are the zero map, at tangent spaces that are both `E` and `E'` by definition.
    rfl

end TauCeti
