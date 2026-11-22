/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Smooth embeddings under restriction of scalars

A `C^n` embedding, `1 ≤ n`, between manifolds modelled on the trivial models over a field `𝕜'`
is a `C^n` embedding for the trivial models over a smaller field `𝕜`, when the target model is
finite-dimensional over `𝕜`: `Manifold.IsSmoothEmbedding.restrictScalars`. For instance, a
holomorphic embedding of complex manifolds is a smooth embedding of the underlying real
manifolds. It combines Tau Ceti's `ContMDiff.restrictScalars`,
`TauCeti.injective_mfderiv_restrictScalars` and `ContMDiff.isImmersion_of_injective_mfderiv`.
-/

public section

open scoped ContDiff Manifold

namespace Manifold.IsSmoothEmbedding

variable (𝕜 : Type*) {𝕜' : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  [IsScalarTower 𝕜 𝕜' E'] [FiniteDimensional 𝕜 E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N]
  {f : M → N}

/-- A `C^n` embedding, `1 ≤ n`, for the trivial models over `𝕜'` is a `C^n` embedding for the
trivial models over the smaller field `𝕜`, if the target model is finite-dimensional over `𝕜`.
For instance, a holomorphic embedding of complex manifolds is a smooth embedding over `ℝ`. -/
theorem restrictScalars (h : IsSmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') n f) (hn : 1 ≤ n) :
    IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n f := by
  have hc := h.contMDiff.restrictScalars 𝕜
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at hc
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact ⟨hc.isImmersion_of_injective_mfderiv hn fun x ↦
    TauCeti.injective_mfderiv_restrictScalars (𝕜' := 𝕜') 𝕜
      (h.isImmersion.mfderiv_injective hn0 x), h.isEmbedding⟩

end Manifold.IsSmoothEmbedding

end
