/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Immersions and embeddings under restriction of scalars

A `C^n` immersion, `1 ≤ n`, between manifolds modelled on the trivial models over a field `𝕜'`
is a `C^n` immersion for the trivial models over a smaller field `𝕜`, when the target model is
finite-dimensional over `𝕜`: `Manifold.IsImmersion.restrictScalars`. The same then holds for
embeddings: `Manifold.IsSmoothEmbedding.restrictScalars`. For instance, a holomorphic embedding
of complex manifolds is a smooth embedding of the underlying real manifolds. The immersion
statement combines `ContMDiff.restrictScalars'`,
`MDifferentiableAt.mfderiv_modelWithCornersSelf_restrictScalars_apply` and
`ContMDiff.isImmersion_of_injective_mfderiv`.
-/

public section

open scoped ContDiff Manifold

namespace Manifold

variable (𝕜 : Type*) {𝕜' : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  [IsScalarTower 𝕜 𝕜' E'] [FiniteDimensional 𝕜 E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace E' N] {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N]
  {f : M → N}

/-- A `C^n` immersion, `1 ≤ n`, for the trivial models over `𝕜'` is a `C^n` immersion for the
trivial models over the smaller field `𝕜`, if the target model is finite-dimensional over `𝕜`.
For instance, a holomorphic immersion of complex manifolds is a smooth immersion over `ℝ`. -/
theorem IsImmersion.restrictScalars (h : IsImmersion 𝓘(𝕜', E) 𝓘(𝕜', E') n f) (hn : 1 ≤ n) :
    IsImmersion 𝓘(𝕜, E) 𝓘(𝕜, E') n f := by
  have hc := h.contMDiff.restrictScalars' 𝕜
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine hc.isImmersion_of_injective_mfderiv hn fun x v w hvw ↦ h.mfderiv_injective hn0 x ?_
  have hd := (h.contMDiff x).mdifferentiableAt hn0
  exact (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply 𝕜 v).symm.trans
    (hvw.trans (hd.mfderiv_modelWithCornersSelf_restrictScalars_apply 𝕜 w))

/-- A `C^n` embedding, `1 ≤ n`, for the trivial models over `𝕜'` is a `C^n` embedding for the
trivial models over the smaller field `𝕜`, if the target model is finite-dimensional over `𝕜`.
For instance, a holomorphic embedding of complex manifolds is a smooth embedding over `ℝ`. -/
theorem IsSmoothEmbedding.restrictScalars (h : IsSmoothEmbedding 𝓘(𝕜', E) 𝓘(𝕜', E') n f)
    (hn : 1 ≤ n) : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n f :=
  ⟨h.isImmersion.restrictScalars 𝕜 hn, h.isEmbedding⟩

end Manifold

end
