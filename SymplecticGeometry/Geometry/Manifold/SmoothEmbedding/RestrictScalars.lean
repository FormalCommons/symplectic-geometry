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

The same holds for maps into a product `N × N'` with the product of the trivial models as
target model (`Manifold.IsImmersion.restrictScalars_prod`,
`Manifold.IsSmoothEmbedding.restrictScalars_prod`): that model is the trivial model on the product
of the model spaces (`modelWithCornersSelf_prod`), so these follow from the statements for the
trivial models.
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

section Prod

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕜' F']
  [IsScalarTower 𝕜 𝕜' F'] [FiniteDimensional 𝕜 F'] {N' : Type*} [TopologicalSpace N']
  [ChartedSpace F' N'] [IsManifold 𝓘(𝕜, F') n N'] {g : M → N × N'}

/-- A `C^n` immersion, `1 ≤ n`, into a product of manifolds, for the trivial model over `𝕜'` on
the source and the product of the trivial models over `𝕜'` on the target, is a `C^n` immersion
for the corresponding models over the smaller field `𝕜`, if both factors of the target model are
finite-dimensional over `𝕜`. For instance, a holomorphic immersion into a product of complex
manifolds is a smooth immersion over `ℝ`. -/
theorem IsImmersion.restrictScalars_prod
    (h : IsImmersion 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) n g) (hn : 1 ≤ n) :
    IsImmersion 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n g := by
  -- Read the product model as the trivial model on `E' × F'`, with the product charts.
  have hp : IsManifold (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n (N × N') := inferInstance
  let : ChartedSpace (E' × F') (N × N') := prodChartedSpace E' N F' N'
  have : IsManifold 𝓘(𝕜, E' × F') n (N × N') :=
    (modelWithCornersSelf_prod (𝕜 := 𝕜) (E := E') (F := F')) ▸ hp
  rw [← modelWithCornersSelf_prod] at h ⊢
  exact h.restrictScalars 𝕜 hn

/-- A `C^n` embedding, `1 ≤ n`, into a product of manifolds, for the trivial model over `𝕜'` on
the source and the product of the trivial models over `𝕜'` on the target, is a `C^n` embedding
for the corresponding models over the smaller field `𝕜`, if both factors of the target model are
finite-dimensional over `𝕜`. For instance, a holomorphic embedding into a product of complex
manifolds is a smooth embedding over `ℝ`. -/
theorem IsSmoothEmbedding.restrictScalars_prod
    (h : IsSmoothEmbedding 𝓘(𝕜', E) (𝓘(𝕜', E').prod 𝓘(𝕜', F')) n g) (hn : 1 ≤ n) :
    IsSmoothEmbedding 𝓘(𝕜, E) (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n g :=
  ⟨h.isImmersion.restrictScalars_prod 𝕜 hn, h.isEmbedding⟩

end Prod

end Manifold

end
