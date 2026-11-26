/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars
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

More generally, both statements hold for any boundaryless models `I`, `I'` over `𝕜'` and their
scalar restrictions `I.restrictScalars 𝕜`, `I'.restrictScalars 𝕜`
(`Manifold.IsImmersion.restrictScalars_modelWithCorners`,
`Manifold.IsSmoothEmbedding.restrictScalars_modelWithCorners`), by Tau Ceti's
`ContMDiff.restrictScalars` and `TauCeti.injective_mfderiv_restrictScalars`. For maps into a
product `N × N'` with the product of the trivial models as target model, they give
`Manifold.IsImmersion.restrictScalars_prod` and `Manifold.IsSmoothEmbedding.restrictScalars_prod`,
since restriction of scalars commutes with products of models
(`ModelWithCorners.restrictScalars_prod`) and takes trivial models to trivial models
(`modelWithCornersSelf_restrictScalars`).
-/

public section

open scoped ContDiff Manifold

namespace Manifold

variable (𝕜 : Type*) {𝕜' : Type*} [RCLike 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  [IsScalarTower 𝕜 𝕜' E'] [FiniteDimensional 𝕜 E']

section General

variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'} [I.Boundaryless]
  [I'.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*}
  [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} [IsManifold (I.restrictScalars 𝕜) n M]
  [IsManifold (I'.restrictScalars 𝕜) n N] {f : M → N}

/-- A `C^n` immersion, `1 ≤ n`, for boundaryless models `I`, `I'` over `𝕜'` is a `C^n` immersion
for their scalar restrictions to the smaller field `𝕜`, if the target model space is
finite-dimensional over `𝕜`. -/
theorem IsImmersion.restrictScalars_modelWithCorners (h : IsImmersion I I' n f) (hn : 1 ≤ n) :
    IsImmersion (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact (h.contMDiff.restrictScalars 𝕜).isImmersion_of_injective_mfderiv hn fun x ↦
    TauCeti.injective_mfderiv_restrictScalars 𝕜 (h.mfderiv_injective hn0 x)

/-- A `C^n` embedding, `1 ≤ n`, for boundaryless models `I`, `I'` over `𝕜'` is a `C^n` embedding
for their scalar restrictions to the smaller field `𝕜`, if the target model space is
finite-dimensional over `𝕜`. -/
theorem IsSmoothEmbedding.restrictScalars_modelWithCorners (h : IsSmoothEmbedding I I' n f)
    (hn : 1 ≤ n) : IsSmoothEmbedding (I.restrictScalars 𝕜) (I'.restrictScalars 𝕜) n f :=
  ⟨h.isImmersion.restrictScalars_modelWithCorners 𝕜 hn, h.isEmbedding⟩

end General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {N : Type*} [TopologicalSpace N]
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
  have : IsManifold (𝓘(𝕜', E).restrictScalars 𝕜) n M := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      (inferInstance : IsManifold 𝓘(𝕜, E) n M)
  have : IsManifold ((𝓘(𝕜', E').prod 𝓘(𝕜', F')).restrictScalars 𝕜) n (N × N') := by
    simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
      (inferInstance : IsManifold (𝓘(𝕜, E').prod 𝓘(𝕜, F')) n (N × N'))
  simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
    h.restrictScalars_modelWithCorners 𝕜 hn

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
