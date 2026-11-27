/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Restricting the scalars of `C^n` sections and coordinate changes

Let `𝕜'` be a normed algebra over `𝕜`, and let `B` be a manifold modelled on a normed space `EB`
over both fields. Tau Ceti's `ContMDiffSection.restrictScalars` regards a `C^n` section of a fibre
bundle over `B`, for a boundaryless model `IB` over `𝕜'`, as a `C^n` section for the model
`IB.restrictScalars 𝕜`. This file states it for the model `𝓘(𝕜', EB)`, whose restriction is
`𝓘(𝕜, EB)` by `modelWithCornersSelf_restrictScalars`, with the model `𝓘(𝕜, EB)` itself in the
type of the section. Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf` gives
the bundle the matching `C^n` structure over `𝕜`.

The main example is a holomorphic section of a holomorphic vector bundle over a complex manifold,
which is a smooth section of the underlying real vector bundle over the underlying real manifold.

Conversely, let `E` be a vector bundle over `𝕜'` with finite-dimensional model `F`, which is also a
vector bundle over the complete field `𝕜` with the same trivializations, and is `C^n` over `𝕜`, for
a model over `𝕜`. Then its coordinate changes over `𝕜'` are `C^n` over `𝕜`
(`contMDiffOn_coordChangeL_of_restrictScalars`): restricting their scalars gives the coordinate
changes over `𝕜` (`Bundle.Trivialization.restrictScalars_coordChangeL`), and restricting scalars
has a continuous linear left inverse in finite dimension
(`ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`). The main example is a
complex vector bundle whose underlying real bundle is smooth.

## Main results

* `ContMDiffSection.restrictScalars'`: a `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n`
  section for the model `𝓘(𝕜, EB)`.
* `contMDiffOn_coordChangeL_of_restrictScalars`: the coordinate changes over `𝕜'` of a bundle
  with finite-dimensional model that is `C^n` over `𝕜` are `C^n` over `𝕜`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold

section Section

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedSpace 𝕜' EB] [IsScalarTower 𝕜 𝕜' EB] {B : Type*} [TopologicalSpace B]
  [ChartedSpace EB B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {n : WithTop ℕ∞}

namespace ContMDiffSection

/-- A `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n` section for the model `𝓘(𝕜, EB)` over
the smaller field `𝕜`. For instance, a holomorphic section of a holomorphic vector bundle, as a
smooth section of the underlying real vector bundle. -/
def restrictScalars' (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ContMDiffSection 𝓘(𝕜, EB) F n E where
  toFun := s
  contMDiff_toFun := by
    simpa only [modelWithCornersSelf_restrictScalars, coe_restrictScalars] using
      (s.restrictScalars 𝕜).contMDiff

/-- Restricting the scalars does not change the underlying section. -/
@[simp]
theorem coe_restrictScalars' (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ⇑(s.restrictScalars' 𝕜) = s :=
  (rfl)

/-- The value of a section with its scalars restricted is that of the section. -/
theorem restrictScalars'_apply (s : ContMDiffSection 𝓘(𝕜', EB) F n E) (x : B) :
    s.restrictScalars' 𝕜 x = s x :=
  (rfl)

end ContMDiffSection

end Section

section CoordChange

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedSpace 𝕜 F] [IsScalarTower 𝕜 𝕜' F]
  [FiniteDimensional 𝕜 F] {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜' (E x)]
  [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜' F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]

/-- For a vector bundle over `𝕜'` with finite-dimensional model, which is a `C^n` vector bundle
over the smaller field `𝕜` with the same trivializations, the coordinate changes over `𝕜'` are
`C^n` over `𝕜`. For instance, the complex coordinate changes of a complex vector bundle whose
underlying real bundle is smooth are smooth. -/
theorem contMDiffOn_coordChangeL_of_restrictScalars (e e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜'] F) n (fun b ↦ (e.coordChangeL 𝕜' e' b : F →L[𝕜'] F))
      (e.baseSet ∩ e'.baseSet) := by
  -- Restricting the scalars to `𝕜` has a continuous `𝕜`-linear left inverse `P`.
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := ContinuousLinearMap.restrictScalarsL 𝕜' F F 𝕜 𝕜)
    (fun f g h ↦ ContinuousLinearMap.ext fun x ↦ by simpa using DFunLike.congr_fun h x)
  refine (P.contMDiff.comp_contMDiffOn (contMDiffOn_coordChangeL (IB := IB) e e')).congr
    fun b _ ↦ ?_
  simp only [Function.comp_apply, ← Trivialization.restrictScalars_coordChangeL 𝕜 𝕜' e e']
  exact (hP _).symm

end CoordChange

end
