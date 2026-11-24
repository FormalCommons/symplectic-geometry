/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars

/-!
# Restricting the scalars of a `C^n` section over a self-modelled base

Let `𝕜'` be a normed algebra over `𝕜`, and let `B` be a manifold modelled on a normed space `EB`
over both fields. Tau Ceti's `ContMDiffSection.restrictScalars` regards a `C^n` section of a fibre
bundle over `B`, for a boundaryless model `IB` over `𝕜'`, as a `C^n` section for the model
`IB.restrictScalars 𝕜`. This file states it for the model `𝓘(𝕜', EB)`, whose restriction is
`𝓘(𝕜, EB)` by `modelWithCornersSelf_restrictScalars`, with the model `𝓘(𝕜, EB)` itself in the
type of the section. Tau Ceti's `ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf` gives
the bundle the matching `C^n` structure over `𝕜`.

The main example is a holomorphic section of a holomorphic vector bundle over a complex manifold,
which is a smooth section of the underlying real vector bundle over the underlying real manifold.

## Main results

* `ContMDiffSection.restrictScalars'`: a `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n`
  section for the model `𝓘(𝕜, EB)`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold

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

end
