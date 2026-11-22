/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import SymplecticGeometry.Geometry.Manifold.ContMDiff.RestrictScalars
public import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# Restricting the scalars of a `C^n` vector bundle

Let `𝕜'` be a normed algebra over `𝕜`, let `B` be a manifold modelled on a normed space `EB` over
both fields, and let `E → B` be a vector bundle over `𝕜'` with model fibre `F`. Tau Ceti's
`VectorBundle.restrictScalars` makes `E` a vector bundle over `𝕜`, with the same trivializations.
This file shows that if `E` is a `C^n` vector bundle for the model `𝓘(𝕜', EB)`, it is a `C^n`
vector bundle over `𝕜` for the model `𝓘(𝕜, EB)`: its coordinate changes over `𝕜` are those over
`𝕜'` with their scalars restricted. Likewise, a section of a fibre bundle that is `C^n` for the
models over `𝕜'` is `C^n` for the models over `𝕜`.

The main example is a holomorphic vector bundle over a complex manifold, which is a smooth real
vector bundle over the underlying real manifold, and whose holomorphic sections are smooth
sections of that real bundle.

## Main results

* `ContMDiffVectorBundle.restrictScalars`: a `C^n` vector bundle over `𝕜'` for the model
  `𝓘(𝕜', EB)` is a `C^n` vector bundle over `𝕜` for the model `𝓘(𝕜, EB)`.
* `ContMDiff.restrictScalars_section`: a section that is `C^n` for the models over `𝕜'` is `C^n`
  for the models over `𝕜`.
* `ContMDiffSection.restrictScalars`: a `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n`
  section for the model `𝓘(𝕜, EB)`.

## Implementation notes

The proof follows that of the continuity of the coordinate changes in Tau Ceti's
`VectorBundle.restrictScalars`, with continuity replaced by smoothness: the coordinate changes over
`𝕜` are those over `𝕜'` composed with the continuous linear map
`ContinuousLinearMap.restrictScalarsL`, by Tau Ceti's
`Bundle.Trivialization.restrictScalars_coordChangeL`, and the base is read over `𝕜` by the
library's `ContMDiffOn.restrictScalars'`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

open Bundle
open scoped Manifold

variable (𝕜 : Type*) {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedSpace 𝕜' EB] [IsScalarTower 𝕜 𝕜' EB] {B : Type*} [TopologicalSpace B]
  [ChartedSpace EB B] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {n : WithTop ℕ∞}

section VectorBundle

variable [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, Module 𝕜' (E x)]
  [VectorBundle 𝕜 F E] [VectorBundle 𝕜' F E]

/-- **Restricting the scalars of a `C^n` vector bundle.** A vector bundle over `𝕜'` that is `C^n`
for the model `𝓘(𝕜', EB)` is `C^n`, as a vector bundle over the smaller field `𝕜`, for the model
`𝓘(𝕜, EB)`. The `𝕜`-structure is any one, such as `VectorBundle.restrictScalars`: a vector bundle
structure is a proposition. For instance, a holomorphic vector bundle over a complex manifold is a
smooth real vector bundle over the underlying real manifold. -/
theorem ContMDiffVectorBundle.restrictScalars [ContMDiffVectorBundle n F E 𝓘(𝕜', EB)] :
    ContMDiffVectorBundle n F E 𝓘(𝕜, EB) where
  contMDiffOn_coordChangeL e e' _ _ :=
    (((ContinuousLinearMap.restrictScalarsL 𝕜' F F 𝕜 𝕜).contMDiff.comp_contMDiffOn
      ((contMDiffOn_coordChangeL (IB := 𝓘(𝕜', EB)) (n := n) e e').restrictScalars' 𝕜))).congr
      fun _ _ ↦ (Bundle.Trivialization.restrictScalars_coordChangeL 𝕜 𝕜' e e').symm

end VectorBundle

variable {F E}

/-- **Restricting the scalars of a `C^n` section.** A section of a fibre bundle that is `C^n` for
the models `𝓘(𝕜', EB)` and `𝓘(𝕜', F)` is `C^n` for the models `𝓘(𝕜, EB)` and `𝓘(𝕜, F)` over the
smaller field `𝕜`. For instance, a holomorphic section of a holomorphic vector bundle is a smooth
section of the underlying real vector bundle. -/
theorem ContMDiff.restrictScalars_section {s : ∀ x, E x}
    (h : ContMDiff 𝓘(𝕜', EB) (𝓘(𝕜', EB).prod 𝓘(𝕜', F)) n fun x ↦ TotalSpace.mk' F x (s x)) :
    ContMDiff 𝓘(𝕜, EB) (𝓘(𝕜, EB).prod 𝓘(𝕜, F)) n fun x ↦ TotalSpace.mk' F x (s x) := by
  simpa only [ModelWithCorners.restrictScalars_prod, modelWithCornersSelf_restrictScalars] using
    h.restrictScalars 𝕜

namespace ContMDiffSection

/-- A `C^n` section for the model `𝓘(𝕜', EB)`, as a `C^n` section for the model `𝓘(𝕜, EB)` over
the smaller field `𝕜`, by `ContMDiff.restrictScalars_section`. For instance, a holomorphic section
of a holomorphic vector bundle, as a smooth section of the underlying real vector bundle. -/
def restrictScalars (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ContMDiffSection 𝓘(𝕜, EB) F n E where
  toFun := s
  contMDiff_toFun := s.contMDiff.restrictScalars_section 𝕜

/-- Restricting the scalars does not change the underlying section. -/
@[simp]
theorem coe_restrictScalars (s : ContMDiffSection 𝓘(𝕜', EB) F n E) :
    ⇑(s.restrictScalars 𝕜) = s :=
  (rfl)

/-- The value of a section with its scalars restricted is that of the section. -/
theorem restrictScalars_apply (s : ContMDiffSection 𝓘(𝕜', EB) F n E) (x : B) :
    s.restrictScalars 𝕜 x = s x :=
  (rfl)

end ContMDiffSection

end
