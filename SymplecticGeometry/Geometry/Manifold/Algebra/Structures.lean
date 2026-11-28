/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# A normed algebra is a `C^n` ring over its scalars

Mathlib's `instFieldContMDiffRing` says that a nontrivially normed field `𝕜` is a `C^n` ring
over itself, with the model `𝓘(𝕜)`. This file gives the same for any normed ring `A` that is a
normed algebra over `𝕜`, with the model `𝓘(𝕜, A)`: addition and multiplication in `A` are `C^n`
over `𝕜`, for every `n`. Tau Ceti's `TauCeti.realComplexContMDiffRing`, the case of `ℂ` over
`ℝ`, is a special case.

The proof is that of `TauCeti.realComplexContMDiffRing`, with Mathlib's `contDiff_mul` for a
normed algebra.

## Main results

* the instance `ContMDiffRing 𝓘(𝕜, A) n A`.
-/

public section

open scoped Manifold ContDiff

/-- A normed ring `A` that is a normed algebra over `𝕜` is a `C^n` ring over `𝕜` with the model
`𝓘(𝕜, A)`, for every `n`. -/
instance instContMDiffRingNormedAlgebra {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] {n : ℕ∞ω} :
    ContMDiffRing 𝓘(𝕜, A) n A where
  toContMDiffAdd := instContMDiffAddSelf
  contMDiff_mul := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contDiff_mul.contMDiff

end
