/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth inversion in a normed field over a smaller field

Mathlib's `ContMDiffInv₀ 𝓘(𝕜) n 𝕜` says that inversion in a nontrivially normed field `𝕜` is
`C^n` away from `0`, over `𝕜` itself. This file gives the same for a normed field `𝕜'` that is a
normed algebra over `𝕜`, with the model `𝓘(𝕜, 𝕜')`, such as `ℂ` over `ℝ` with the model
`𝓘(ℝ, ℂ)`. With Tau Ceti's `TauCeti.realComplexContMDiffRing`, it lets Mathlib's
`ContMDiffAt.div₀` and its variants divide real `C^n` complex valued functions on a real manifold.

The proof is that of Mathlib's instance `instContMDiffInv₀ModelWithCornersSelf`, with Mathlib's
`contDiffAt_inv` over `𝕜` for elements of `𝕜'`.

## Main results

* the instance `ContMDiffInv₀ 𝓘(𝕜, 𝕜') n 𝕜'`.
-/

public section

open scoped Manifold ContDiff

/-- In a normed field `𝕜'` that is a normed algebra over `𝕜`, inversion is `C^n` over `𝕜` away
from `0`, for every `n`. -/
instance instContMDiffInv₀NormedAlgebra {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {n : ℕ∞ω} :
    ContMDiffInv₀ 𝓘(𝕜, 𝕜') n 𝕜' where
  contMDiffAt_inv₀ _ hx := by
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_inv 𝕜 hx

end
