/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of `AffineMap.lineMap` on a manifold

For `C^n` maps `f₁ f₂ : M → V` into a normed space over a nontrivially normed field `𝕜` and a
`C^n` map `g : M → 𝕜`, the map `x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)`, that is
`x ↦ f₁ x + g x • (f₂ x - f₁ x)`, is `C^n`.

## Main results

* `ContMDiff.lineMap`: the manifold version of Mathlib's `ContDiff.lineMap`, proved the same way,
  by composing `AffineMap.contDiff_lineMap_uncurry` with the smooth map `(f₁, f₂, g)`.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {n : WithTop ℕ∞} {f₁ f₂ : M → V} {g : M → 𝕜}

/-- For `C^n` maps `f₁ f₂ : M → V` into a normed space over `𝕜` and a `C^n` map `g : M → 𝕜`, the
map `x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)`, that is `x ↦ f₁ x + g x • (f₂ x - f₁ x)`, is
`C^n`. This is the manifold version of Mathlib's `ContDiff.lineMap`. -/
theorem ContMDiff.lineMap (h₁ : ContMDiff I 𝓘(𝕜, V) n f₁) (h₂ : ContMDiff I 𝓘(𝕜, V) n f₂)
    (hg : ContMDiff I 𝓘(𝕜) n g) :
    ContMDiff I 𝓘(𝕜, V) n fun x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x) :=
  AffineMap.contDiff_lineMap_uncurry.comp_contMDiff (h₁.prodMk_space (h₂.prodMk_space hg))

end
