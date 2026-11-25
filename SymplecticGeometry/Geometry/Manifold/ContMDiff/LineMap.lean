/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of `AffineMap.lineMap` on a manifold

For `C^n` maps `f₁ f₂ : M → V` into a normed space over a nontrivially normed field `𝕜` and a
`C^n` map `g : M → 𝕜`, the map `x ↦ AffineMap.lineMap (f₁ x) (f₂ x) (g x)`, that is
`x ↦ f₁ x + g x • (f₂ x - f₁ x)`, is `C^n`. Composing with it, a map from a real normed
space to a manifold that is `C^n` on a set containing a segment is `C^n` along the segment.

## Main results

* `ContMDiff.lineMap`: the manifold version of Mathlib's `ContDiff.lineMap`.
* `ContMDiffOn.comp_lineMap`: for `g : W → M` that is `C^n` on a set containing the segment from
  `p` to `q`, the curve `t ↦ g (AffineMap.lineMap p q t)` is `C^n` on `[0, 1]`. For the inverse
  of a chart, smooth on the chart's target, this is the preimage of a segment of the target.
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

section Segment

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A map `g` from a real normed space `W` to a manifold that is `C^n` on a set `s` containing
the segment from `p` to `q` is `C^n` along it: the curve `t ↦ g (AffineMap.lineMap p q t)`, that
is `t ↦ g (p + t • (q - p))`, is `C^n` on `[0, 1]`. -/
theorem ContMDiffOn.comp_lineMap {g : W → M'} {s : Set W} (hg : ContMDiffOn 𝓘(ℝ, W) I' n g s)
    {p q : W} (hpq : segment ℝ p q ⊆ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I' n (fun t : ℝ ↦ g (AffineMap.lineMap p q t)) (Set.Icc 0 1) :=
  hg.comp (AffineMap.contDiff_lineMap p q).contMDiff.contMDiffOn
    fun _ ht ↦ hpq (lineMap_mem_segment ℝ p q ht)

end Segment

end
