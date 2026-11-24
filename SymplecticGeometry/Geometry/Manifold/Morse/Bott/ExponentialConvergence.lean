/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Morse.ExponentialConvergence
public import TauCeti.Geometry.Manifold.Morse.Bott.Lemma

/-!
# Łojasiewicz's gradient inequality at a Morse–Bott critical submanifold

This file is a part of Tau Ceti's
`TauCeti/Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`, copied from Tau Ceti's main
branch at commit `07c8b6b1f5ff5bdab8363e207e59d68eccc82bef`.

Let `i : S → M` be a nondegenerate, or Morse–Bott, critical submanifold of a function `f` on a
boundaryless manifold carrying a Riemannian metric. Its points are critical points of `f`, but
they need not be isolated. This file proves Łojasiewicz's gradient inequality with exponent
`1 / 2` at every point `i s` of such a submanifold, for the Riemannian gradient and any continuous
metric: near `i s`,

`lam * |f y - f (i s)| ≤ ‖grad f y‖ ^ 2`

(`IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_mgradient_sq`, in the namespace
`TauCeti.SmoothEmbedding`). It is the inequality in the preferred chart at `i s`
(`IsNondegenerateCriticalSubmanifold.exists_mul_abs_sub_le_norm_fderiv_comp_extChartAt_symm_sq`),
carried to the gradient by
`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm`, since in that
chart the differential of `f` is bounded by a multiple of the length of its gradient.

The pinned version of Tau Ceti has this theorem too, in its own
`TauCeti/Geometry/Manifold/Morse/Bott/ExponentialConvergence.lean`, but that file imports the
pinned `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`, which declares
`TauCeti.le_comp_maximalIntegralCurve_neg_mgradient`, as does this library's copy of Tau Ceti
main's `GradientFlow.lean`. So the pinned file cannot be imported together with this library's
copies of Łojasiewicz's convergence theorem
(`TauCeti.tendsto_maximalIntegralCurve_neg_mgradient_of_mapClusterPt`). This file can: it takes
`TauCeti.exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm` from this
library's copy of `TauCeti/Geometry/Manifold/Morse/ExponentialConvergence.lean`, at the same
commit.

Changes from Tau Ceti's file: only the theorem listed below is taken, with the namespaces, `open`
lines and `variable` line it needs, and only the imports it uses; the import of
`TauCeti.Geometry.Manifold.Morse.ExponentialConvergence` is replaced by that of this library's
copy of it. This module docstring replaces Tau Ceti's, and keeps the parts of its text that
concern this theorem. The theorem, its docstring and its proof are unchanged.

## Main results

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_mul_abs_sub_le_norm_mgradient_sq`: the Łojasiewicz inequality with exponent `1 / 2`
  near a point of a Morse–Bott critical submanifold, for the Riemannian gradient.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, Éditions du CNRS, Paris, 1963, 87--89.
* A. Banyaga and D. E. Hurtubise, *Lectures on Morse homology*, Kluwer Texts in the Mathematical
  Sciences 29, Kluwer, 2004, Chapter 6 (the Morse–Bott case of the gradient flow).
-/

public section

open Bundle Filter Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S] [ChartedSpace H' S]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {n : ℕ∞ω} {i : SmoothEmbedding J I n S M}

/-- **The Morse–Bott form of Łojasiewicz's gradient inequality on a Riemannian manifold.** If
`i : S → M` is a nondegenerate critical submanifold of `f`, with `i` of class `C²`, then near each
point `i s` the absolute energy difference `|f y - f (i s)|` is bounded by a multiple of the
squared Riemannian length of the gradient of `f` at `y`, for any continuous Riemannian metric. -/
theorem exists_mul_abs_sub_le_norm_mgradient_sq
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (hi : i.IsNondegenerateCriticalSubmanifold f) (hn : 2 ≤ n) (s : S) :
    ∃ lam > 0, ∀ᶠ y in 𝓝 (i s), lam * |f y - f (i s)| ≤ ‖mgradient I f y‖ ^ 2 :=
  exists_mul_abs_sub_le_norm_mgradient_sq_of_fderiv_comp_extChartAt_symm
    (hi.exists_mul_abs_sub_le_norm_fderiv_comp_extChartAt_symm_sq hn s)

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end TauCeti
