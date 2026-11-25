/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import SymplecticGeometry.Analysis.Complex.Pseudoconvex

/-!
# Strong pseudoconvexity on a complex manifold persists near a point

For a real function `f` on a complex manifold that is `C²` at `x`, strong `q`-pseudoconvexity at
`x` (Tau Ceti's `TauCeti.IsManifoldStronglyPseudoconvexAt`) holds at all points near `x`, and so
does strict plurisubharmonicity:

* `TauCeti.IsManifoldStronglyPseudoconvexAt.eventually`,
* `TauCeti.IsManifoldStrictlyPlurisubharmonicAt.eventually`.

In the preferred chart at `x` this is `TauCeti.IsStronglyPseudoconvexAt.eventually`, and Tau
Ceti's `isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas` lets that one chart serve all
nearby points.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 2 M]
  {f : M → ℝ} {x : M}

/-- **Strong `q`-pseudoconvexity is an open condition** on a complex manifold. If `f` is real
`C²` at `x` and strongly `q`-pseudoconvex at `x`, then it is strongly `q`-pseudoconvex at every
point near `x`. -/
theorem IsManifoldStronglyPseudoconvexAt.eventually {q : ℕ}
    (h : IsManifoldStronglyPseudoconvexAt E q f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    ∀ᶠ y in 𝓝 x, IsManifoldStronglyPseudoconvexAt E q f y := by
  have : IsManifold 𝓘(ℝ, E) 2 M :=
    IsManifold.restrictScalars ℝ (inferInstance : IsManifold 𝓘(ℂ, E) 2 M)
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, E)) (n := 2) x
  have hx := mem_chart_source E x
  -- Read `f` in the preferred chart at `x`, and use the openness on the model space.
  have h' := ((isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas he hx hf).1 h).eventually
    hf.contDiffAt_comp_chartAt_symm
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf,
    (chartAt E x).open_source.mem_nhds hx, (chartAt E x).continuousAt hx h'] with y hfy hy hy'
  exact (isManifoldStronglyPseudoconvexAt_iff_of_mem_maximalAtlas he hy hfy).2 hy'

/-- **Strict plurisubharmonicity is an open condition** on a complex manifold. If `f` is real
`C²` at `x` and strictly plurisubharmonic at `x`, then it is strictly plurisubharmonic at every
point near `x`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.eventually
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x) (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2 f x) :
    ∀ᶠ y in 𝓝 x, IsManifoldStrictlyPlurisubharmonicAt E f y := by
  simpa only [isManifoldStronglyPseudoconvexAt_zero_iff] using
    (h.isManifoldStronglyPseudoconvexAt 0).eventually hf

end TauCeti

end
