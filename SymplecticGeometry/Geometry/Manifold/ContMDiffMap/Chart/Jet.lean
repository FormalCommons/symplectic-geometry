/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Jet

/-!
# Chart jets on a boundaryless manifold

Tau Ceti's chart jet `ContMDiffMap.chartIteratedFDeriv f a m hm` differentiates the coordinate
expression `f ∘ (extChartAt I a).symm` of a map `f` into a normed space within the target of the
extended chart. When the model has no boundary, that target is open, so the chart jet is the
ordinary iterated derivative of the coordinate expression
(`ContMDiffMap.chartIteratedFDeriv_eq_iteratedFDeriv`). In orders one and two this reads:
the first chart jet vanishes exactly when the derivative of the coordinate expression does
(`ContMDiffMap.chartIteratedFDeriv_one_eq_zero_iff`), and the second chart jet at a pair of
vectors is the second derivative of the coordinate expression
(`ContMDiffMap.chartIteratedFDeriv_two_apply`).

The file has the name of Tau Ceti's `Geometry/Manifold/ContMDiffMap/Chart/Jet.lean`, which
defines the chart jet, so that the two can join.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1
-/

public section

open Set
open scoped Manifold ContDiff

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- On a boundaryless manifold, the chart jet of order `m` at a point `z` of the chart target is
the ordinary `m`-th derivative of the coordinate expression at `z`. -/
theorem chartIteratedFDeriv_eq_iteratedFDeriv (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (a : M) (m : ℕ)
    (hm : m ≤ n) (z : (extChartAt I a).target) :
    chartIteratedFDeriv f a m hm z = iteratedFDeriv 𝕜 m (f ∘ (extChartAt I a).symm) z := by
  rw [chartIteratedFDeriv_self_target_apply,
    iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target a) z.property]

/-- On a boundaryless manifold, the first chart jet vanishes at a point `z` of the chart target
exactly when the derivative of the coordinate expression vanishes at `z`. -/
theorem chartIteratedFDeriv_one_eq_zero_iff (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (a : M)
    (hn : ((1 : ℕ) : WithTop ℕ∞) ≤ n) (z : (extChartAt I a).target) :
    chartIteratedFDeriv f a 1 hn z = 0 ↔ fderiv 𝕜 (f ∘ (extChartAt I a).symm) z = 0 := by
  rw [chartIteratedFDeriv_eq_iteratedFDeriv, ← norm_eq_zero, ← norm_eq_zero (a := fderiv _ _ _),
    norm_iteratedFDeriv_one]

/-- On a boundaryless manifold, the second chart jet at a point `z` of the chart target, applied
to `![v, w]`, is the second derivative of the coordinate expression at `z`, applied to `v` and
then `w`. -/
theorem chartIteratedFDeriv_two_apply (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (a : M) (hn : 2 ≤ n)
    (z : (extChartAt I a).target) (v w : E) :
    chartIteratedFDeriv f a 2 hn z ![v, w] =
      fderiv 𝕜 (fderiv 𝕜 (f ∘ (extChartAt I a).symm)) z v w := by
  rw [chartIteratedFDeriv_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
  simp

end ContMDiffMap

end
