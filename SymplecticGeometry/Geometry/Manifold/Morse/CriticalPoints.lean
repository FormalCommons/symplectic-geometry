/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Jet
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Geometry.Manifold.ContMDiffMap.Chart.Jet
import SymplecticGeometry.Topology.DiscreteSubset
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Finiteness of isolated critical points, and critical points in charts

If each critical point of a `C¹` function `f` in a compact set `K` is isolated among the critical
points of `f`, then `K` holds only finitely many critical points
(`TauCeti.finite_criticalPoints_inter_of_forall_eventually_notMem`), since the critical set is
closed (`TauCeti.isClosed_criticalPoints`). No Morse condition is assumed, so this
serves Morse functions, whose critical points are isolated because they are nondegenerate, as well
as generalized Morse functions, whose degenerate critical points are of birth–death type.

## Implementation notes

The statement is Tau Ceti's
`TauCeti.finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint`, with the
isolation of each critical point as the hypothesis in place of its nondegeneracy. The proof applies
`IsClosed.finite_inter_of_forall_eventually_notMem`, which holds for every closed set, to the
critical set.

The same isolation makes the critical set of a Morse function discrete
(`TauCeti.IsMorse.isDiscrete_criticalPoints`).

On a boundaryless manifold, criticality at the point over `z` in the target of an extended chart
is the vanishing of the first chart jet `ContMDiffMap.chartIteratedFDeriv g a 1` at `z`
(`TauCeti.extChartAt_symm_mem_criticalPoints_iff`), by Tau Ceti's
`TauCeti.mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero`. This is how the open conditions on
critical points of `PositiveDirection.lean` and `ComplexNegativity.lean` are read on jets.
-/

public section

open Set Filter ContMDiffMap
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {f : M → ℝ}

/-- If every critical point of a `C¹` function `f` in a compact set `K` has a punctured
neighbourhood free of critical points, then `K` contains only finitely many critical points
of `f`. Nothing is assumed about the critical points outside `K`. -/
theorem finite_criticalPoints_inter_of_forall_eventually_notMem (hf : ContMDiff I 𝓘(ℝ) 1 f)
    {K : Set M} (hK : IsCompact K)
    (h : ∀ x ∈ criticalPoints I f ∩ K, ∀ᶠ y in 𝓝[≠] x, y ∉ criticalPoints I f) :
    (criticalPoints I f ∩ K).Finite :=
  (isClosed_criticalPoints hf).finite_inter_of_forall_eventually_notMem hK h

/-- The critical points of a Morse function form a discrete set. -/
theorem IsMorse.isDiscrete_criticalPoints (hf : IsMorse I f) : IsDiscrete (criticalPoints I f) :=
  isDiscrete_iff_nhdsNE.2 fun _ hx ↦ inf_principal_eq_bot.2
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      hx).eventually_notMem_criticalPoints

section Chart

omit [IsManifold I 1 M]

variable [I.Boundaryless] {n : WithTop ℕ∞} [IsManifold I n M]

/-- On a boundaryless manifold, the point of `M` over a point `z` of the target of the extended
chart at `a` is a critical point of a `C^n` function `g`, `n ≥ 1`, exactly when the first chart
jet of `g` at `a` vanishes at `z`. -/
theorem extChartAt_symm_mem_criticalPoints_iff (hn : ((1 : ℕ) : WithTop ℕ∞) ≤ n)
    (g : C^n⟮I, M; 𝓘(ℝ), ℝ⟯) (a : M) (z : (extChartAt I a).target) :
    (extChartAt I a).symm z ∈ criticalPoints I g ↔ chartIteratedFDeriv g a 1 hn z = 0 := by
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    (IsManifold.maximalAtlas_subset_of_le (by exact_mod_cast hn)
      (IsManifold.chart_mem_maximalAtlas a)) (extChartAt_symm_mem_chart_source z.property),
    ← extChartAt.eq_1, (extChartAt I a).right_inv z.property, chartIteratedFDeriv_one_eq_zero_iff]

end Chart

end TauCeti

end
