/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import SymplecticGeometry.Topology.DiscreteSubset

/-!
# Finiteness of isolated critical points

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
-/

public section

open Set Filter
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

end TauCeti

end
