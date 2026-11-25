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
(`TauCeti.finite_criticalPoints_inter_of_forall_eventually_notMem`): the critical set is closed,
so its part in `K` is compact, and it is discrete there. No Morse condition is assumed, so this
serves Morse functions, whose critical points are isolated because they are nondegenerate, as well
as generalized Morse functions, whose degenerate critical points are of birth–death type.

## Implementation notes

The proof is that of Tau Ceti's
`TauCeti.finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint`, with the
isolation of each critical point as the hypothesis in place of its nondegeneracy.
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
  (hK.inter_left (isClosed_criticalPoints hf)).finite <|
    isDiscrete_iff_forall_eventually_notMem.2 fun x hx ↦
      (h x hx).mono fun _ hy hyK ↦ hy hyK.1

end TauCeti

end
