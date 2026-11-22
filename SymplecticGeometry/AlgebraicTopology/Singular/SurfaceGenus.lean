/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus

/-!
# The genus of surfaces

Facts about Tau Ceti's `TauCeti.surfaceGenus`, half the rank of the first rational singular
homology, rounded down. The file has the name of Tau Ceti's file on the same subject, so that the
two can merge.

## Main results

* `TauCeti.surfaceGenus_sphere`: the unit sphere `S²` of `EuclideanSpace ℝ (Fin 3)` has genus
  `0`, since `H₁(S²; ℚ) = 0` (Tau Ceti's
  `ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti

/-- **The 2-sphere has genus `0`**: the first rational homology of the unit sphere of
`ℝ³ = EuclideanSpace ℝ (Fin 3)` vanishes. -/
theorem surfaceGenus_sphere :
    surfaceGenus (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 0 := by
  rw [surfaceGenus_def, ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ
    (ModuleCat.of ℚ ℚ) (d := 2) finrank_euclideanSpace_fin 1]
  simp

end TauCeti

end
