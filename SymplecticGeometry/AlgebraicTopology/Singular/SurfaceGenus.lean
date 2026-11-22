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

* `TauCeti.surfaceGenus_sphere_of_finrank_eq_three`: the unit sphere of a real normed space of
  dimension `3` has genus `0`, since its first rational homology vanishes (Tau Ceti's
  `ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ`).
* `TauCeti.surfaceGenus_sphere`: the case of `S²` in `EuclideanSpace ℝ (Fin 3)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace TauCeti

/-- **The 2-sphere has genus `0`.** The unit sphere of a real normed space `E` of dimension `3`
has genus `0`, since its first rational homology vanishes. -/
@[simp]
theorem surfaceGenus_sphere_of_finrank_eq_three {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : Module.finrank ℝ E = 3) :
    surfaceGenus (Metric.sphere (0 : E) 1) = 0 := by
  rw [surfaceGenus_def, ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ
    (ModuleCat.of ℚ ℚ) (d := 2) hE 1]
  simp

/-- The unit sphere `S²` of `ℝ³ = EuclideanSpace ℝ (Fin 3)` has genus `0`, since its first
rational homology vanishes. -/
theorem surfaceGenus_sphere :
    surfaceGenus (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 0 :=
  surfaceGenus_sphere_of_finrank_eq_three finrank_euclideanSpace_fin

end TauCeti

end
