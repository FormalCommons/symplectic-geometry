/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Smale
import TauCeti.Geometry.Manifold.DeRham.Sphere

/-!
# The de Rham cohomology of the Riemann sphere

The Riemann sphere `OnePoint ℂ`, with the model `𝓘(ℝ, ℂ)`, is diffeomorphic to the unit sphere
of `ℝ³` (`SymplecticGeometry.roundSphereDiffeomorph`), and a diffeomorphism induces linear
equivalences on de Rham cohomology (`TauCeti.deRhamCohomology.equivOfDiffeomorph`). So Tau Ceti's
computation of the de Rham cohomology of spheres (`TauCeti.rank_deRhamCohomology_sphere`) gives
that of `OnePoint ℂ`: a line in degrees `0` and `2`, and zero in every other degree.

That a class of nonzero integral spans the top degree holds on every compact connected oriented
manifold (`TauCeti.deRhamCohomology.span_singleton_eq_top_of_integral_ne_zero`); it applies to
`OnePoint ℂ` with the orientation `TauCeti.complexManifoldOrientation`.

## Main results

* `TauCeti.rank_deRhamCohomology_onePoint`: `H^k(OnePoint ℂ)` has rank one for `k = 0` and
  `k = 2`, and rank zero otherwise.
* `TauCeti.finrank_deRhamCohomology_onePoint_zero`,
  `TauCeti.subsingleton_deRhamCohomology_onePoint_one`,
  `TauCeti.finrank_deRhamCohomology_onePoint_two`: the cases `k = 0, 1, 2`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 17.21 (the de Rham cohomology of spheres).
-/

public section

open Module
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- **The de Rham cohomology of the Riemann sphere.** The de Rham cohomology `H^k` of `OnePoint ℂ`
has rank one in degrees `0` and `2`, and rank zero, so vanishes, in every other degree. -/
theorem rank_deRhamCohomology_onePoint (k : ℕ) :
    Module.rank ℝ (deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) k) =
      if k = 0 ∨ k = 2 then 1 else 0 := by
  rw [← (deRhamCohomology.equivOfDiffeomorph SymplecticGeometry.roundSphereDiffeomorph k).rank_eq]
  exact rank_deRhamCohomology_sphere two_pos k

/-- `H⁰(OnePoint ℂ)` is one-dimensional. -/
theorem finrank_deRhamCohomology_onePoint_zero :
    finrank ℝ (deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) 0) = 1 :=
  finrank_eq_of_rank_eq <| by simp [rank_deRhamCohomology_onePoint]

/-- `H¹(OnePoint ℂ)` vanishes. -/
theorem subsingleton_deRhamCohomology_onePoint_one :
    Subsingleton (deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) 1) :=
  rank_zero_iff (R := ℝ) |>.mp <| (rank_deRhamCohomology_onePoint 1).trans (by simp)

/-- `H²(OnePoint ℂ)` is one-dimensional. -/
theorem finrank_deRhamCohomology_onePoint_two :
    finrank ℝ (deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) 2) = 1 :=
  finrank_eq_of_rank_eq <| by simp [rank_deRhamCohomology_onePoint]

end TauCeti

end
