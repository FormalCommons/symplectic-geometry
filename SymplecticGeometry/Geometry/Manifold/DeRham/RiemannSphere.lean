/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.Smale
import SymplecticGeometry.Geometry.Manifold.DeRham.Integration.Bijective
import TauCeti.Geometry.Manifold.DeRham.Map
import TauCeti.Geometry.Manifold.DeRham.Sphere

/-!
# The de Rham cohomology of the Riemann sphere

The Riemann sphere `OnePoint ℂ`, with the model `𝓘(ℝ, ℂ)`, is diffeomorphic to the unit sphere
of `ℝ³` (`SymplecticGeometry.roundSphereDiffeomorph`), and a diffeomorphism induces linear
equivalences on de Rham cohomology (`TauCeti.deRhamCohomology.equivOfDiffeomorph`). So Tau Ceti's
computation of the de Rham cohomology of spheres (`TauCeti.rank_deRhamCohomology_sphere`) gives
that of `OnePoint ℂ`: a line in degrees `0` and `2`, and zero in every other degree.

In degrees `0` and `1`, general results of Tau Ceti apply directly: `OnePoint ℂ` is connected
(Mathlib's instance), so `TauCeti.finrank_deRhamCohomology_zero` gives `H⁰`, and it is simply
connected (`TauCeti.simplyConnectedSpace_onePoint_complex`), so
`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace` gives `H¹ = 0`.

In degree `2`, orient `OnePoint ℂ` by its complex structure
(`SymplecticGeometry.complexCurveOrientation`, which is Tau Ceti's
`TauCeti.complexManifoldOrientation` indexed by `Fin 2`). Then a class, or the class of a closed
`2`-form, whose integral is nonzero spans `H²`. This is the case `M = OnePoint ℂ` of
`TauCeti.deRhamCohomology.span_singleton_eq_top_of_integral_ne_zero`, which holds on every
compact, preconnected, boundaryless, Hausdorff oriented manifold.

## Main results

* `TauCeti.rank_deRhamCohomology_onePoint`: `H^k(OnePoint ℂ)` has rank one for `k = 0` and
  `k = 2`, and rank zero otherwise.
* `TauCeti.finrank_deRhamCohomology_onePoint_two`: `H²(OnePoint ℂ)` is a line.
* `TauCeti.span_singleton_eq_top_of_integral_ne_zero_onePoint`,
  `TauCeti.span_singleton_mk_eq_top_of_integralTopForm_ne_zero_onePoint`: a class, or the class
  of a closed `2`-form, with nonzero integral spans `H²(OnePoint ℂ)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 17.21 (the de Rham cohomology of spheres).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5.
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

/-- `H²(OnePoint ℂ)` is one-dimensional. -/
theorem finrank_deRhamCohomology_onePoint_two :
    finrank ℝ (deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) 2) = 1 :=
  finrank_eq_of_rank_eq <| by simp [rank_deRhamCohomology_onePoint]

/-- On the Riemann sphere `OnePoint ℂ`, oriented by its complex structure, a degree-`2` de Rham
class with nonzero integral spans `H²(OnePoint ℂ)`. -/
theorem span_singleton_eq_top_of_integral_ne_zero_onePoint
    {c : deRhamCohomology 𝓘(ℝ, ℂ) (OnePoint ℂ) 2}
    (hc : deRhamCohomology.integral (SymplecticGeometry.complexCurveOrientation ℂ (OnePoint ℂ))
      c ≠ 0) :
    Submodule.span ℝ {c} = ⊤ :=
  deRhamCohomology.span_singleton_eq_top_of_integral_ne_zero _ hc

/-- On the Riemann sphere `OnePoint ℂ`, oriented by its complex structure, the class of a closed
`2`-form with nonzero integral spans `H²(OnePoint ℂ)`. -/
theorem span_singleton_mk_eq_top_of_integralTopForm_ne_zero_onePoint
    (φ : closedForms 𝓘(ℝ, ℂ) (OnePoint ℂ) 2)
    (hφ : integralTopForm (SymplecticGeometry.complexCurveOrientation ℂ (OnePoint ℂ))
      φ.val.val ≠ 0) :
    Submodule.span ℝ {deRhamCohomology.mk 𝓘(ℝ, ℂ) 2 φ} = ⊤ :=
  span_singleton_eq_top_of_integral_ne_zero_onePoint <| by rwa [deRhamCohomology.integral_mk]

end TauCeti

end
