/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
import TauCeti.AlgebraicTopology.Singular.ReducedRelative

/-!
# Zero-dimensional local orientations under linear equivalences

A real normed space `P` of dimension zero is a point, and Tau Ceti's
`TauCeti.localOrientationOfZeroDimChart` of its identity chart is the class of the origin in
`H₀(P, P ∖ {0}; ℤ)`. A continuous linear equivalence `h : P ≃L[ℝ] P'` sends the origin to the
origin, so transport along the isomorphism of pairs `h.complZeroPairIso` carries this local
orientation of `P` to that of `P'`
(`TauCeti.localOrientationOfZeroDimChart_refl_map`). This is the rank-zero counterpart of Tau
Ceti's `Orientation.localOrientation_map`, where in positive rank the local orientation is
selected by an orientation of the space.

## Main results

* `TauCeti.localOrientationOfZeroDimChart_refl_map`: the point-class local orientation of the
  identity chart is natural under continuous linear equivalences.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Module

universe w

namespace TauCeti

variable {P P' : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P'] [FiniteDimensional ℝ P']

/-- A continuous linear equivalence `h : P ≃L[ℝ] P'` between zero-dimensional real normed spaces
carries the local orientation of the identity chart of `P` at the origin, the class of the
origin, to that of `P'`. -/
theorem localOrientationOfZeroDimChart_refl_map (h : P ≃L[ℝ] P') (hP : finrank ℝ P = 0)
    (hP' : finrank ℝ P' = 0) :
    (localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P)
        (OpenPartialHomeomorph.mem_refl_source _) hP).map h.complZeroPairIso =
      localOrientationOfZeroDimChart (OpenPartialHomeomorph.refl P')
        (OpenPartialHomeomorph.mem_refl_source _) hP' := by
  refine Subtype.ext ?_
  rw [LocalOrientation.coe_map, localOrientationOfZeroDimChart_coe,
    localOrientationOfZeroDimChart_coe, localHomologyPointClass_def, localHomologyPointClass_def]
  exact ConcreteCategory.congr_hom (TopPair.singularHomology₀Section_singularHomologyMap _
    (ModuleCat.of ℤ (ULift.{w} ℤ)) h.complZeroPairIso.hom (0 : P) (0 : P')
    ((ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply h 0).trans h.map_zero)) 1

end TauCeti

end
