/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
public import SymplecticGeometry.Geometry.Manifold.Orientation.EulerCharacteristic
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.Structure

/-!
# The top Chern class of an almost complex manifold and its Euler characteristic

Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on a real normed space `E`
of dimension `2 r + 2`, and `J` a continuous complex structure on its tangent bundle (Tau Ceti's
`TauCeti.Bundle.ContinuousComplexStructure`). The complex orientation `J.orientation` of the
tangent bundle is an orientation of `M`
(`TauCeti.Manifold.Orientation.ofVectorBundleOrientation`), which gives `M` a fundamental class.

* `TauCeti.Bundle.ContinuousComplexStructure.evalFundamentalClass_chernClass_eq_eulerChar`: the
  top Chern class `c_{r+1}` of the complex tangent bundle `J.Fiber`, evaluated on that
  fundamental class, is the Euler characteristic of `M`.

## Proof

The top Chern class is the Euler class of `J.Fiber`
(`SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass`), read in integral
cohomology through `TopCat.uliftIntegralCohomologyIso`, which does not change its evaluation
(`TauCeti.HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom`). It is the
Euler class of the tangent bundle oriented by `J`
(`TauCeti.Bundle.ContinuousComplexStructure.complexEulerClass_eq_eulerClass`), whose evaluation on
the fundamental class is the Euler characteristic
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar`). The argument is
that of `SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`
(`SymplecticGeometry/Geometry/Manifold/Complex/EulerCharacteristic.lean`) for complex manifolds,
with the complex structure on the tangent bundle in place of complex charts.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic) and §14 (the top Chern class of a complex bundle is its Euler
  class).
-/

public section

open Bundle Module
open scoped Manifold ContDiff VectorBundle.ComplexToReal

namespace TauCeti.Bundle.ContinuousComplexStructure

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M] [IsManifold I ∞ M]
  [FiniteCWType M]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- **The top Chern number of a closed almost complex manifold is its Euler characteristic.**
Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on `E`, with
`finrank ℝ E = 2 r + 2`, and `J` a continuous complex structure on its tangent bundle, with
complex model `G`. Orient `M` by `J`. Then the top Chern class `c_{r+1}` of the complex bundle
`J.Fiber`, evaluated on the fundamental class of `M`, is the Euler characteristic
`TauCeti.eulerChar M`. A finite CW type of `M`, which `eulerChar` needs, is given by
`TauCeti.FiniteCWType.of_isManifold`. -/
theorem evalFundamentalClass_chernClass_eq_eulerChar
    (J : ContinuousComplexStructure E (TangentSpace I : M → Type)) {r : ℕ}
    (hE : finrank ℝ E = 2 * r + 2) :
    ((Manifold.Orientation.ofVectorBundleOrientation
        (finBasisOfFinrankEq ℝ E hE).orientation ((Fintype.card_fin _).trans hE.symm)
        (J.orientation hE)).toHomologicalOrientation hE).evalFundamentalClass hE
      (ModuleCat.of ℤ ℤ) (ContinuousMap.id M)
      (SymplecticGeometry.Bundle.chernClass G J.Fiber (r + 1)) =
      eulerChar M := by
  have hG : finrank ℂ G = r + 1 := by
    have : finrank ℝ E = 2 * finrank ℂ G := Fact.out
    omega
  rw [SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass hG,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    J.complexEulerClass_eq_eulerClass G hE]
  conv_rhs => rw [← Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar hE
    (Manifold.Orientation.ofVectorBundleOrientation
        (finBasisOfFinrankEq ℝ E hE).orientation ((Fintype.card_fin _).trans hE.symm)
        (J.orientation hE))]
  rw [Manifold.Orientation.toVectorBundleOrientation_ofVectorBundleOrientation]

end TauCeti.Bundle.ContinuousComplexStructure

end
