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
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.Orientation

/-!
# The top Chern class of an almost complex manifold and its Euler characteristic

Let `M` be a compact Hausdorff boundaryless smooth manifold modelled on a real normed space `E`
of dimension `2 r + 2`, and `J` a continuous complex structure on its tangent bundle (Tau Ceti's
`TauCeti.Bundle.ContinuousComplexStructure`). The complex orientation `J.orientation` of the
tangent bundle is an orientation of `M`
(`TauCeti.Manifold.Orientation.ofVectorBundleOrientation`), which gives `M` a fundamental class.

* `TauCeti.Bundle.ContinuousComplexStructure.tangentOrientation`: that orientation of `M`, with
  `TauCeti.Bundle.ContinuousComplexStructure.toVectorBundleOrientation_tangentOrientation`, which
  says that its tangent orientations are those of `J.orientation`. For a smooth almost complex
  structure it is Tau Ceti's `TauCeti.SmoothAlmostComplexStructure.orientation`
  (`TauCeti.SmoothAlmostComplexStructure.orientation_eq_tangentOrientation`);
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

`TauCeti.SmoothAlmostComplexStructure.orientation_eq_tangentOrientation` compares the tangent
orientations point by point, as Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.orientationAt_orientation` does.

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

section TangentOrientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  (J : ContinuousComplexStructure E (TangentSpace I : M → Type _)) {k : ℕ}

/-- **The orientation of a manifold given by a complex structure on its tangent bundle.** A
continuous complex structure `J` on the tangent bundle of `M`, with `finrank ℝ E = k`, orients
`M`: this is the orientation of `M` whose tangent orientation at each point is the complex
orientation `J.orientation hk` of the tangent space there. -/
noncomputable def tangentOrientation (hk : finrank ℝ E = k) : Manifold.Orientation I M (Fin k) :=
  Manifold.Orientation.ofVectorBundleOrientation (finBasisOfFinrankEq ℝ E hk).orientation
    ((Fintype.card_fin k).trans hk.symm) (J.orientation hk)

theorem tangentOrientation_def (hk : finrank ℝ E = k) :
    J.tangentOrientation hk =
      Manifold.Orientation.ofVectorBundleOrientation (finBasisOfFinrankEq ℝ E hk).orientation
        ((Fintype.card_fin k).trans hk.symm) (J.orientation hk) :=
  (rfl)

/-- The tangent bundle orientation of `J.tangentOrientation hk` is the complex orientation
`J.orientation hk`. -/
@[simp]
theorem toVectorBundleOrientation_tangentOrientation (hk : finrank ℝ E = k) :
    (J.tangentOrientation hk).toVectorBundleOrientation = J.orientation hk := by
  rw [tangentOrientation_def,
    Manifold.Orientation.toVectorBundleOrientation_ofVectorBundleOrientation]

end TangentOrientation

end TauCeti.Bundle.ContinuousComplexStructure

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- For a smooth almost complex structure `J` on `M`, Tau Ceti's complex orientation
`J.orientation hk` is `tangentOrientation` of `J` seen as a continuous complex structure on the
tangent bundle. -/
theorem orientation_eq_tangentOrientation (J : SmoothAlmostComplexStructure I M) {k : ℕ}
    (hk : finrank ℝ E = k) :
    J.orientation hk = (J.toContMDiff 0).toContinuousComplexStructure.tangentOrientation hk := by
  ext x
  rw [orientationAt_orientation, ← Manifold.Orientation.toVectorBundleOrientation_apply,
    Bundle.ContinuousComplexStructure.toVectorBundleOrientation_tangentOrientation,
    Bundle.ContinuousComplexStructure.orientation_apply,
    ContMDiffAlmostComplexStructure.toContinuousComplexStructure_almostComplexStructureAt]
  -- The pointwise structures of `J` do not depend on the regularity it is viewed with.
  congr 1
  ext v
  rw [ContMDiffAlmostComplexStructure.almostComplexStructureAt_apply, toContMDiff_apply,
    almostComplexStructureAt_apply]

end TauCeti.SmoothAlmostComplexStructure

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
complex model `G`. Orient `M` by `J` (`J.tangentOrientation hE`). Then the top Chern class
`c_{r+1}` of the complex bundle `J.Fiber`, evaluated on the fundamental class of `M`, is the Euler
characteristic `TauCeti.eulerChar M`. A finite CW type of `M`, which `eulerChar` needs, is given
by `TauCeti.FiniteCWType.of_isManifold`. -/
theorem evalFundamentalClass_chernClass_eq_eulerChar
    (J : ContinuousComplexStructure E (TangentSpace I : M → Type)) {r : ℕ}
    (hE : finrank ℝ E = 2 * r + 2) :
    ((J.tangentOrientation hE).toHomologicalOrientation hE).evalFundamentalClass hE
      (ModuleCat.of ℤ ℤ) (ContinuousMap.id M)
      (SymplecticGeometry.Bundle.chernClass G J.Fiber (r + 1)) =
      eulerChar M := by
  have hG : finrank ℂ G = r + 1 := by
    have : finrank ℝ E = 2 * finrank ℂ G := Fact.out
    omega
  rw [SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass hG,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    J.complexEulerClass_eq_eulerClass G hE, ← toVectorBundleOrientation_tangentOrientation J hE,
    Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar]

end TauCeti.Bundle.ContinuousComplexStructure

end
