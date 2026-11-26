/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.HomologicalOrientation
public import TauCeti.Geometry.Manifold.Complex.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.AlgebraicTopology.Cohomology.FundamentalClass
import SymplecticGeometry.Geometry.Manifold.Orientation.EulerCharacteristic
import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.EulerClass

/-!
# The top Chern class of a compact complex manifold and its Euler characteristic

Let `M` be a compact Hausdorff smooth complex manifold modelled on `𝓘(ℂ, E)`, with
`finrank ℂ E = r + 1`, oriented by its complex structure. This file proves
`SymplecticGeometry.evalFundamentalClass_chernClass_eq_eulerChar`: `⟨c_{r+1}(TM), [M]⟩ = χ(M)`.

The top Chern class is the Euler class
(`SymplecticGeometry.Bundle.chernClass_finrank_eq_complexEulerClass`), read in integral
cohomology through `TopCat.uliftIntegralCohomologyIso`, which does not change its evaluation
(`TauCeti.HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom`). The Euler
class of the complex tangent bundle is that of the real tangent bundle with the canonical
orientation of `M`, by Tau Ceti's `TauCeti.complexEulerClass_tangentSpace_eq_eulerClass`, and the
evaluation of the latter on the fundamental class is the Euler characteristic
(`TauCeti.Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType`).

For a compact Riemann surface, Tau Ceti's
`TauCeti.evalFundamentalClass_complexEulerClass_tangentSpace_eq_eulerChar` is the case `r = 0`,
stated for the complex Euler class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11 (the Euler class of the tangent bundle evaluated on the fundamental class
  is the Euler characteristic) and §14 (complex bundles are oriented as real bundles, and
  their top Chern class is their Euler class).
* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §11 and §20.
-/

public section

open Bundle Module TauCeti
open scoped Manifold ContDiff TauCeti.ComplexManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

namespace SymplecticGeometry

variable [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℂ, E) ∞ M] [FiniteCWType M]

/-- **The top Chern number of a compact complex manifold is its Euler characteristic.** Let `M` be
a compact Hausdorff smooth complex manifold modelled on `𝓘(ℂ, E)`, of complex dimension
`finrank ℂ E = r + 1`, oriented by its complex structure
(`complexManifoldHomologicalOrientation E M hE`). Then the top Chern class `c_{r+1}(TM)` evaluated
on the fundamental class of `M` (`complexManifoldEvalFundamentalClass E M hE`) is the Euler
characteristic `TauCeti.eulerChar M`. A finite CW type of `M`, which `eulerChar` needs, is given
by `TauCeti.ComplexManifold.finiteCWType`. -/
theorem evalFundamentalClass_chernClass_eq_eulerChar {r : ℕ} (hE : finrank ℂ E = r + 1) :
    complexManifoldEvalFundamentalClass E M hE
        (Bundle.chernClass E (TangentSpace 𝓘(ℂ, E) : M → Type) (r + 1)) =
      eulerChar M := by
  rw [complexManifoldEvalFundamentalClass_def, complexManifoldHomologicalOrientation_def,
    Bundle.chernClass_finrank_eq_complexEulerClass hE,
    HomologicalOrientation.evalFundamentalClass_uliftIntegralCohomologyIso_hom,
    complexEulerClass_tangentSpace_eq_eulerClass hE,
    ← complexManifoldOrientationOfFinrank_def (M := M) hE,
    Manifold.Orientation.evalFundamentalClass_eulerClass_eq_eulerChar_of_finiteCWType]

end SymplecticGeometry

end
