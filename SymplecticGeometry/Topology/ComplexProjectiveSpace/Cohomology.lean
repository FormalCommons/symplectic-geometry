/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Homeomorph
public import TauCeti.AlgebraicTopology.Cellular.ComplexProjective.Cohomology
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup

/-!
# Vanishing of the integral cohomology of complex projective spaces

For a Hausdorff complex topological vector space `V` with `finrank ℂ V = n + 1`, the integral
cohomology `Hᵐ(ℙ ℂ V; ℤ)` vanishes above degree `2n`
(`Projectivization.isZero_integralCohomology_of_lt`) and in odd degrees
(`Projectivization.isZero_integralCohomology_of_odd`). These are Tau Ceti's
`TauCeti.ComplexProjectiveSpace.isZero_singularCohomology_of_lt` and
`TauCeti.ComplexProjectiveSpace.isZero_singularCohomology_of_odd`, carried along
`Projectivization.complexProjectiveSpaceHomeomorph`.
-/

public section

open CategoryTheory Limits Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {V : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] {n : ℕ}

/-- The integral cohomology of `ℙ ℂ V`, for `finrank ℂ V = n + 1`, vanishes above degree `2n`. -/
theorem isZero_integralCohomology_of_lt (hV : finrank ℂ V = n + 1) {m : ℕ} (hm : 2 * n < m) :
    IsZero ((TopCat.of (ℙ ℂ V)).integralCohomology m) :=
  (ComplexProjectiveSpace.isZero_singularCohomology_of_lt _ _ hm).of_iso
    ((singularCohomologyFunctor _ ℤ _ m).mapIso
      (TopCat.isoOfHomeo (complexProjectiveSpaceHomeomorph hV)).op)

/-- The integral cohomology of `ℙ ℂ V`, for `finrank ℂ V = n + 1`, vanishes in odd degrees. -/
theorem isZero_integralCohomology_of_odd (hV : finrank ℂ V = n + 1) {m : ℕ} (hm : Odd m) :
    IsZero ((TopCat.of (ℙ ℂ V)).integralCohomology m) :=
  (ComplexProjectiveSpace.isZero_singularCohomology_of_odd _ _ hm).of_iso
    ((singularCohomologyFunctor _ ℤ _ m).mapIso
      (TopCat.isoOfHomeo (complexProjectiveSpaceHomeomorph hV)).op)

end Projectivization

end
