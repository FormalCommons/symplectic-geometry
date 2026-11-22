/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# An open set without boundary points, modelled on the model vector space

Let `W` be a manifold modelled on `I : ModelWithCorners 𝕜 E H`, which may have boundary or
corners, and `U` an open subset of `W` with no boundary points (`BoundarylessManifold I U`), for
instance the interior of `W`. Then `U` is also a manifold modelled on `E` itself, with the
extended charts of `W` as its charts. This file names that manifold and its diffeomorphism
with `U`, so that results about boundaryless manifolds over a vector space apply to `U`.

The construction is Tau Ceti's `TauCeti.BoundarylessModel I U` with its atlas
`TauCeti.BoundarylessModel.interiorChartedSpace`, which Tau Ceti does not make an instance. The
type synonym `TopologicalSpace.Opens.InteriorModel I U` carries that atlas as an instance.

## Main definitions

* `TopologicalSpace.Opens.InteriorModel I U`: the open set `U`, with charts in `E`.
* `TopologicalSpace.Opens.interiorModelHomeomorph I U`: the identity of `U`, as a homeomorphism
  onto `U.InteriorModel I`.
* `TopologicalSpace.Opens.interiorModelDiffeomorph I U n`: the identity of `U`, as a
  `C^n` diffeomorphism from the model `I` to the model `𝓘(𝕜, E)`, at every regularity `n`.

## Main results

* The instances `TopologicalSpace`, `T2Space`, `SecondCountableTopology`, `ChartedSpace E` and
  `IsManifold 𝓘(𝕜, E) n` on `U.InteriorModel I`.
* `TopologicalSpace.Opens.coe_interiorModelHomeomorph`,
  `TopologicalSpace.Opens.coe_interiorModelHomeomorph_symm`: the homeomorphism and its inverse are
  the identity of the common carrier.
* `TopologicalSpace.Opens.coe_interiorModelDiffeomorph`,
  `TopologicalSpace.Opens.coe_interiorModelDiffeomorph_symm`: the diffeomorphism and its inverse
  are the homeomorphism and its inverse, at every regularity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, Proposition 1.17.
-/

public section

noncomputable section

open TauCeti
open scoped Manifold ContDiff

namespace TopologicalSpace.Opens

variable {𝕜 E H W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  [TopologicalSpace W] (U : Opens W)

/-- An open set `U` of a manifold `W` modelled on `I`, to be modelled on the model vector space
`E` of `I`: a copy of `U`, with the same points and topology. When `U` has no boundary points, its
charts are the extended charts of `W`. -/
@[expose] def InteriorModel : Type _ := BoundarylessModel I U

instance : TopologicalSpace (U.InteriorModel I) :=
  inferInstanceAs (TopologicalSpace (BoundarylessModel I U))

instance [T2Space W] : T2Space (U.InteriorModel I) :=
  inferInstanceAs (T2Space U)

instance [SecondCountableTopology W] : SecondCountableTopology (U.InteriorModel I) :=
  inferInstanceAs (SecondCountableTopology U)

/-- The identity of `U`, as a homeomorphism onto its copy `U.InteriorModel I`. -/
def interiorModelHomeomorph : U ≃ₜ U.InteriorModel I :=
  BoundarylessModel.homeomorph I U

/-- The homeomorphism sends each point of `U` to the same point of the copy. -/
theorem coe_interiorModelHomeomorph : ⇑(U.interiorModelHomeomorph I) = id :=
  BoundarylessModel.coe_homeomorph I U

/-- The inverse homeomorphism sends each point of the copy to the same point of `U`. -/
theorem coe_interiorModelHomeomorph_symm : ⇑(U.interiorModelHomeomorph I).symm = id :=
  BoundarylessModel.coe_homeomorph_symm I U

variable [ChartedSpace H W] [IsManifold I 1 W] [BoundarylessManifold I U]

/-- The charts of `U.InteriorModel I` are the extended charts of `W`, with values in `E`. -/
instance : ChartedSpace E (U.InteriorModel I) :=
  BoundarylessModel.interiorChartedSpace I (M := U)

instance {n : ℕ∞ω} [IsManifold I n W] : IsManifold 𝓘(𝕜, E) n (U.InteriorModel I) :=
  BoundarylessModel.instIsManifoldInteriorChartedSpace I (M := U)

/-- The identity of `U`, as a `C^n` diffeomorphism from `U`, modelled on `I`, to
`U.InteriorModel I`, modelled on `E`; this holds at every regularity `n`. -/
def interiorModelDiffeomorph (n : ℕ∞ω) : U ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ U.InteriorModel I :=
  BoundarylessModel.interiorDiffeomorph I (M := U) n

@[simp]
theorem coe_interiorModelDiffeomorph (n : ℕ∞ω) :
    ⇑(U.interiorModelDiffeomorph I n) = U.interiorModelHomeomorph I :=
  BoundarylessModel.coe_interiorDiffeomorph I n

@[simp]
theorem coe_interiorModelDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(U.interiorModelDiffeomorph I n).symm = (U.interiorModelHomeomorph I).symm :=
  BoundarylessModel.coe_interiorDiffeomorph_symm I n

end TopologicalSpace.Opens

end
