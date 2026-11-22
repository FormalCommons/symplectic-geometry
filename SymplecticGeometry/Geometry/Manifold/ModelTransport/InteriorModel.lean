/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ModelTransport.Interior

/-!
# A manifold without boundary points, modelled on the model vector space

Let `M` be a manifold modelled on `I : ModelWithCorners 𝕜 E H`, a model which may have boundary
or corners, and suppose that `M` has no boundary points (`BoundarylessManifold I M`); for instance
`M` is the interior of a manifold with boundary, as an open subset. Then `M` is also a manifold
modelled on `E` itself, with the extended charts of `M` as its charts. This file names that
manifold and its diffeomorphism with `M`, so that results about boundaryless manifolds over a
vector space apply to `M`.

The construction is Tau Ceti's `TauCeti.BoundarylessModel I M` with its atlas
`TauCeti.BoundarylessModel.interiorChartedSpace`, which Tau Ceti does not make an instance. The
type synonym `SymplecticGeometry.InteriorModel I M` carries that atlas as an instance.

## Main definitions

* `SymplecticGeometry.InteriorModel I M`: the space `M`, with charts in `E`.
* `SymplecticGeometry.interiorModelHomeomorph I M`: the identity of `M`, as a homeomorphism onto
  `InteriorModel I M`.
* `SymplecticGeometry.interiorModelDiffeomorph I M n`: the identity of `M`, as a `C^n`
  diffeomorphism from the model `I` to the model `𝓘(𝕜, E)`, at every regularity `n`.

## Main results

* The instances `TopologicalSpace`, `T2Space`, `SecondCountableTopology`, `PreconnectedSpace`,
  `ConnectedSpace`, `ChartedSpace E` and `IsManifold 𝓘(𝕜, E) n` on `InteriorModel I M`.
* `SymplecticGeometry.coe_interiorModelHomeomorph`,
  `SymplecticGeometry.coe_interiorModelHomeomorph_symm`: the homeomorphism and its inverse are
  the identity of the common carrier.
* `SymplecticGeometry.coe_interiorModelDiffeomorph`,
  `SymplecticGeometry.coe_interiorModelDiffeomorph_symm`: the diffeomorphism and its inverse
  are the homeomorphism and its inverse, at every regularity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, Proposition 1.17.
-/

public section

noncomputable section

open TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type*) [TopologicalSpace M]

/-- A space `M` charted on the model `I`, to be modelled on the model vector space `E` of `I`: a
copy of `M`, with the same points and topology. When `M` is a manifold without boundary points,
its charts are the extended charts of `M`. -/
@[expose] def InteriorModel : Type _ := BoundarylessModel I M

instance : TopologicalSpace (InteriorModel I M) :=
  inferInstanceAs (TopologicalSpace (BoundarylessModel I M))

instance [T2Space M] : T2Space (InteriorModel I M) :=
  inferInstanceAs (T2Space M)

instance [SecondCountableTopology M] : SecondCountableTopology (InteriorModel I M) :=
  inferInstanceAs (SecondCountableTopology M)

instance [PreconnectedSpace M] : PreconnectedSpace (InteriorModel I M) :=
  inferInstanceAs (PreconnectedSpace M)

instance [ConnectedSpace M] : ConnectedSpace (InteriorModel I M) :=
  inferInstanceAs (ConnectedSpace M)

/-- The identity of `M`, as a homeomorphism onto its copy `InteriorModel I M`. -/
def interiorModelHomeomorph : M ≃ₜ InteriorModel I M :=
  BoundarylessModel.homeomorph I M

/-- The homeomorphism sends each point of `M` to the same point of the copy. -/
theorem coe_interiorModelHomeomorph : ⇑(interiorModelHomeomorph I M) = id :=
  BoundarylessModel.coe_homeomorph I M

/-- The inverse homeomorphism sends each point of the copy to the same point of `M`. -/
theorem coe_interiorModelHomeomorph_symm : ⇑(interiorModelHomeomorph I M).symm = id :=
  BoundarylessModel.coe_homeomorph_symm I M

variable [ChartedSpace H M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- The charts of `InteriorModel I M` are the extended charts of `M`, with values in `E`. -/
instance : ChartedSpace E (InteriorModel I M) :=
  BoundarylessModel.interiorChartedSpace I (M := M)

instance {n : ℕ∞ω} [IsManifold I n M] : IsManifold 𝓘(𝕜, E) n (InteriorModel I M) :=
  BoundarylessModel.instIsManifoldInteriorChartedSpace I (M := M)

/-- The identity of `M`, as a `C^n` diffeomorphism from `M`, modelled on `I`, to
`InteriorModel I M`, modelled on `E`; this holds at every regularity `n`. -/
def interiorModelDiffeomorph (n : ℕ∞ω) : M ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ InteriorModel I M :=
  BoundarylessModel.interiorDiffeomorph I (M := M) n

@[simp]
theorem coe_interiorModelDiffeomorph (n : ℕ∞ω) :
    ⇑(interiorModelDiffeomorph I M n) = interiorModelHomeomorph I M :=
  BoundarylessModel.coe_interiorDiffeomorph I n

@[simp]
theorem coe_interiorModelDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(interiorModelDiffeomorph I M n).symm = (interiorModelHomeomorph I M).symm :=
  BoundarylessModel.coe_interiorDiffeomorph_symm I n

end SymplecticGeometry

end
