/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Orientation.ThomClass
public import SymplecticGeometry.Topology.VectorBundle.Thom.SecondCountable
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Basic

/-!
# The Thom isomorphism of the normal bundle of an embedding

Let `f : Z → X` be a smooth embedding of manifolds over finite-dimensional real models, with `X`
Hausdorff and second countable, and let `ν` be its intrinsic normal bundle
`f.isImmersion.NormalSpace · hn`, with model fibre `P` of dimension `r = dim X - dim Z` and the bundle
structure `f.normalSpaceFiberBundle hn hdim`, `f.normalSpaceVectorBundle hn hdim` installed
locally, as in Tau Ceti's `TauCeti.SmoothEmbedding.diagonalNormalOrientation`. A normal orientation
`o` has a canonical Thom class `o.canonicalThomClass hr` and its integral form
`o.intCanonicalThomClass hr` (`Topology/VectorBundle/Orientation/ThomClass.lean`); the normal
bundle needs no class of its own.

This file proves that the Thom map `a ↦ π^*a ⌣ u` of the integral class `u` is bijective in every
degree, `Hᵖ(Z; M) ≅ Hᵖ⁺ʳ(ν, ν ∖ Z; M)` for every `ℤ`-module `M`, `r = 0` included
(`TauCeti.SmoothEmbedding.bijective_thomMap_intCanonicalThomClass`). It is the Thom isomorphism
over a second-countable base, `TauCeti.bijective_thomMap_of_secondCountableTopology`, for which
`Z` is Hausdorff and second countable through the embedding and locally compact as a manifold
over a finite-dimensional model (`Manifold.locallyCompact_of_finiteDimensional`).

## Main results

* `TauCeti.SmoothEmbedding.bijective_thomMap_intCanonicalThomClass`: the Thom isomorphism of the
  normal bundle of an embedding, with integer coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4 (the Thom isomorphism).
* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

open Bundle Module

open scoped ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H G : Type*} {V P Z X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ V G} [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I 1 Z]
  [TopologicalSpace X] [ChartedSpace G X] [IsManifold J 1 X] {n : ℕ∞ω}

/-- **The Thom isomorphism of the normal bundle, with integer coefficients.** For a smooth
embedding `f : Z → X` into a Hausdorff, second-countable manifold, a model fibre `P` of the
codimension and an orientation `o` of the normal bundle `ν`, the Thom map
`Hᵖ(Z; M) ⟶ Hᵐ(ν, ν ∖ Z; M)`, `a ↦ π^*a ⌣ u`, `p + finrank ℝ P = m`, of the canonical Thom class
`u = o.intCanonicalThomClass hr` with coefficients `ℤ` is bijective, for every `ℤ`-module `M`. -/
theorem bijective_thomMap_intCanonicalThomClass [T2Space X] [SecondCountableTopology X]
    (f : SmoothEmbedding I J n Z X) (hn : n ≠ 0)
    (hdim : finrank ℝ P = finrank ℝ V - finrank ℝ E) {r : ℕ}
    (o : letI := f.normalSpaceFiberBundle hn hdim
      letI := f.normalSpaceVectorBundle hn hdim
      VectorBundleOrientation P (f.isImmersion.NormalSpace · hn) (Fin r)) (hr : finrank ℝ P = r)
    (M : ModuleCat.{0} ℤ) (p m : ℕ) (h : p + finrank ℝ P = m) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    Function.Bijective
      (thomMap P (f.isImmersion.NormalSpace · hn) M (finrank ℝ P) p m h (o.intCanonicalThomClass hr)) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space Z := f.isEmbedding.t2Space
  have : SecondCountableTopology Z := f.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace Z := _root_.Manifold.locallyCompact_of_finiteDimensional I
  exact bijective_thomMap_of_secondCountableTopology M p m h
    (o.isThomClass_intCanonicalThomClass hr)

end TauCeti.SmoothEmbedding

end
