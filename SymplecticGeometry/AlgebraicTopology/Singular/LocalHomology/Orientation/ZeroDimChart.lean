/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
import SymplecticGeometry.Topology.Category.TopPair
import TauCeti.AlgebraicTopology.Singular.ReducedRelative

/-!
# Zero-dimensional local orientations under isomorphisms of pairs

At a point `x` with a zero-dimensional chart, Tau Ceti's
`TauCeti.localOrientationOfZeroDimChart` is the class of `x` in `H₀(M, M ∖ {x}; ℤ)`. An
isomorphism of pairs `(M, M ∖ {x}) ≅ (N, N ∖ {y})` always sends `x` to `y`
(`TopPair.iso_ofSubset_compl_singleton_hom_fst_apply`), so it carries the class of `x`
to the class of `y`. Hence it carries this local orientation at `x` to the one at `y`,
whichever zero-dimensional charts select them (`TauCeti.localOrientationOfZeroDimChart_map`).
This is the rank-zero counterpart of Tau Ceti's `Orientation.localOrientation_map`, where in
positive rank the local orientation is selected by an orientation of the model space. For
instance, through `h.complZeroPairIso`, a continuous linear equivalence `h : P ≃L[ℝ] P'` of
zero-dimensional spaces carries the local orientation of the identity chart of `P` at the
origin to that of `P'`.

## Main results

* `TauCeti.localOrientationOfZeroDimChart_map`: the point-class local orientation of a
  zero-dimensional chart is natural under isomorphisms of pairs.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

open CategoryTheory Module

universe w

namespace TauCeti

/-- Let `x ∈ M` and `y ∈ N` have zero-dimensional charts `φ` and `ψ`. An isomorphism of pairs
`e : (M, M ∖ {x}) ≅ (N, N ∖ {y})` carries the local orientation of `φ` at `x`, the class of
`x`, to the local orientation of `ψ` at `y`. -/
theorem localOrientationOfZeroDimChart_map {M N E F : Type w} [TopologicalSpace M] [T2Space M]
    [TopologicalSpace N] [T2Space N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : OpenPartialHomeomorph M E) (ψ : OpenPartialHomeomorph N F) {x : M} {y : N}
    (hx : x ∈ φ.source) (hy : y ∈ ψ.source) (hE : finrank ℝ E = 0) (hF : finrank ℝ F = 0)
    (e : TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M)) ≅
      TopPair.ofSubset ({y}ᶜ : Set (TopCat.of N))) :
    (localOrientationOfZeroDimChart φ hx hE).map e = localOrientationOfZeroDimChart ψ hy hF := by
  refine Subtype.ext ?_
  rw [LocalOrientation.coe_map, localOrientationOfZeroDimChart_coe,
    localOrientationOfZeroDimChart_coe, localHomologyPointClass_def, localHomologyPointClass_def]
  exact ConcreteCategory.congr_hom (TopPair.singularHomology₀Section_singularHomologyMap _
    (ModuleCat.of ℤ (ULift.{w} ℤ)) e.hom x y
    (TopPair.iso_ofSubset_compl_singleton_hom_fst_apply e)) 1

end TauCeti

end
