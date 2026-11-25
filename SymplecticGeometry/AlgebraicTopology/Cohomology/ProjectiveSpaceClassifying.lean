/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairCohomology
public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairHom
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.DiskPair

/-!
# Maps into complex projective space that realize a class of degree two

Let `N ≥ 1`, let `ℙ = ℙ ℂ (Fin (N + 1) → ℂ)` and `h = Projectivization.hyperplaneClass` its
hyperplane class. This file constructs maps into `ℙ` that pull `h` back to a prescribed class of
`H²(-; ℤ)`, by induction over the skeleta of a CW complex.

The first step is the `2`-skeleton
(`Projectivization.exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq`): for a
CW complex `C`, a class `b ∈ H²(C; ℤ)` and a point `p ∈ ℙ`, there is a map `f : X² → ℙ` from the
`2`-skeleton, constant at `p` on the `1`-skeleton, with `f^* h` the restriction of `b` to `X²`.

## Main results

* `Projectivization.exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq`: the
  statement above on the `2`-skeleton.

## Proof

Cohomology is taken with chain coefficients and cochain values the unit object `ℤ` of
`ModuleCat ℤ`, through `TopCat.integralCohomologyEquiv`, as in
`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`. The `1`-skeleton `X¹` has
no cohomology in degree `2`, so the restriction of `b` to `X²` lifts to a class
`c ∈ H²(X², X¹)` (`TauCeti.surjective_singularCohomologyπ_skeletonPair`). Fix a lift
`h_p ∈ H²(ℙ, {p})` of `h`. Every class of `H²(D², S¹)` is the pull-back of `h_p` along a map of
pairs `(D², S¹) ⟶ (ℙ, {p})`
(`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`), so `c` is the
pull-back of `h_p` along a map of pairs `F : (X², X¹) ⟶ (ℙ, {p})`, built cell by cell
(`TauCeti.exists_skeletonPair_hom_singularCohomologyMap_eq`). The images of `F^* h_p` and `c` in
`H²(X²)` then give `F^* h = b|X²`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 2.2 and 3.1 (the
  cellular description of `H²(X², X¹)`) and Section 4.3, the proof of Theorem 4.57 (maps into
  Eilenberg–MacLane spaces, built cell by cell).
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti Topology Topology.RelCWComplex
open scoped LinearAlgebra.Projectivization MonoidalCategory

namespace Projectivization

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C] {N : ℕ}

/-- **Classes of degree two on the `2`-skeleton come from complex projective space.** Let `C` be a
CW complex, `N ≠ 0`, `b ∈ H²(C; ℤ)` and `p` a point of `ℙ ℂ (Fin (N + 1) → ℂ)`. There is a
continuous map `f` from the `2`-skeleton `skeletonLT C 3` to `ℙ ℂ (Fin (N + 1) → ℂ)`, equal to `p`
on the `1`-skeleton `skeletonLT C 2`, that pulls the hyperplane class back to the restriction of
`b` to the `2`-skeleton. -/
theorem exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq (hN : N ≠ 0)
    (b : (TopCat.of C).integralCohomology 2) (p : ℙ ℂ (Fin (N + 1) → ℂ)) :
    ∃ f : C(skeletonLT C 3, ℙ ℂ (Fin (N + 1) → ℂ)),
      (∀ x : skeletonLT C 3, (x : X) ∈ skeletonLT C 2 → f x = p) ∧
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (hyperplaneClass (Fin (N + 1) → ℂ)) =
        TopCat.singularCohomologyMap
          (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 3).subset_complex)) 2 b := by
  -- The relative classes below are taken with the `ℤ`-linear structure of
  -- `TopCat.integralCohomologyEquiv`, as in `exists_hom_diskBoundaryPair_singularCohomologyMap_eq`.
  let : Linear ℤ (ModuleCat.{0} ℤ) := ModuleCat.instLinear
  obtain ⟨hp, hhp⟩ := TopPair.surjective_singularCohomologyπ_ofSubset_singleton
    (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ) (M := 𝟙_ (ModuleCat.{0} ℤ))
    (X := TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))) p two_ne_zero
    ((TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
      (hyperplaneClass (Fin (N + 1) → ℂ)))
  obtain ⟨c, hc⟩ := surjective_singularCohomologyπ_skeletonPair C (𝟙_ (ModuleCat.{0} ℤ))
    (𝟙_ (ModuleCat.{0} ℤ)) one_lt_two (TopCat.singularCohomologyMap
      (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 3).subset_complex)) 2
      ((TopCat.of C).integralCohomologyEquiv 2 b))
  obtain ⟨F, hF⟩ := exists_skeletonPair_hom_singularCohomologyMap_eq C hp
    (exists_hom_diskBoundaryPair_singularCohomologyMap_eq hN hp hhp) c
  refine ⟨(TopPair.Hom.fst F).hom, fun x hx ↦ ?_, ?_⟩
  · exact TopPair.mapsTo_range_map_of_hom F ⟨⟨x, hx⟩, rfl⟩
  · apply (TopCat.integralCohomologyEquiv _ 2).injective
    rw [TopCat.integralCohomologyEquiv_naturality, TopCat.integralCohomologyEquiv_naturality,
      ← hc, ← hF, ← hhp]
    exact ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality F 2) hp

end Projectivization

end
