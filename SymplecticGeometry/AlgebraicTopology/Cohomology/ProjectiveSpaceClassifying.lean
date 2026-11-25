/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairCohomology
public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairHom
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.DiskPair
public import TauCeti.AlgebraicTopology.Cellular.Dimension

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

* `Projectivization.exists_skeletonPair_hom_singularCohomologyMap_eq`: every class of
  `H²(X², X¹; ℤ)` is the pull-back of a relative lift `h_p ∈ H²(ℙ, {p}; ℤ)` of `h` along a map of
  pairs `(X², X¹) ⟶ (ℙ, {p})`.
* `Projectivization.exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq`: the
  statement above on the `2`-skeleton.

## Proof

Cohomology is taken with chain coefficients and cochain values the unit object `ℤ` of
`ModuleCat ℤ`, through `TopCat.integralCohomologyEquiv`, as in
`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`. The `1`-skeleton `X¹` is a
CW complex without cells of dimension above `1`, so `H²(X¹) = 0`
(`TauCeti.isZero_singularCohomology_of_isEmpty_cell_gt`), and the restriction of `b` to `X²` lifts
to a class `c ∈ H²(X², X¹)`, since `H²(X², X¹) → H²(X²) → H²(X¹)` is exact. Fix a lift
`h_p ∈ H²(ℙ, {p})` of `h`. For each `2`-cell `j`, the pull-back of `c` along the characteristic
map `(D², S¹) ⟶ (X², X¹)` of `j` is `f_j^* h_p` for some map of pairs
`f_j : (D², S¹) ⟶ (ℙ, {p})`; these glue to a map of pairs `F : (X², X¹) ⟶ (ℙ, {p})`
(`TauCeti.exists_skeletonPair_hom_ofSubset_singleton`). The classes `F^* h_p` and `c` have the same
pull-back along every characteristic map, so they are equal
(`TauCeti.singularCohomology_skeletonPair_ext`), and their images in `H²(X²)` give `F^* h = b|X²`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (the cellular
  description of `H²(X², X¹)`) and Section 4.3, the proof of Theorem 4.57 (maps into
  Eilenberg–MacLane spaces, built cell by cell).
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti Topology Topology.RelCWComplex
open scoped LinearAlgebra.Projectivization MonoidalCategory

namespace Projectivization

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C] {N : ℕ}

section UnitCoefficients

/- The cohomology in this section is that of `TopCat.integralCohomologyEquiv`, with the structure
`ModuleCat.instLinear`; instance search would otherwise find
`CategoryTheory.Linear.preadditiveIntLinear`. -/
attribute [local instance high] ModuleCat.instLinear

/-- Let `C` be a CW complex, `N ≠ 0`, `p` a point of `ℙ ℂ (Fin (N + 1) → ℂ)` and
`hp ∈ H²(ℙ ℂ (Fin (N + 1) → ℂ), {p}; ℤ)` a relative class that maps to the hyperplane class. Every
class `c ∈ H²(X², X¹; ℤ)` of the pair of the `2`-skeleton and the `1`-skeleton of `C` is the
pull-back of `hp` along some map of pairs `(X², X¹) ⟶ (ℙ ℂ (Fin (N + 1) → ℂ), {p})`. -/
theorem exists_skeletonPair_hom_singularCohomologyMap_eq (hN : N ≠ 0)
    {p : ℙ ℂ (Fin (N + 1) → ℂ)}
    (hp : (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomology
      (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2)
    (hhp : (TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))))).singularCohomologyπ
        (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2 hp =
      (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
        (hyperplaneClass (Fin (N + 1) → ℂ)))
    (c : (skeletonPair C 2).singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ (𝟙_ (ModuleCat.{0} ℤ)) 2) :
    ∃ F : skeletonPair C 2 ⟶ TopPair.ofSubset ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ)))),
      TopPair.singularCohomologyMap F 2 hp = c := by
  choose f hf using fun j : cell C 2 ↦ exists_hom_diskBoundaryPair_singularCohomologyMap_eq hN hp
    hhp (TopPair.singularCohomologyMap (characteristicCellPairMap C j) 2 c)
  obtain ⟨F, hF⟩ := exists_skeletonPair_hom_ofSubset_singleton C
    (Y := TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))) p f
  refine ⟨F, singularCohomology_skeletonPair_ext C _ ℤ _ fun j ↦ ?_⟩
  rw [← TopPair.singularCohomologyMap_comp_apply, hF, hf]

end UnitCoefficients

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
          (TopCat.ofHom ⟨Set.inclusion (skeletonLT C 3).subset_complex, by fun_prop⟩) 2 b := by
  -- The relative classes below are taken with the `ℤ`-linear structure of
  -- `TopCat.integralCohomologyEquiv`, as in `exists_skeletonPair_hom_singularCohomologyMap_eq`.
  let : Linear ℤ (ModuleCat.{0} ℤ) := ModuleCat.instLinear
  set P := skeletonPair C 2
  obtain ⟨hp, hhp⟩ := TopPair.surjective_singularCohomologyπ_ofSubset_singleton
    (R := 𝟙_ (ModuleCat.{0} ℤ)) (k := ℤ) (M := 𝟙_ (ModuleCat.{0} ℤ))
    (X := TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))) p two_ne_zero
    ((TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ))).integralCohomologyEquiv 2
      (hyperplaneClass (Fin (N + 1) → ℂ)))
  -- The `1`-skeleton has no cohomology in degree `2`.
  have hP : IsZero (P.snd.singularCohomology (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 2) := by
    refine isZero_singularCohomology_of_isEmpty_cell_gt (skeletonLT C 2 : Set X) _ _ (d := 1)
      (fun m hm ↦ ⟨fun x ↦ ?_⟩) one_lt_two
    have := x.property
    simp only [RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] at this
    exact absurd this (by exact_mod_cast (by omega : ¬ m < 2))
  have hsurj : Function.Surjective (P.singularCohomologyπ (𝟙_ (ModuleCat.{0} ℤ)) ℤ
      (𝟙_ (ModuleCat.{0} ℤ)) 2) := by
    rw [← ModuleCat.epi_iff_surjective]
    exact (P.singularCohomology_exact_space _ ℤ _ 2).epi_f (hP.eq_of_tgt _ _)
  obtain ⟨c, hc⟩ := hsurj (TopCat.singularCohomologyMap
    (TopCat.ofHom ⟨Set.inclusion (skeletonLT C 3).subset_complex, by fun_prop⟩) 2
    ((TopCat.of C).integralCohomologyEquiv 2 b))
  obtain ⟨F, hF⟩ := exists_skeletonPair_hom_singularCohomologyMap_eq hN hp hhp c
  refine ⟨(TopPair.Hom.fst F).hom, fun x hx ↦ ?_, ?_⟩
  · -- The point of `{p}` to which `F` sends `x`.
    let y : ({p} : Set (TopCat.of (ℙ ℂ (Fin (N + 1) → ℂ)))) := TopPair.Hom.snd F ⟨x, hx⟩
    have h : TopPair.Hom.fst F x = y.val :=
      (ConcreteCategory.congr_hom (TopPair.Hom.w F) ⟨x, hx⟩).symm
    exact h.trans y.property
  · apply (TopCat.integralCohomologyEquiv _ 2).injective
    rw [TopCat.integralCohomologyEquiv_naturality, TopCat.integralCohomologyEquiv_naturality,
      ← hc, ← hF, ← hhp]
    exact ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality F 2) hp

end Projectivization

end
