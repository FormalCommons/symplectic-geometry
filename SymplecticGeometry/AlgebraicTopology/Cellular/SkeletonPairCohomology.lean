/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.AlgebraicTopology.Cellular.Dimension
public import TauCeti.AlgebraicTopology.Cohomology.Additivity.Relative
public import TauCeti.AlgebraicTopology.Cohomology.WeakHomotopyEquivalence
import all TauCeti.AlgebraicTopology.Cellular.Boundary

/-!
# Relative cohomology of consecutive skeleta

For a relative CW complex `C` with skeleta `Xⁿ`, the relative singular cohomology
`Hᵐ(Xⁿ, Xⁿ⁻¹)` is the product, over the `n`-cells `j`, of the relative cohomology of the
Euclidean disk pair `(Dⁿ, Sⁿ⁻¹)`, the projections being the maps induced by the characteristic
maps `TauCeti.characteristicCellPairMap C j` of the single cells. The chain coefficients are a
projective module `R` over a ring and the values any module `M` over it.

The proof has two steps. The characteristic maps of all the `n`-cells,
`∐ⱼ (Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`, induce isomorphisms on relative homology
(`TauCeti.isIso_singularHomologyMap_characteristicPairMap`), hence on relative cohomology, since
the relative chains with projective coefficients are projective
(`TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap`). And relative cohomology
turns the disjoint union of pairs into a product (`TopPair.isLimitFanSingularCohomology`). This
follows the proof of `TauCeti.TopCat.isLimitFanSingularCohomologyPreimageSkeletonPair`, which is
the analogous statement for the preimages of the skeleta under a Serre fibration, with the
identity map in place of the fibration.

For an absolute CW complex, the `n`-skeleton has no cohomology above degree `n`, so the map
`Hᵐ(Xⁿ⁺¹, Xⁿ) → Hᵐ(Xⁿ⁺¹)` from relative to absolute cohomology is onto for `m > n`.

## Main results

* `TauCeti.characteristicCellPairMap_def`: the characteristic map of one cell is the inclusion of
  its summand followed by `TauCeti.characteristicPairMap`.
* `TauCeti.isIso_singularCohomologyMap_characteristicPairMap`: the characteristic maps of the
  `n`-cells induce isomorphisms on relative cohomology, for projective chain coefficients.
* `TauCeti.isLimitFanSingularCohomologySkeletonPair`: the maps induced by the characteristic
  maps of the `n`-cells exhibit `Hᵐ(Xⁿ, Xⁿ⁻¹)` as the product of copies of `Hᵐ(Dⁿ, Sⁿ⁻¹)`.
* `TauCeti.singularCohomology_skeletonPair_ext`: two classes of `Hᵐ(Xⁿ, Xⁿ⁻¹)` with the same
  pull-back along every characteristic map of an `n`-cell are equal.
* `TauCeti.isZero_singularCohomology_skeletonObj_of_lt`: the `n`-skeleton of a CW complex has no
  cohomology in degrees above `n`.
* `TauCeti.surjective_singularCohomologyπ_skeletonPair`: every class of `Hᵐ(Xⁿ⁺¹)` with `m > n`
  comes from `Hᵐ(Xⁿ⁺¹, Xⁿ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe u v

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The characteristic map of one `n`-cell, as a map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`, is the
inclusion of its summand into `∐ⱼ (Dⁿ, Sⁿ⁻¹)`, followed by the characteristic maps of all the
`n`-cells. -/
lemma characteristicCellPairMap_def {n : ℕ} (j : cell C n) :
    characteristicCellPairMap C j =
      TopPair.sigmaι (fun _ : cell C n ↦ diskBoundaryPair.{u} n) j ≫
        (sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n :=
  (rfl)

variable {A : Type v} [Ring A] (R : ModuleCat.{u} A) [Projective R]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{u} A)] (M : ModuleCat.{u} A)

/-- The characteristic maps of the `n`-cells, `∐ⱼ (Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)`, induce isomorphisms
`Hᵐ(Xⁿ, Xⁿ⁻¹; M) ≅ Hᵐ(∐ⱼ (Dⁿ, Sⁿ⁻¹); M)` on relative singular cohomology, for chain coefficients
in a projective module `R`. -/
instance isIso_singularCohomologyMap_characteristicPairMap (n m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (characteristicPairMap C n) m) :=
  TopPair.isIso_singularCohomologyMap_of_isIso_singularHomologyMap _ R k M
    (fun _ ↦ inferInstance) m

/-- The characteristic maps of the `n`-cells, read on Euclidean disk pairs, induce isomorphisms
`Hᵐ(Xⁿ, Xⁿ⁻¹) ≅ Hᵐ(∐ⱼ (Dⁿ, Sⁿ⁻¹))` on relative singular cohomology. -/
private lemma isIso_singularCohomologyMap_sigmaDiskBoundaryPair (n m : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      ((sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n) m) := by
  rw [TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMapIso_hom]
  infer_instance

/-- **The relative cohomology of consecutive skeleta is a product over the cells.** For a relative
CW complex `C` with skeleta `Xⁿ`, the maps induced on relative singular cohomology by the
characteristic maps `(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)` of the `n`-cells exhibit `Hᵐ(Xⁿ, Xⁿ⁻¹; M)` as the
product, over the `n`-cells, of copies of `Hᵐ(Dⁿ, Sⁿ⁻¹; M)`, in every degree `m`, for chain
coefficients in a projective module `R`. -/
def isLimitFanSingularCohomologySkeletonPair (n m : ℕ) :
    IsLimit (Fan.mk ((skeletonPair C n).singularCohomology R k M m)
      fun j : cell C n ↦ TopPair.singularCohomologyMap (characteristicCellPairMap C j) m) :=
  have := isIso_singularCohomologyMap_sigmaDiskBoundaryPair C R k M n m
  IsLimit.ofIsoLimit
    (TopPair.isLimitFanSingularCohomology (fun _ : cell C n ↦ diskBoundaryPair.{u} n)
      (ModuleCat.{u} A) R k M m)
    (Fan.ext (asIso (TopPair.singularCohomologyMap
        ((sigmaDiskBoundaryPairIso (cell C n) n).hom ≫ characteristicPairMap C n) m)).symm
      fun j ↦ by
        rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, fan_mk_proj, fan_mk_proj,
          characteristicCellPairMap_def]
        exact (TopPair.singularCohomologyMap_comp _ _ m).symm)

/-- Two classes of the relative singular cohomology `Hᵐ(Xⁿ, Xⁿ⁻¹; M)` of consecutive skeleta of a
relative CW complex are equal if their pull-backs along the characteristic map
`(Dⁿ, Sⁿ⁻¹) ⟶ (Xⁿ, Xⁿ⁻¹)` of every `n`-cell are equal. -/
theorem singularCohomology_skeletonPair_ext {n m : ℕ}
    {x y : (skeletonPair C n).singularCohomology R k M m}
    (h : ∀ j : cell C n, TopPair.singularCohomologyMap (characteristicCellPairMap C j) m x =
      TopPair.singularCohomologyMap (characteristicCellPairMap C j) m y) :
    x = y :=
  Concrete.isLimit_ext _ (isLimitFanSingularCohomologySkeletonPair C R k M n m) x y
    fun ⟨j⟩ ↦ h j

section Absolute

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] (C : Set Y) [CWComplex C]
  {k : Type v} [CommRing k] [∀ V : ModuleCat.{u} k, HasProjectiveDimensionLE V 1]
  (R M : ModuleCat.{u} k) [Module.Projective k R]

/-- The `n`-skeleton `Xⁿ` of a CW complex has no singular cohomology in degrees `m > n`, over a
hereditary commutative ring `k` and for projective chain coefficients `R`. -/
theorem isZero_singularCohomology_skeletonObj_of_lt {n m : ℕ} (hm : n < m) :
    IsZero ((skeletonObj C (n + 1)).singularCohomology R k M m) := by
  refine isZero_singularCohomology_of_isEmpty_cell_gt (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set Y)
    R M (d := n) (fun j hj ↦ ⟨fun x ↦ ?_⟩) hm
  have := x.property
  simp only [RelCWComplex.skeletonLT_I, Set.mem_ofPred_eq] at this
  exact absurd this (by exact_mod_cast (by omega : ¬ j < n + 1))

/-- For a CW complex with skeleta `Xⁿ` and `m > n`, the map `Hᵐ(Xⁿ⁺¹, Xⁿ) → Hᵐ(Xⁿ⁺¹)` from
relative to absolute singular cohomology is surjective. -/
theorem surjective_singularCohomologyπ_skeletonPair {n m : ℕ} (hm : n < m) :
    Function.Surjective ((skeletonPair C (n + 1)).singularCohomologyπ R k M m) := by
  rw [← ModuleCat.epi_iff_surjective]
  exact ((skeletonPair C (n + 1)).singularCohomology_exact_space R k M m).epi_f
    ((isZero_singularCohomology_skeletonObj_of_lt C R M hm).eq_of_tgt _ _)

end Absolute

end TauCeti

end
