/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairCohomology
public import SymplecticGeometry.AlgebraicTopology.Cellular.SkeletonPairHom
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.DiskPair
public import SymplecticGeometry.Topology.ComplexProjectiveSpace.Nullhomotopic
public import TauCeti.AlgebraicTopology.Cellular.Dimension
public import TauCeti.AlgebraicTopology.Cohomology.ConnectedMap
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.Topology.CWComplex.Abstract.CellAttachment
public import TauCeti.Topology.CWComplex.Classical.Extension
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Maps into complex projective space that realize a class of degree two

Let `N` be a natural number, `ℙ = ℙ ℂ (Fin (N + 1) → ℂ)` and `h = Projectivization.hyperplaneClass`
its hyperplane class. This file constructs maps into `ℙ` that pull `h` back to a prescribed class
of `H²(-; ℤ)`, by induction over the skeleta of a CW complex.

The first step is the `2`-skeleton
(`Projectivization.exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq`): for a
CW complex `C`, a class `b ∈ H²(C; ℤ)` and a point `p ∈ ℙ`, there is a map `f : X² → ℙ` from the
`2`-skeleton, constant at `p` on the `1`-skeleton, with `f^* h` the restriction of `b` to `X²`.
When `C` has no cells of dimension above `2N`, such a map extends to all of `C`
(`Projectivization.exists_continuousMap_projectivization_pullback_eq`), and the extension pulls
`h` back to `b` itself.

## Main results

* `Projectivization.exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq`: the
  statement above on the `2`-skeleton.
* `Projectivization.nullhomotopic_cellAttachingMap_comp_of_singularCohomologyMap_eq`: the attaching
  map of a `3`-cell, followed by such a map on the `2`-skeleton, is null-homotopic.
* `Projectivization.exists_continuousMap_projectivization_pullback_eq`: on a CW complex with no
  cells of dimension above `2N`, every class of `H²(-; ℤ)` is `f^* h` for a map `f` to `ℙ`.

## Proof

On the `2`-skeleton, cohomology is taken with chain coefficients and cochain values the unit
object `ℤ` of `ModuleCat ℤ`, through `TopCat.integralCohomologyEquiv`, as in
`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`. The `1`-skeleton `X¹` has
no cohomology in degree `2`, so the restriction of `b` to `X²` lifts to a class
`c ∈ H²(X², X¹)` (`TauCeti.surjective_singularCohomologyπ_skeletonPair`). Fix a lift
`h_p ∈ H²(ℙ, {p})` of `h`. Every class of `H²(D², S¹)` is the pull-back of `h_p` along a map of
pairs `(D², S¹) ⟶ (ℙ, {p})`
(`Projectivization.exists_hom_diskBoundaryPair_singularCohomologyMap_eq`), so `c` is the
pull-back of `h_p` along a map of pairs `F : (X², X¹) ⟶ (ℙ, {p})`, built cell by cell
(`TauCeti.exists_skeletonPair_hom_singularCohomologyMap_eq`). The images of `F^* h_p` and `c` in
`H²(X²)` then give `F^* h = b|X²`.

To extend `f : X² → ℙ` over a `3`-cell, compose it with the attaching map
`TauCeti.cellAttachingMap` of the cell, from the boundary sphere `S²` to `X²`. The composition
pulls `h` back to the pull-back of `b` along `S² → X² ⊆ C`, which is zero since that map extends
over the disk by the characteristic map (`TauCeti.cellAttachingMap_comp_skeletonFunctor_map`,
`TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq`). So the composition is
null-homotopic (`Projectivization.nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero`,
`Projectivization.nullhomotopic_cellAttachingMap_comp_of_singularCohomologyMap_eq`), and `f`
extends over the `3`-cells, which `TauCeti.skeletonAttachCells` attaches along these maps
(`HomotopicalAlgebra.AttachCells.exists_comp_eq_iff_nullhomotopic`). The cells of
dimension `4` to `2N` attach along spheres of dimension `3` to `2N - 1`, from which every map to
`ℙ` is null-homotopic (`Projectivization.nullhomotopic_of_three_le_of_le`), so Tau Ceti's
extension lemma `TauCeti.exists_extension_skeletonLT_of_nullhomotopic` extends the map to all of
`C`. Restriction from `C` to `X²` is injective on `H²`, since the inclusion `X² ⊆ C` is
`2`-connected (`TauCeti.isNConnected_inclusion_skeletonLT`,
`ContinuousMap.IsNConnected.mono_singularCohomologyMap`), so the extension pulls `h` back to `b`.
When `N = 0`, `C` has only `0`-cells and `H²(C; ℤ)` vanishes.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 2.2 and 3.1 (the
  cellular description of `H²(X², X¹)`) and Section 4.3, the proof of Theorem 4.57 (maps into
  Eilenberg–MacLane spaces, built cell by cell).
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module TauCeti Topology Topology.RelCWComplex
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

/-- **Maps that realize a class of degree two on the `2`-skeleton kill the attaching maps of the
`3`-cells.** Let `C` be a CW complex, `b ∈ H²(C; ℤ)` and `f` a continuous map from the
`2`-skeleton `skeletonLT C 3` to `ℙ ℂ (Fin (N + 1) → ℂ)` that pulls the hyperplane class back to
the restriction of `b` to the `2`-skeleton. Then the attaching map `TauCeti.cellAttachingMap j`
of each `3`-cell `j`, followed by `f`, is null-homotopic. -/
theorem nullhomotopic_cellAttachingMap_comp_of_singularCohomologyMap_eq
    (b : (TopCat.of C).integralCohomology 2) (f : C(skeletonLT C 3, ℙ ℂ (Fin (N + 1) → ℂ)))
    (hf : TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (hyperplaneClass (Fin (N + 1) → ℂ)) =
      TopCat.singularCohomologyMap
        (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 3).subset_complex)) 2 b)
    (j : cell C 3) : (cellAttachingMap j ≫ TopCat.ofHom f).hom.Nullhomotopic := by
  have hV : finrank ℂ (Fin (N + 1) → ℂ) = N + 1 := by simp
  -- The attaching map of `j` followed by `X² ⊆ C` extends over the disk by the characteristic
  -- map, so it is null-homotopic and pulls `b` back to zero.
  have ha : (cellAttachingMap j ≫
      TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 3).subset_complex)).hom.Nullhomotopic :=
    (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq _).2
      ⟨cellDiskHom j ≫ TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C _).subset_complex), by
        rw [← reassoc_of% (cellAttachingMap_comp_skeletonFunctor_map j)]
        rw [← TopCat.ofHom_comp, ContinuousMap.inclusion_comp_inclusion]⟩
  refine (nullhomotopic_iff_singularCohomologyMap_hyperplaneClass_eq_zero hV _).2 ?_
  rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hf,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    TopCat.singularCohomologyMap_eq_zero_of_nullhomotopic ha two_ne_zero]
  simp

/-- **Classes of degree two come from complex projective space.** Let `C` be a CW complex with no
cells of dimension above `2N`. Every class `b ∈ H²(C; ℤ)` is the pull-back `f^* h` of the
hyperplane class `h` of `ℙ ℂ (Fin (N + 1) → ℂ)` along some continuous map
`f : C → ℙ ℂ (Fin (N + 1) → ℂ)`. -/
theorem exists_continuousMap_projectivization_pullback_eq
    (hC : ∀ m, 2 * N < m → IsEmpty (cell C m)) (b : (TopCat.of C).integralCohomology 2) :
    ∃ f : C(C, ℙ ℂ (Fin (N + 1) → ℂ)),
      TopCat.singularCohomologyMap (TopCat.ofHom f) 2 (hyperplaneClass (Fin (N + 1) → ℂ)) = b := by
  have hV : finrank ℂ (Fin (N + 1) → ℂ) = N + 1 := by simp
  obtain ⟨p⟩ : Nonempty (ℙ ℂ (Fin (N + 1) → ℂ)) := inferInstance
  rcases eq_or_ne N 0 with rfl | hN
  · -- `C` has only `0`-cells, so `H²(C; ℤ)` vanishes.
    have hz : IsZero ((TopCat.of C).integralCohomology 2) :=
      isZero_singularCohomology_of_isEmpty_cell_gt C _ _ hC (by omega)
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨ContinuousMap.const _ p, Subsingleton.elim _ _⟩
  obtain ⟨f₂, -, hf₂⟩ :=
    exists_continuousMap_skeletonLT_singularCohomologyMap_hyperplaneClass_eq hN b p
  -- `f₂` extends over the `3`-cells, whose attaching maps it sends to null-homotopic maps.
  obtain ⟨F₃, hF₃⟩ := ((skeletonAttachCells C 3).exists_comp_eq_iff_nullhomotopic
    (TopCat.ofHom f₂)).2 fun j ↦ by
      simpa [skeletonAttachCells] using
        nullhomotopic_cellAttachingMap_comp_of_singularCohomologyMap_eq b f₂ hf₂ j
  -- The higher cells attach along spheres of dimension `3` to `2N - 1`, into `ℙ` null-homotopic.
  obtain ⟨F, hF⟩ := TauCeti.exists_extension_skeletonLT_of_nullhomotopic (C := C) 4
    (fun m hm hcell g ↦ by
      have hm' : m ≤ 2 * N := by
        by_contra hlt
        exact (hC m (by omega)).false hcell.some
      exact nullhomotopic_of_three_le_of_le (k := m - 1) hV (by simp; omega) (by omega)
        (by omega) g) F₃.hom
  refine ⟨F, ?_⟩
  -- `F` restricts to `f₂` on the `2`-skeleton, where restriction is injective on `H²`.
  have hFf₂ : F.comp (ContinuousMap.inclusion (skeletonLT C 3).subset_complex) = f₂ := by
    ext x
    exact (hF ⟨x, _⟩).trans (ConcreteCategory.congr_hom hF₃ x)
  -- Restriction to the `2`-skeleton is injective on `H²`, since the inclusion is `2`-connected.
  have hinj : Function.Injective fun x : (TopCat.of C).integralCohomology 2 ↦
      @TopCat.singularCohomologyMap _ _ _ _ (𝟙_ (ModuleCat.{0} ℤ)) ℤ _ ModuleCat.instLinear
        (𝟙_ (ModuleCat.{0} ℤ)) _ _
        (TopCat.ofHom (ContinuousMap.inclusion (skeletonLT C 3).subset_complex)) 2
        ((TopCat.of C).integralCohomologyEquiv 2 x) := by
    -- The `ℤ`-linear structure of `TopCat.integralCohomologyEquiv`, as in the proof above.
    let : Linear ℤ (ModuleCat.{0} ℤ) := ModuleCat.instLinear
    have := (isNConnected_inclusion_skeletonLT (n := 2) (C := C)
      (A := (skeletonLT C 3 : Set X)) (by norm_num)
      (skeletonLT C 3).subset_complex).mono_singularCohomologyMap ℤ ℤ (𝟙_ (ModuleCat.{0} ℤ))
      (m := 2) le_rfl
    exact ((ModuleCat.mono_iff_injective _).1 this).comp
      ((TopCat.of C).integralCohomologyEquiv 2).injective
  apply hinj
  simp only
  rw [← TopCat.integralCohomologyEquiv_naturality, ← TopCat.integralCohomologyEquiv_naturality,
    ← hf₂, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, ← TopCat.ofHom_comp,
    hFf₂]

end Projectivization

end
