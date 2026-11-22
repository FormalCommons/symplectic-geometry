/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscComplement.BoundaryDegree

/-!
# The boundary class of the complement of coordinate discs

Let `φ i`, `i : ι` finite, be coordinate discs of a compact homologically oriented surface `M`
with pairwise disjoint closed discs, and `X = discComplement φ` the complement of their open
discs, with interior `discComplementInterior φ` oriented by the restriction of `o`. We show that
the boundary class `∂[X, ∂X] ∈ H₁(∂X; ℤ)` is the sum of the classes of the reversed boundary
loops of the discs
(`SymplecticGeometry.sum_map_toCircle_discComplementBoundaryLoop_eq_boundaryClass`). The boundary
loop of `φ i` runs counterclockwise in its chart, so each circle of `∂X` runs clockwise in the
chart of its disc.

This is the hypothesis of `TauCeti.HomologicalOrientation.boundaryDegree_eq_sum_degree` for the
loops `SymplecticGeometry.discComplementBoundaryLoop φ hφ i`.

## Proof

The boundary `∂X` is `ι × S¹` (`SymplecticGeometry.discComplementBoundaryHomeomorph`), read in
`TopCat` as `TopCat.of ι ⊗ TopCat.of Circle` through `TopCat.prodHomeomorphTensorObj`. A class
of `H₁(ι ⊗ S¹; ℤ)` is determined by its images under the fibre retractions
`TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) j`, which keep the `j`-th circle and send
the others to `1` (`Circle.singularHomologyOne_prod_ext`). The image of the boundary class is `-1`
(`boundaryDegree_prodFiberRetraction_comp_discComplementBoundaryHomeomorph_symm`).
The image of the class of the reversed loop of disc `i` is the degree of a reversed loop that is
the identity of the circle if `i = j` (`Circle.degree_symm`), so `-1`, and constant at `1`
otherwise, so `0`.

## Main definitions

* `SymplecticGeometry.discComplementBoundaryLoop`: the reversed boundary loop of one disc, as a
  loop in the boundary of `X`.

## Main results

* `SymplecticGeometry.sum_map_toCircle_discComplementBoundaryLoop_eq_boundaryClass`: the
  boundary class of `X` is the sum of the classes of these loops.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7,
  where the first Chern number of a bundle over a surface is computed from trivializations over
  discs and over their complement.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Proposition 2.6,
  for the first homology of a disjoint union of circles.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology Set Topology Module TauCeti Function

namespace SymplecticGeometry

variable {M : Type} [TopologicalSpace M] [T2Space M] {E : Type} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] {o : HomologicalOrientation M E 2}
  {ι : Type} (φ : ι → CoordinateDisc o) [TopologicalSpace ι] [DiscreteTopology ι]
  (hφ : Pairwise (Disjoint on fun i ↦ (φ i).disc))

/- The type of the loop, its endpoints included, is written with `↥(discComplementInterior φ)` in
place of `↥↑(discComplementInterior φ)`, as in `coe_discComplementBoundaryHomeomorph_apply`:
`simp` puts it in that form by `SetLike.coe_sort_coe` before it tries the `_apply` lemmas below,
which would not match otherwise. The explicit `DFunLike.coe` arguments are needed because a type
ascription leaves the term unchanged. -/
/-- The boundary loop of `φ i`, reversed, as a loop in the boundary of the complement
`discComplement φ` of the open discs, based at the point `(φ i).boundaryCircle 1`: the reverse of
the based loop of the circle `discComplementBoundaryHomeomorph φ hφ (i, ·)`. In `M` it is
`(φ i).boundaryLoop.symm` (`coe_coe_discComplementBoundaryLoop_apply`). -/
def discComplementBoundaryLoop [Finite ι] (i : ι) :
    @Path ↥(@range _ (discComplementInterior φ) (inclusion (discComplementInterior_subset φ)))ᶜ _
      (@DFunLike.coe (ι × Circle ≃ₜ ↥(@range _ (discComplementInterior φ)
        (inclusion (discComplementInterior_subset φ)))ᶜ) _ _ _
        (discComplementBoundaryHomeomorph φ hφ) (i, 1))
      (@DFunLike.coe (ι × Circle ≃ₜ ↥(@range _ (discComplementInterior φ)
        (inclusion (discComplementInterior_subset φ)))ᶜ) _ _ _
        (discComplementBoundaryHomeomorph φ hφ) (i, 1)) :=
  ((discComplementBoundaryHomeomorph φ hφ :
      C(ι × Circle, ↥(range (inclusion (discComplementInterior_subset φ)))ᶜ)).comp
    ⟨fun z ↦ (i, z), by fun_prop⟩).toBasedLoop.symm

@[simp]
theorem discComplementBoundaryLoop_apply [Finite ι] (i : ι) (t : unitInterval) :
    discComplementBoundaryLoop φ hφ i t =
      discComplementBoundaryHomeomorph φ hφ (i, unitToCircle (unitInterval.symm t)) := by
  rw [discComplementBoundaryLoop, Path.symm_apply, Function.comp_apply,
    ContinuousMap.toBasedLoop_apply, ContinuousMap.comp_apply]
  simp

theorem coe_coe_discComplementBoundaryLoop_apply [Finite ι] (i : ι) (t : unitInterval) :
    ((discComplementBoundaryLoop φ hφ i t : discComplement φ) : M) =
      (φ i).boundaryLoop.symm t := by
  simp [CoordinateDisc.boundaryLoop_def]

/-- Read through `discComplementBoundaryHomeomorph`, the retraction onto the `j`-th circle sends
the class of the reversed loop of disc `i` to `-1` if `i = j`, and to `0` otherwise. -/
private lemma singularHomologyOneIso_hom_map_map_discComplementBoundaryLoop [Finite ι]
    [DecidableEq ι] (i j : ι) :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom
            ((TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 j).hom.comp
             ((discComplementBoundaryHomeomorph φ hφ).symm.trans
               (TopCat.prodHomeomorphTensorObj ι Circle) : C(_, _))))).hom
          ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ (ULift.{0} ℤ))).map
              (TopCat.ofHom (discComplementBoundaryLoop φ hφ i).toCircle)).hom
            ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom
              (ULift.up 1)))) =
      if i = j then -1 else 0 := by
  set u : C(↥(range (inclusion (discComplementInterior_subset φ)))ᶜ, Circle) :=
    (TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 j).hom.comp
      ((discComplementBoundaryHomeomorph φ hφ).symm.trans
        (TopCat.prodHomeomorphTensorObj ι Circle) : C(_, _))
  rw [ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one,
    (u.comp (discComplementBoundaryLoop φ hφ i).toCircle).circleDegree_eq_degree
      ((discComplementBoundaryLoop φ hφ i).map u.continuous) fun t ↦ by simp]
  split_ifs with h
  · subst h
    rw [Circle.degree_congr _ (ContinuousMap.id Circle).toBasedLoop.symm fun t ↦ by
        rw [Path.map_coe, Function.comp_apply, discComplementBoundaryLoop_apply, Path.symm_apply,
          Function.comp_apply, ContinuousMap.toBasedLoop_apply]
        simp [u],
      Circle.degree_symm, Circle.degree_toBasedLoop, ContinuousMap.circleDegree_id]
    ext
    simp
  · rw [Circle.degree_congr _ (Path.refl 1) fun t ↦ by
        rw [Path.map_coe, Function.comp_apply, discComplementBoundaryLoop_apply]
        simp [u, h], Circle.degree_refl]
    ext
    simp

/-- **The boundary class of the complement of coordinate discs.** Let `φ i`, `i : ι` finite, be
coordinate discs of a compact surface `M` homologically oriented by `o`, with pairwise disjoint
closed discs. In the boundary of the complement of their open discs, oriented by `o`, the boundary
class is the sum over `i` of the classes of the reversed boundary loops
`discComplementBoundaryLoop φ hφ i`. -/
theorem sum_map_toCircle_discComplementBoundaryLoop_eq_boundaryClass [CompactSpace M] [Fintype ι]
    (hn : finrank ℝ E = 2) :
    ∑ i, (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom (discComplementBoundaryLoop φ hφ i).toCircle)).hom
          ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) =
      (o.comap (discComplementInterior φ).isOpenEmbedding').boundaryClass hn
        (isOpenEmbedding_inclusion_discComplementInterior φ)
        (range_inclusion_discComplementInterior φ hφ) (isCollared_discComplementBoundary φ hφ) := by
  classical
  set h := (discComplementBoundaryHomeomorph φ hφ).symm.trans
    (TopCat.prodHomeomorphTensorObj ι Circle)
  set g : C(↥(range (inclusion (discComplementInterior_subset φ)))ᶜ,
    ↑(TopCat.of ι ⊗ TopCat.of Circle)) := ↑h
  -- push both classes to `ι ⊗ S¹`, where `Circle.singularHomologyOne_prod_ext` applies
  have hinj : Injective (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom g)).hom := by
    refine Function.LeftInverse.injective
      (g := (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (h.symm : C(_, _)))).hom) fun y ↦ ?_
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← TopCat.ofHom_comp,
      Homeomorph.symm_comp_toContinuousMap, TopCat.ofHom_id, CategoryTheory.Functor.map_id,
      ModuleCat.id_apply]
  have hiso : Injective (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom :=
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).toLinearEquiv.injective
  have hcomp (j : ι) (y) : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 j)).hom
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom g)).hom y) =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom
          ((TopCat.prodFiberRetraction (TopCat.of ι) (X := TopCat.of Circle) 1 j).hom.comp
            g))).hom y := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, TopCat.ofHom_comp, TopCat.ofHom_hom]
  refine hinj (Circle.singularHomologyOne_prod_ext fun j ↦ hiso ?_)
  have hb :=
    boundaryDegree_prodFiberRetraction_comp_discComplementBoundaryHomeomorph_symm φ hn hφ j
  rw [HomologicalOrientation.boundaryDegree_def] at hb
  rw [hcomp, hcomp, map_sum, map_sum, Finset.sum_congr rfl fun i _ ↦
      singularHomologyOneIso_hom_map_map_discComplementBoundaryLoop φ hφ i j]
  ext
  rw [hb]
  simp [Finset.sum_ite_eq']

end SymplecticGeometry
