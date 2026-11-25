/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Boundary
public import TauCeti.Topology.CWComplex.Classical.RelativeCWComplex

/-!
# Maps of pairs out of a skeletal pair, cell by cell

Let `C` be a relative CW complex in a Hausdorff space and `P = (Y, B)` a topological pair. A map
`g : Xⁿ⁻¹ ⟶ B` on the `(n - 1)`-skeleton and one map of pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Y, B)` for each
`n`-cell, whose map of boundaries is the attaching map of the cell followed by `g`, glue to a map
of pairs `(Xⁿ, Xⁿ⁻¹) ⟶ (Y, B)` out of the skeletal pair `TauCeti.skeletonPair C n`
(`TauCeti.exists_skeletonPair_hom`). The glued map is `g` on `Xⁿ⁻¹`, and it is the given map of
each cell through the characteristic map `TauCeti.characteristicCellPairMap` of that cell.

For the pair `(Y, {p})` the condition on the boundaries always holds, so any family of maps of
pairs `(Dⁿ, Sⁿ⁻¹) ⟶ (Y, {p})`, one for each `n`-cell, glues to a map of pairs
`(Xⁿ, Xⁿ⁻¹) ⟶ (Y, {p})` (`TauCeti.exists_skeletonPair_hom_ofSubset_singleton`), that is, a map
`Xⁿ → Y` constant at `p` on `Xⁿ⁻¹`.

The ambient map comes from the universal property of the pushout square that attaches the
`n`-cells to `Xⁿ⁻¹` to give `Xⁿ`, Tau Ceti's `TauCeti.isPushout_skeletonObj`.

## Main results

* `TauCeti.exists_skeletonPair_hom`: maps of pairs on the disks of the `n`-cells, compatible along
  the attaching maps with a map on `Xⁿ⁻¹`, glue to a map of pairs out of `(Xⁿ, Xⁿ⁻¹)`.
* `TauCeti.exists_skeletonPair_hom_ofSubset_singleton`: maps of pairs from the disks of the
  `n`-cells to `(Y, {p})` glue to a map of pairs from `(Xⁿ, Xⁿ⁻¹)` to `(Y, {p})`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, the inductive
  construction of a cell complex by attaching `n`-cells to the `(n - 1)`-skeleton.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D]

/-- **Maps of pairs out of a skeletal pair, cell by cell.** Let `P` be a topological pair,
`g : Xⁿ⁻¹ ⟶ P.snd` a map on the `(n - 1)`-skeleton, and `f j : (Dⁿ, Sⁿ⁻¹) ⟶ P` a map of pairs for
each `n`-cell `j` whose map of boundaries is the attaching map of `j` followed by `g`. Then there is
a map of pairs `F : (Xⁿ, Xⁿ⁻¹) ⟶ P` that is `g` on `Xⁿ⁻¹` and is `f j` through the characteristic
map of each `n`-cell `j`. -/
theorem exists_skeletonPair_hom {n : ℕ} {P : TopPair.{w}} (g : skeletonObj C n ⟶ P.snd)
    (f : cell C n → (diskBoundaryPair.{w} n ⟶ P))
    (hf : ∀ j, TopPair.Hom.snd (f j) = cellAttachingMap j ≫ g) :
    ∃ F : skeletonPair C n ⟶ P,
      TopPair.Hom.snd F = g ∧ ∀ j, characteristicCellPairMap C j ≫ F = f j := by
  -- The ambient maps of the `f j`, with the disk as their source.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ _ : cell C n, TopCat.disk.{w} n ⟶ P.fst,
      ∀ j, TopPair.Hom.fst (f j) = ψ j := ⟨_, fun _ ↦ rfl⟩
  have hw : Sigma.desc (cellAttachingMap (C := C) (n := n)) ≫ g ≫ P.map =
      Limits.Sigma.map (fun _ : cell C n ↦ TopCat.diskBoundaryInclusion.{w} n) ≫ Sigma.desc ψ := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc, ← hψ, ← Category.assoc,
      ← hf j]
    exact TopPair.Hom.w (f j)
  let φ := (isPushout_skeletonObj C n).desc (g ≫ P.map) (Sigma.desc ψ) hw
  refine ⟨TopPair.ofHom φ g ?_, rfl, fun j ↦ TopPair.hom_ext_of_fst _ ?_⟩
  · exact ((isPushout_skeletonObj C n).inl_desc _ _ hw).symm
  · rw [TopPair.Hom.fst_comp, characteristicCellPairMap_fst, hψ, ← Sigma.ι_comp_desc cellDiskHom j]
    exact (Sigma.ι _ j ≫= (isPushout_skeletonObj C n).inr_desc _ _ hw).trans
      (Sigma.ι_comp_desc _ j)

/-- **Maps of the disk pairs into `(Y, {p})` glue to a map of the skeletal pair.** For a space `Y`
with a point `p`, maps of pairs `f j : (Dⁿ, Sⁿ⁻¹) ⟶ (Y, {p})`, one for each `n`-cell `j`, glue to
a map of pairs `F : (Xⁿ, Xⁿ⁻¹) ⟶ (Y, {p})`, that is, a map `Xⁿ → Y` constant at `p` on `Xⁿ⁻¹`,
which is `f j` through the characteristic map of each `n`-cell `j`. -/
theorem exists_skeletonPair_hom_ofSubset_singleton {n : ℕ} {Y : TopCat.{w}} (p : Y)
    (f : cell C n → (diskBoundaryPair.{w} n ⟶ TopPair.ofSubset ({p} : Set Y))) :
    ∃ F : skeletonPair C n ⟶ TopPair.ofSubset ({p} : Set Y),
      ∀ j, characteristicCellPairMap C j ≫ F = f j := by
  obtain ⟨F, -, hF⟩ := exists_skeletonPair_hom C
    (TopCat.ofHom (ContinuousMap.const _ (⟨p, rfl⟩ : ({p} : Set Y)))) f fun j ↦ by
      ext x
      exact Subsingleton.elim (α := ({p} : Set Y)) _ _
  exact ⟨F, hF⟩

end TauCeti

end
