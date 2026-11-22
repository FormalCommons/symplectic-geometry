/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.DirectedUnion
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import SymplecticGeometry.Topology.Sets.Opens
public import SymplecticGeometry.Topology.Sets.Opens.Comap

/-!
# Invariance and vanishing of cohomology with compact supports

A homeomorphism `e : X ≃ₜ Y` induces an isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`, by pulling back along
the proper maps `e` and `e.symm`. The Mayer–Vietoris sequence of an open cover `X = U ∪ V` shows
that `Hᵐ_c(X)` vanishes once `Hᵐ_c(U)`, `Hᵐ_c(V)` and `Hᵐ⁺¹_c(U ∩ V)` do, and the same holds for
the union of two open sets of a Hausdorff space. Since every class of `Hᵐ_c(X)` is extended from a
member of a directed open cover, `Hᵐ_c(X)` also vanishes once it vanishes on every member.

## Main results

* `TopCat.compactSupportCohomologyIsoOfHomeomorph`: the isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`.
* `TopCat.isZero_compactSupportCohomology_iff_of_homeomorph`: vanishing of `Hᵐ_c` is invariant
  under homeomorphisms.
* `TopCat.isZero_compactSupportCohomology_of_isEmpty`: `Hᵐ_c` of the empty space vanishes.
* `TopCat.isZero_compactSupportCohomology_of_sup_eq_top` and
  `TopCat.isZero_compactSupportCohomology_sup`: vanishing of `Hᵐ_c` passes from `U`, `V` and
  `U ∩ V` to `U ∪ V`.
* `TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`: vanishing of `Hᵐ_c` passes from the
  members of a directed open cover to the whole space.

## Implementation notes

For open sets `W ≤ Y` of `X`, `TopCat.isZero_compactSupportCohomology_comap_iff` compares `W` with
`W` read as an open set of `Y` through Mathlib's homeomorphism
`Topology.IsEmbedding.homeomorphOfSubsetRange`. The cover of `U ⊔ V` by `U` and `V`, read as open
sets of `U ⊔ V`, is `TopologicalSpace.Opens.comap_val_sup_comap_val_eq_top`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  Mayer–Vietoris sequence for cohomology with compact supports in the proof of Lemma 3.36, and
  step (B) of the proof of Theorem 3.35 (increasing unions of open sets).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] (R : C) (k : Type v)
  [Ring k] [Linear k C] (N : C)

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`, the pullback along
`e`, with inverse the pullback along `e.symm`. -/
def compactSupportCohomologyIsoOfHomeomorph {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
    Y.compactSupportCohomology R k N m ≅ X.compactSupportCohomology R k N m where
  hom := compactSupportCohomologyMap (ofHom (e : C(X, Y))) e.isProperMap m
  inv := compactSupportCohomologyMap (ofHom (e.symm : C(Y, X))) e.symm.isProperMap m
  hom_inv_id := by
    have h : ofHom (e.symm : C(Y, X)) ≫ ofHom (e : C(X, Y)) = 𝟙 Y := by ext; simp
    rw [← compactSupportCohomologyMap_comp]
    simp only [h, compactSupportCohomologyMap_id]
  inv_hom_id := by
    have h : ofHom (e : C(X, Y)) ≫ ofHom (e.symm : C(Y, X)) = 𝟙 X := by ext; simp
    rw [← compactSupportCohomologyMap_comp]
    simp only [h, compactSupportCohomologyMap_id]

@[simp]
lemma compactSupportCohomologyIsoOfHomeomorph_hom {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
    (compactSupportCohomologyIsoOfHomeomorph R k N e m).hom =
      compactSupportCohomologyMap (ofHom (e : C(X, Y))) e.isProperMap m :=
  (rfl)

@[simp]
lemma compactSupportCohomologyIsoOfHomeomorph_inv {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
    (compactSupportCohomologyIsoOfHomeomorph R k N e m).inv =
      compactSupportCohomologyMap (ofHom (e.symm : C(Y, X))) e.symm.isProperMap m :=
  (rfl)

/-- Cohomology with compact supports vanishes on a space exactly when it vanishes on a homeomorphic
one. -/
theorem isZero_compactSupportCohomology_iff_of_homeomorph {X Y : TopCat.{v}} (e : X ≃ₜ Y)
    (m : ℕ) :
    IsZero (X.compactSupportCohomology R k N m) ↔ IsZero (Y.compactSupportCohomology R k N m) :=
  ⟨fun h ↦ h.of_iso (compactSupportCohomologyIsoOfHomeomorph R k N e m),
    fun h ↦ h.of_iso (compactSupportCohomologyIsoOfHomeomorph R k N e m).symm⟩

/-- **Vanishing of cohomology with compact supports along a cover by two open sets.** If the
Hausdorff space `X` is the union of open sets `U` and `V` with `Hᵐ_c(U) = 0`, `Hᵐ_c(V) = 0` and
`Hᵐ⁺¹_c(U ∩ V) = 0`, then `Hᵐ_c(X) = 0`. -/
theorem isZero_compactSupportCohomology_of_sup_eq_top {X : TopCat.{v}} [T2Space X] {U V : Opens X}
    (hUV : U ⊔ V = ⊤) {m : ℕ}
    (hU : IsZero (((Opens.toTopCat X).obj U).compactSupportCohomology R k N m))
    (hV : IsZero (((Opens.toTopCat X).obj V).compactSupportCohomology R k N m))
    (hW : IsZero (((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k N (m + 1))) :
    IsZero (X.compactSupportCohomology R k N m) :=
  (compactSupportCohomologyMayerVietoris_exact₃ R k N U V hUV m (m + 1)).isZero_X₂
    (((biprod_isZero_iff _ _).2 ⟨hU, hV⟩).eq_of_src _ _) (hW.eq_of_tgt _ _)

/-- Cohomology with compact supports of the empty space vanishes in every degree. -/
theorem isZero_compactSupportCohomology_of_isEmpty (X : TopCat.{v}) [IsEmpty X] (m : ℕ) :
    IsZero (X.compactSupportCohomology R k N m) :=
  (TauCeti.isZero_singularCohomology_of_isEmpty R k N X m).of_iso
    (compactSupportCohomologyIsoOfCompactSpace (R := R) (k := k) (M := N) m)

/-- **Vanishing of cohomology with compact supports along a directed open cover.** If the
Hausdorff space `X` is the union of a monotone family of open sets `U i`, indexed by a directed
preorder, with `Hᵐ_c(U i) = 0` for every `i`, then `Hᵐ_c(X) = 0`. -/
theorem isZero_compactSupportCohomology_of_iSup_eq_top {X : TopCat.{v}} [T2Space X] {ι : Type*}
    [Preorder ι] [IsDirected ι (· ≤ ·)] {U : ι → Opens X} (hU : Monotone U)
    (hcover : ⨆ i, U i = ⊤) {m : ℕ}
    (h : ∀ i, IsZero (((Opens.toTopCat X).obj (U i)).compactSupportCohomology R k N m)) :
    IsZero (X.compactSupportCohomology R k N m) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty X := Opens.isEmpty_of_iSup_eq_top hcover
    exact isZero_compactSupportCohomology_of_isEmpty R k N X m
  refine ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b ↦ ?_⟩
  suffices ∀ x : X.compactSupportCohomology R k N m, x = 0 by rw [this a, this b]
  intro x
  obtain ⟨i, z, rfl⟩ := exists_compactSupportCohomologyExtend_eq_of_iSup_eq_top hU hcover x
  have := ModuleCat.subsingleton_of_isZero (h i)
  rw [Subsingleton.elim z 0, map_zero]

variable {X : Type v} [TopologicalSpace X]

/-- Cohomology with compact supports of an open set `W ≤ Y` of `X` vanishes exactly when that of
`W`, read as an open set of `Y`, does. -/
theorem isZero_compactSupportCohomology_comap_iff {Y W : Opens X} (hWY : W ≤ Y) (m : ℕ) :
    IsZero ((of ↥(Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ W :
        Opens Y)).compactSupportCohomology R k N m) ↔
      IsZero ((of W).compactSupportCohomology R k N m) :=
  isZero_compactSupportCohomology_iff_of_homeomorph R k N
    (X := of ↥(Opens.comap ⟨Subtype.val, continuous_subtypeVal⟩ W : Opens Y)) (Y := of W)
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (Subtype.range_coe.symm ▸ SetLike.coe_subset_coe.2 hWY)) m

/-- **Vanishing of cohomology with compact supports for a union of two open sets.** For open sets
`U` and `V` of a Hausdorff space with `Hᵐ_c(U) = 0`, `Hᵐ_c(V) = 0` and `Hᵐ⁺¹_c(U ∩ V) = 0`, also
`Hᵐ_c(U ∪ V) = 0`. -/
theorem isZero_compactSupportCohomology_sup [T2Space X] {U V : Opens X} {m : ℕ}
    (hU : IsZero ((of U).compactSupportCohomology R k N m))
    (hV : IsZero ((of V).compactSupportCohomology R k N m))
    (hW : IsZero ((of ↥(U ⊓ V)).compactSupportCohomology R k N (m + 1))) :
    IsZero ((of ↥(U ⊔ V)).compactSupportCohomology R k N m) := by
  let i : C(↥(U ⊔ V), X) := ⟨Subtype.val, continuous_subtypeVal⟩
  refine isZero_compactSupportCohomology_of_sup_eq_top R k N
    (X := of ↥(U ⊔ V)) (U := Opens.comap i U) (V := Opens.comap i V) ?_
    ((isZero_compactSupportCohomology_comap_iff R k N le_sup_left m).2 hU)
    ((isZero_compactSupportCohomology_comap_iff R k N le_sup_right m).2 hV) ?_
  · exact Opens.comap_val_sup_comap_val_eq_top U V
  · rw [← map_inf]
    exact (isZero_compactSupportCohomology_comap_iff R k N
      (inf_le_left.trans le_sup_left) (m + 1)).2 hW

end TopCat
