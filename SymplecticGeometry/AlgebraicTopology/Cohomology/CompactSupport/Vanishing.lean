/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Vanishing
public import SymplecticGeometry.Order.SupClosed
import SymplecticGeometry.Topology.Sets.Opens.Basic

/-!
# Invariance and vanishing of cohomology with compact supports

A homeomorphism `e : X ≃ₜ Y` induces an isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)` by pulling back along the
proper maps `e` and `e.symm`, for any spaces `X` and `Y`. Tau Ceti's
`TopCat.compactSupportCohomologyIsoOfHomeomorph` goes the other way, as the extension along `e`,
and needs both spaces to be Hausdorff; the pullback here does not. So vanishing of `Hᵐ_c` is
invariant under homeomorphisms of arbitrary spaces.

Tau Ceti shows that `Hᵐ_c` vanishes on `U ∪ V` once it vanishes on `U` and `V` in degree `m` and
on `U ∩ V` in degree `m + 1` (`TopCat.isZero_compactSupportCohomology_sup`), on the empty space
(`TopCat.isZero_compactSupportCohomology_of_isEmpty`), and on a space covered by a directed family
of open sets on each of which it vanishes (`TopCat.isZero_compactSupportCohomology_of_iSup_eq_top`).
This file combines the three: vanishing above a degree passes from the members of a family of open
sets closed under intersection to its finite unions, and then to the whole space when the family
covers it. This is the induction of Hatcher's Lemma 3.36, for vanishing alone.

## Main results

* `TopCat.compactSupportCohomologyMapIsoOfHomeomorph`: the isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`
  given by pulling back along a homeomorphism `X ≃ₜ Y`.
* `TopCat.isZero_compactSupportCohomology_iff_of_homeomorph`: vanishing of `Hᵐ_c` is invariant
  under homeomorphisms.
* `TopCat.isZero_compactSupportCohomology_comap_iff`: for open sets `W ≤ Y` of `X`, `Hᵐ_c(W)`
  vanishes exactly when `Hᵐ_c` of `W`, read as an open set of `Y`, does.
* `TopCat.isZero_compactSupportCohomology_of_infClosed`: vanishing of `Hᵐ_c` above a degree
  passes from the members of an inf-closed family of open sets that covers the space to the
  whole space.

## Implementation notes

`TopCat.isZero_compactSupportCohomology_comap_iff` compares `W` with `W` read as an open set of `Y`
through Mathlib's homeomorphism `Topology.IsEmbedding.homeomorphOfSubsetRange`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the
  Mayer–Vietoris sequence for cohomology with compact supports in the proof of Lemma 3.36, and
  step (B) of the proof of Theorem 3.35 (increasing unions of open sets), and the induction over
  finite unions in the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] (R : C) (k : Type v)
  [Ring k] [Linear k C] (N : C)

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`, the pullback along
`e`, with inverse the pullback along `e.symm`. Unlike Tau Ceti's
`TopCat.compactSupportCohomologyIsoOfHomeomorph`, the extension along `e` in the opposite
direction, it assumes neither space Hausdorff. -/
def compactSupportCohomologyMapIsoOfHomeomorph {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
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
lemma compactSupportCohomologyMapIsoOfHomeomorph_hom {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
    (compactSupportCohomologyMapIsoOfHomeomorph R k N e m).hom =
      compactSupportCohomologyMap (ofHom (e : C(X, Y))) e.isProperMap m :=
  (rfl)

@[simp]
lemma compactSupportCohomologyMapIsoOfHomeomorph_inv {X Y : TopCat.{v}} (e : X ≃ₜ Y) (m : ℕ) :
    (compactSupportCohomologyMapIsoOfHomeomorph R k N e m).inv =
      compactSupportCohomologyMap (ofHom (e.symm : C(Y, X))) e.symm.isProperMap m :=
  (rfl)

/-- Cohomology with compact supports vanishes on a space exactly when it vanishes on a homeomorphic
one, with no separation axiom on either space. -/
theorem isZero_compactSupportCohomology_iff_of_homeomorph {X Y : TopCat.{v}} (e : X ≃ₜ Y)
    (m : ℕ) :
    IsZero (X.compactSupportCohomology R k N m) ↔ IsZero (Y.compactSupportCohomology R k N m) :=
  ⟨fun h ↦ h.of_iso (compactSupportCohomologyMapIsoOfHomeomorph R k N e m),
    fun h ↦ h.of_iso (compactSupportCohomologyMapIsoOfHomeomorph R k N e m).symm⟩

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

/-- **Vanishing of cohomology with compact supports over an inf-closed family of open sets.** Let
`S` be a family of open sets of a Hausdorff space `X`, closed under intersection, that covers
`X`. If `Hᵐ_c(W) = 0` for every `W ∈ S` and every `m > d`, then `Hᵐ_c(X) = 0` for
every `m > d`. -/
theorem isZero_compactSupportCohomology_of_infClosed [T2Space X] {S : Set (Opens X)}
    (hS : InfClosed S) (hcover : sSup S = ⊤) {d : ℕ}
    (hbase : ∀ W ∈ S, ∀ m, d < m → IsZero ((of W).compactSupportCohomology R k N m))
    {m : ℕ} (hm : d < m) : IsZero ((of X).compactSupportCohomology R k N m) := by
  -- Vanishing passes to the finite unions of members of `S`, by Mayer–Vietoris.
  have hT (s : Finset S) : ∀ m, d < m →
      IsZero ((of ↥(s.sup Subtype.val)).compactSupportCohomology R k N m) := by
    refine hS.finset_sup_induction
      (fun W : Opens X ↦ ∀ m, d < m → IsZero ((of W).compactSupportCohomology R k N m))
      (fun m _ ↦ ?_) hbase (fun V W hV hW hVW m hm ↦ ?_) s
    · exact isZero_compactSupportCohomology_of_isEmpty R k N m
    · exact isZero_compactSupportCohomology_sup (X := of X) (hV m hm) (hW m hm)
        (hVW (m + 1) (by omega))
  -- They form a directed family covering `X`; `(Opens.toTopCat (of X)).obj W` is `of W` by
  -- definition.
  exact isZero_compactSupportCohomology_of_iSup_eq_top (X := of X)
    (U := fun s : Finset S ↦ s.sup Subtype.val) (fun _ _ hst ↦ Finset.sup_mono hst)
    (by rw [SymplecticGeometry.iSup_finset_sup_eq_iSup, ← sSup_eq_iSup', hcover]) fun s ↦ hT s m hm

end TopCat
