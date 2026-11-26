/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Vanishing

/-!
# Invariance of cohomology with compact supports under homeomorphisms

A homeomorphism `e : X ≃ₜ Y` induces an isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)` by pulling back along the
proper maps `e` and `e.symm`, for any spaces `X` and `Y`. Tau Ceti's
`TopCat.compactSupportCohomologyIsoOfHomeomorph` goes the other way, as the extension along `e`,
and needs both spaces to be Hausdorff; the pullback here does not. So vanishing of `Hᵐ_c` is
invariant under homeomorphisms of arbitrary spaces.

## Main results

* `TopCat.compactSupportCohomologyMapIsoOfHomeomorph`: the isomorphism `Hᵐ_c(Y) ≅ Hᵐ_c(X)`
  given by pulling back along a homeomorphism `X ≃ₜ Y`.
* `TopCat.isZero_compactSupportCohomology_iff_of_homeomorph`: vanishing of `Hᵐ_c` is invariant
  under homeomorphisms.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, cohomology
  with compact supports.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

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

end TopCat
