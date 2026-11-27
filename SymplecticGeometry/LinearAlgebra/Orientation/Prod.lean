/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Product orientations with a zero-dimensional factor

A module of rank zero has two orientations of the empty index type, `positiveOrientation` and
its negative. The product orientation (Tau Ceti's `Orientation.prod`) of an orientation `o` of
`E` with the positive orientation of a zero-dimensional module `F` is the image of `o` under the
inclusion `E ≃ E × F`, `v ↦ (v, 0)` (`Orientation.prod_positiveOrientation_right`). When both
factors have rank zero, the product of two orientations is positive exactly when they have the
same sign (`Orientation.prod_eq_positiveOrientation_iff`).
-/

public section

open Module

namespace Orientation

variable {R E F : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F] {m : ℕ}
  [Module.Free R E] [Module.Finite R E] [Module.Free R F] [Module.Finite R F]

/-- The product of an orientation `o` of `E` with the positive orientation of a zero-dimensional
module `F` is the image of `o` under the inclusion `E ≃ E × F`, `v ↦ (v, 0)`. -/
theorem prod_positiveOrientation_right [Unique F] (o : Orientation R E (Fin m))
    (hm : finrank R E = m) (hn : finrank R F = 0) :
    o.prod positiveOrientation hm hn =
      o.map (Fin m) (LinearEquiv.prodUnique (R := R) (M := E) (M₂ := F)).symm := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  have hb : prod b.orientation positiveOrientation hm hn =
      b.orientation.map (Fin m) (LinearEquiv.prodUnique (R := R) (M := E) (M₂ := F)).symm := by
    rw [← c.orientation_isEmpty, prod_basis_orientation, ← Basis.orientation_map]
    congr 1
    refine Basis.eq_of_apply_eq fun k ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ j.elim0) k
    rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Basis.prod_apply, Basis.map_apply]
    exact Prod.ext rfl (Subsingleton.elim _ _)
  rcases b.orientation_eq_or_eq_neg o with rfl | rfl
  · exact hb
  · rw [prod_neg_left, hb, Orientation.map_neg]

/-- For empty index types `Fin m` and `Fin n`, the product of orientations `o` and `p` is the
positive orientation if and only if `o` and `p` are both positive or both negative. -/
theorem prod_eq_positiveOrientation_iff {n : ℕ} [IsEmpty (Fin m)] [IsEmpty (Fin n)]
    [IsEmpty (Fin (m + n))] (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : finrank R E = m) (hn : finrank R F = n) :
    o.prod p hm hn = positiveOrientation ↔
      (o = positiveOrientation ↔ p = positiveOrientation) := by
  have hpp : prod (positiveOrientation : Orientation R E (Fin m))
      (positiveOrientation : Orientation R F (Fin n)) hm hn = positiveOrientation := by
    rw [← (finBasisOfFinrankEq R E hm).orientation_isEmpty,
      ← (finBasisOfFinrankEq R F hn).orientation_isEmpty, prod_basis_orientation,
      Basis.orientation_isEmpty]
  have hE : -(positiveOrientation : Orientation R E (Fin m)) ≠ positiveOrientation :=
    (Module.Ray.ne_neg_self _).symm
  have hF : -(positiveOrientation : Orientation R F (Fin n)) ≠ positiveOrientation :=
    (Module.Ray.ne_neg_self _).symm
  have hEF : -(positiveOrientation : Orientation R (E × F) (Fin (m + n))) ≠
      positiveOrientation := (Module.Ray.ne_neg_self _).symm
  rcases eq_or_eq_neg_of_isEmpty o with rfl | rfl <;>
    rcases eq_or_eq_neg_of_isEmpty p with rfl | rfl
  · simp [hpp]
  · simp [hpp, hF, hEF]
  · simp [hpp, hE, hEF]
  · rw [prod_neg_neg, hpp]
    simp [hE, hF]

end Orientation
