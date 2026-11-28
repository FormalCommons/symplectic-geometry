/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Product orientations: zero-dimensional factors and block-triangular maps

A module of rank zero has two orientations of the empty index type, `positiveOrientation` and
its negative. The product orientation (Tau Ceti's `Orientation.prod`) of an orientation `o` of
`E` with the positive orientation of a zero-dimensional module `F` is the image of `o` under the
inclusion `E ≃ E × F`, `v ↦ (v, 0)` (`Orientation.prod_positiveOrientation_right`). This is the
case of Tau Ceti's `Orientation.reindex_prod_of_right_eq_zero` where the second orientation is
the positive one, so that no sign and no reindexing appear. When both
factors have rank zero, the product of two orientations is positive exactly when they have the
same sign (`Orientation.prod_eq_positiveOrientation_iff`).

Over a linearly ordered field, a linear equivalence `f : E × F ≃ U × W` that is block lower
triangular, sending `(x, 0)` to `(e x, *)` and `(0, y)` to `(0, e' y)`, carries the product of
orientations `o` and `p` to the product of their images under `e` and `e'`
(`Orientation.map_prod_of_blockTriangular`). The proof factors `f` as `e × e'` followed by a
shear, and applies Tau Ceti's `Orientation.map_prod` and `Orientation.map_skewProd_refl`. For a
splitting `V = H ⊕ N` this gives `Orientation.map_map_prodEquivOfIsCompl_prod`: an equivalence
`D : V ≃ U × W` that maps `N` into `{0} × W` sends the orientation of `V` induced by orientations
of `H` and `N` to the product of their images in `U` and `W`.
-/

public section

open Module

namespace Orientation

section CommRing

variable {R E F : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F] {m : ℕ}
  [Module.Free R E] [Module.Finite R E] [Module.Free R F] [Module.Finite R F]

/-- The product of an orientation `o` of `E` with the positive orientation of a zero-dimensional
module `F` is the image of `o` under the inclusion `E ≃ E × F`, `v ↦ (v, 0)`. -/
theorem prod_positiveOrientation_right [Unique F] (o : Orientation R E (Fin m))
    (hm : finrank R E = m) (hn : finrank R F = 0) :
    o.prod positiveOrientation hm hn =
      o.map (Fin m) (LinearEquiv.prodUnique (R := R) (M := E) (M₂ := F)).symm := by
  -- The sign of the positive orientation relative to the empty basis of `F` is `1`.
  have hc : signBasis positiveOrientation (Module.finBasisOfFinrankEq R F hn) = 1 := by
    rw [← (Module.finBasisOfFinrankEq R F hn).orientation_isEmpty, signBasis_orientation]
  have h := reindex_prod_of_right_eq_zero o positiveOrientation hm hn (add_zero m) rfl
    (LinearEquiv.prodUnique (R := R) (M := E) (M₂ := F)).symm
    fun v ↦ Prod.ext rfl (Subsingleton.elim _ _)
  simpa [hc, finCongr_refl, reindex_refl] using h

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

end CommRing

section Field

variable {K E F U W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] {m n : ℕ}

/-- A block lower triangular linear equivalence `f : E × F ≃ U × W`, one whose first component
on `(x, 0)` is `e x` and which sends `(0, y)` to `(0, e' y)`, carries the product of orientations
`o` of `E` and `p` of `F` to the product of the orientations `e o` of `U` and `e' p` of `W`. -/
theorem map_prod_of_blockTriangular (f : (E × F) ≃ₗ[K] U × W) (e : E ≃ₗ[K] U)
    (e' : F ≃ₗ[K] W) (hf₁ : ∀ x, (f (x, 0)).1 = e x) (hf₂ : ∀ y, f (0, y) = (0, e' y))
    (o : Orientation K E (Fin m)) (p : Orientation K F (Fin n)) (hm : finrank K E = m)
    (hn : finrank K F = n) :
    Orientation.map (Fin (m + n)) f (o.prod p hm hn) =
      (Orientation.map (Fin m) e o).prod (Orientation.map (Fin n) e' p)
        (e.finrank_eq.symm.trans hm) (e'.finrank_eq.symm.trans hn) := by
  -- `f` is `e × e'` followed by the shear `(u, w) ↦ (u, w + s u)`.
  let s : U →ₗ[K] W := LinearMap.snd K U W ∘ₗ f.toLinearMap ∘ₗ LinearMap.inl K E F ∘ₗ
    e.symm.toLinearMap
  have hf : f = (e.prodCongr e').trans
      ((LinearEquiv.refl K U).skewProd (LinearEquiv.refl K W) s) := by
    refine LinearEquiv.ext fun z ↦ ?_
    have hz : f z = f (z.1, 0) + f (0, z.2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [hz, hf₂]
    ext <;> simp [s, hf₁, add_comm]
  rw [hf, map_trans, map_prod, map_skewProd_refl]
  simp [finrank_prod, e.finrank_eq.symm.trans hm, e'.finrank_eq.symm.trans hn]

/-- Let `V = H ⊕ N` and let `D : V ≃ U × W` map `N` into `{0} × W`, with `D k = (0, e' k)` for
`k ∈ N` and `(D h).1 = e h` for `h ∈ H`. Then `D` carries the orientation of `V` induced by
orientations `o` of `H` and `p` of `N` (the image of their product under `H × N ≃ V`) to the
product of the orientations `e o` of `U` and `e' p` of `W`. -/
theorem map_map_prodEquivOfIsCompl_prod {V : Type*} [AddCommGroup V] [Module K V]
    {H N : Submodule K V} [FiniteDimensional K H] [FiniteDimensional K N] (hc : IsCompl H N)
    (D : V ≃ₗ[K] U × W) (e : H ≃ₗ[K] U) (e' : N ≃ₗ[K] W) (hD₁ : ∀ h : H, (D h).1 = e h)
    (hD₂ : ∀ k : N, D k = (0, e' k)) (o : Orientation K H (Fin m))
    (p : Orientation K N (Fin n)) (hm : finrank K H = m) (hn : finrank K N = n) :
    Orientation.map (Fin (m + n)) D
        (Orientation.map (Fin (m + n)) (Submodule.prodEquivOfIsCompl H N hc) (o.prod p hm hn)) =
      (Orientation.map (Fin m) e o).prod (Orientation.map (Fin n) e' p)
        (e.finrank_eq.symm.trans hm) (e'.finrank_eq.symm.trans hn) := by
  rw [← map_trans]
  exact map_prod_of_blockTriangular _ e e' (fun x ↦ by simp [hD₁]) (fun y ↦ by simp [hD₂]) o p
    hm hn

end Field

end Orientation
