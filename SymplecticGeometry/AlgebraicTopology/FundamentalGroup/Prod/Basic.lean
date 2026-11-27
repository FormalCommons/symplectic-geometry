/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Loop classes in a product, coordinate by coordinate

Tau Ceti's `FundamentalGroup.prodMulEquiv` splits `π₁(X × Y, (x, y))` as
`π₁(X, x) × π₁(Y, y)` by the maps induced by the two coordinate projections. This file states
the consequences used to compute maps between fundamental groups of products one coordinate at
a time.

## Main results

* `FundamentalGroup.prod_ext`: an element of `π₁(X × Y, (x, y))` is determined by its images
  under the two projections, and `FundamentalGroup.map_fst_injective`: by its image under the
  first one if `Y` is simply connected.
* `FundamentalGroup.map_prodMk_const_surjective`: if `Y` is simply connected, the inclusion of
  the slice `X × {y}` is onto on fundamental groups.
* `FundamentalGroup.prodMulEquiv_mapOfEq`: the coordinates of the image of a class under a map
  `f : Z → X × Y` are its images under the two coordinates of `f`.
* `FundamentalGroup.map_fst_map_prodMap`, `FundamentalGroup.map_snd_map_prodMap`: the
  coordinates of the image of a class under `f.prodMap g` are the images of its coordinates.
* `FundamentalGroup.ker_map_fst_eq_range`: the classes with trivial first coordinate are those
  of loops in the slice `{x} × Y`.
* `FundamentalGroup.map_id_prodMap_surjective`, `FundamentalGroup.mem_ker_map_id_prodMap_iff`,
  `FundamentalGroup.ker_map_id_prodMap`: if `Y'` is simply connected, the map induced by
  `id × g : X × Y → X × Y'` is surjective, and a class is in its kernel exactly when its first
  coordinate is trivial, so that its kernel is the kernel of the first projection.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Cambridge University Press, 2002, Proposition 1.12.
-/

public section

namespace FundamentalGroup

variable {X X' Y Y' : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  [TopologicalSpace Y']

/-- Two elements of `π₁(X × Y, (x, y))` are equal if their images under both coordinate
projections are. -/
theorem prod_ext {x : X} {y : Y} {γ δ : FundamentalGroup (X × Y) (x, y)}
    (h₁ : map .fst (x, y) γ = map .fst (x, y) δ) (h₂ : map .snd (x, y) γ = map .snd (x, y) δ) :
    γ = δ :=
  (prodMulEquiv x y).injective <| (prodMulEquiv_apply x y γ).trans <|
    (Prod.ext h₁ h₂).trans (prodMulEquiv_apply x y δ).symm

/-- The first coordinate of the image of a loop class under `f.prodMap g` is the image under `f`
of its first coordinate. -/
theorem map_fst_map_prodMap (f : C(X, X')) (g : C(Y, Y')) (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    map .fst (f x, g y) (map (f.prodMap g) (x, y) γ) = map f x (map .fst (x, y) γ) :=
  (DFunLike.congr_fun (map_comp .fst (f.prodMap g) (x, y)) γ).symm.trans
    (DFunLike.congr_fun (map_comp f .fst (x, y)) γ)

/-- The second coordinate of the image of a loop class under `f.prodMap g` is the image under `g`
of its second coordinate. -/
theorem map_snd_map_prodMap (f : C(X, X')) (g : C(Y, Y')) (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    map .snd (f x, g y) (map (f.prodMap g) (x, y) γ) = map g y (map .snd (x, y) γ) :=
  (DFunLike.congr_fun (map_comp .snd (f.prodMap g) (x, y)) γ).symm.trans
    (DFunLike.congr_fun (map_comp g .snd (x, y)) γ)

/-- The image of a loop class under `f : C(Z, X × Y)` with `f z = (x, y)`, split by
`prodMulEquiv`, is the pair of its images under the two coordinates of `f`. -/
theorem prodMulEquiv_mapOfEq {Z : Type*} [TopologicalSpace Z] {z : Z} {x : X} {y : Y}
    (f : C(Z, X × Y)) (hf : f z = (x, y)) (γ : FundamentalGroup Z z) :
    prodMulEquiv x y (mapOfEq f hf γ) =
      (mapOfEq (ContinuousMap.fst.comp f) (by simp [hf]) γ,
        mapOfEq (ContinuousMap.snd.comp f) (by simp [hf]) γ) := by
  rw [prodMulEquiv_apply, ← mapOfEq_rfl, ← mapOfEq_rfl, mapOfEq_comp, mapOfEq_comp]
  -- The two sides differ only in the proofs of the base point equations.
  rfl

/-- If `Y` is simply connected, the first coordinate projection is injective on
`π₁(X × Y, (x, y))`. -/
theorem map_fst_injective [SimplyConnectedSpace Y] (x : X) (y : Y) :
    Function.Injective (map (.fst : C(X × Y, X)) (x, y)) :=
  fun _ _ h => prod_ext h (Subsingleton.elim _ _)

/-- If `Y` is simply connected, the inclusion `x' ↦ (x', y)` of the slice `X × {y}` induces a
surjection `π₁(X, x) → π₁(X × Y, (x, y))`. -/
theorem map_prodMk_const_surjective [SimplyConnectedSpace Y] (x : X) (y : Y) :
    Function.Surjective (map ((ContinuousMap.id X).prodMk (.const X y)) x) := fun γ =>
  ⟨map .fst _ γ, map_fst_injective x y <|
    (DFunLike.congr_fun (map_comp .fst ((ContinuousMap.id X).prodMk (.const X y)) x) _).symm.trans
      (DFunLike.congr_fun (map_id x) _)⟩

/-- The kernel of the first coordinate projection on `π₁(X × Y, (x, y))` is the image of
`π₁(Unit × Y, ((), y))` under the inclusion `(u, y') ↦ (x, y')` of the slice through `x`. -/
theorem ker_map_fst_eq_range (x : X) (y : Y) :
    (map (.fst : C(X × Y, X)) (x, y)).ker =
      (map ((ContinuousMap.const Unit x).prodMap (.id Y)) ((), y)).range := by
  -- the first coordinate of a class from the slice factors through `π₁(Unit, ())`
  have h₁ : ∀ δ₀, map .fst (x, y) (map ((ContinuousMap.const Unit x).prodMap (.id Y)) ((), y)
      δ₀) = 1 := fun δ₀ => (map_fst_map_prodMap _ _ () y δ₀).trans <|
    (congrArg (map (ContinuousMap.const Unit x) ()) (Subsingleton.elim _ 1)).trans (map_one _)
  apply le_antisymm
  · intro δ hδ
    rw [MonoidHom.mem_ker] at hδ
    refine ⟨(prodMulEquiv () y).symm (1, map .snd (x, y) δ), ?_⟩
    have h₂ := congrArg Prod.snd <| (prodMulEquiv_apply () y _).symm.trans <|
      (prodMulEquiv () y).apply_symm_apply (1, map .snd (x, y) δ)
    exact prod_ext ((h₁ _).trans hδ.symm) <| (map_snd_map_prodMap _ _ () y _).trans <|
      (DFunLike.congr_fun (map_id y) _).trans h₂
  · rintro _ ⟨δ₀, rfl⟩
    exact h₁ δ₀

/-- The first coordinate of the image of a class under `id × g` is its first coordinate. -/
theorem map_fst_map_id_prodMap (g : C(Y, Y')) (x : X) (y : Y)
    (γ : FundamentalGroup (X × Y) (x, y)) :
    map .fst (x, g y) (map ((ContinuousMap.id X).prodMap g) (x, y) γ) = map .fst (x, y) γ :=
  (map_fst_map_prodMap _ _ x y γ).trans (DFunLike.congr_fun (map_id x) _)

/-- If `Y'` is simply connected, the map `id × g : X × Y → X × Y'` induces a surjection of
fundamental groups. -/
theorem map_id_prodMap_surjective [SimplyConnectedSpace Y'] (g : C(Y, Y')) (x : X) (y : Y) :
    Function.Surjective (map ((ContinuousMap.id X).prodMap g) (x, y)) := by
  intro γ
  let δ := (prodMulEquiv x y).symm (map .fst _ γ, 1)
  have h : map .fst (x, y) δ = map .fst _ γ :=
    congrArg Prod.fst <| (prodMulEquiv_apply x y δ).symm.trans <|
      (prodMulEquiv x y).apply_symm_apply _
  exact ⟨δ, map_fst_injective x _ <| (map_fst_map_id_prodMap g x y δ).trans h⟩

/-- If `Y'` is simply connected, a class of `π₁(X × Y, (x, y))` is in the kernel of the map
induced by `id × g : X × Y → X × Y'` if and only if its first coordinate is trivial. -/
theorem mem_ker_map_id_prodMap_iff [SimplyConnectedSpace Y'] (g : C(Y, Y')) {x : X} {y : Y}
    {δ : FundamentalGroup (X × Y) (x, y)} :
    δ ∈ (map ((ContinuousMap.id X).prodMap g) (x, y)).ker ↔ map .fst (x, y) δ = 1 := by
  have hδ := map_fst_map_id_prodMap g x y δ
  rw [MonoidHom.mem_ker]
  exact ⟨fun h => hδ.symm.trans ((congrArg (map .fst (x, g y)) h).trans (map_one _)),
    fun h => map_fst_injective x _ (hδ.trans (h.trans (map_one _).symm))⟩

/-- If `Y'` is simply connected, the kernel of the map induced by `id × g : X × Y → X × Y'` is
the kernel of the first coordinate projection. -/
theorem ker_map_id_prodMap [SimplyConnectedSpace Y'] (g : C(Y, Y')) (x : X) (y : Y) :
    (map ((ContinuousMap.id X).prodMap g) (x, y)).ker = (map (.fst : C(X × Y, X)) (x, y)).ker :=
  Subgroup.ext fun _ => (mem_ker_map_id_prodMap_iff g).trans MonoidHom.mem_ker.symm

end FundamentalGroup

end
