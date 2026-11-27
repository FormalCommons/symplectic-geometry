/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Transporting a map of fundamental groups along homeomorphisms

Let `F : C(A, B)` and `g : C(C, D)` be continuous maps, and `e' : A ≃ₜ C`, `e : B ≃ₜ D`
homeomorphisms with `g ∘ e' = e ∘ F`. Then the map of fundamental groups that `g` induces at
`e' a` is the one that `F` induces at `a`, read through the isomorphisms
`FundamentalGroup.homeomorphMulEquivOfEq` of `e'` and `e`. So one is surjective exactly when
the other is, and the kernel of the first is the image of the kernel of the second.

A typical use is a map between two open subsets of a space, such as the inclusion of an
intersection `S ∩ T` into `T`, which an open embedding identifies with a map between products.

## Main results

* `FundamentalGroup.map_homeomorphMulEquivOfEq`: the square of fundamental groups commutes.
* `FundamentalGroup.map_surjective_iff_of_homeomorph`: `g` is surjective on fundamental groups
  if and only if `F` is.
* `FundamentalGroup.ker_map_eq_map_ker_of_homeomorph`: the kernel of the map induced by `g` is
  the image of that of `F`.
-/

public section

namespace FundamentalGroup

variable {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace D] {F : C(A, B)} {g : C(C, D)} {e' : A ≃ₜ C} {e : B ≃ₜ D} {a : A} {c : C}

/-- If `g ∘ e' = e ∘ F` for homeomorphisms `e'` and `e`, then the map of fundamental groups
induced by `g` at `c = e' a`, applied to the image under `e'` of a class `γ`, is the image under
`e` of the image of `γ` under `F`. -/
theorem map_homeomorphMulEquivOfEq (h : ∀ w, g (e' w) = e (F w)) (hc : e' a = c)
    (γ : FundamentalGroup A a) :
    map g c (homeomorphMulEquivOfEq e' hc γ) =
      homeomorphMulEquivOfEq e ((h a).symm.trans (congrArg g hc)) (map F a γ) := by
  subst hc
  simp only [homeomorphMulEquivOfEq_apply, ← mapOfEq_rfl]
  exact mapOfEq_mapOfEq_eq_mapOfEq_mapOfEq (ContinuousMap.ext h) _ _ _ _ γ

/-- If `g ∘ e' = e ∘ F` for homeomorphisms `e'` and `e`, then the map of fundamental groups
induced by `g` at `e' a` is surjective if and only if the one induced by `F` at `a` is. -/
theorem map_surjective_iff_of_homeomorph (h : ∀ w, g (e' w) = e (F w)) (hc : e' a = c) :
    Function.Surjective (map g c) ↔ Function.Surjective (map F a) := by
  have hg : ⇑(map g c) = homeomorphMulEquivOfEq e ((h a).symm.trans (congrArg g hc)) ∘
      map F a ∘ (homeomorphMulEquivOfEq e' hc).symm := funext fun y ↦ by
    simp only [Function.comp_apply, ← map_homeomorphMulEquivOfEq h hc, MulEquiv.apply_symm_apply]
  rw [hg, EquivLike.comp_surjective, EquivLike.surjective_comp]

/-- If `g ∘ e' = e ∘ F` for homeomorphisms `e'` and `e`, then the kernel of the map of
fundamental groups induced by `g` at `e' a` is the image under `e'` of the kernel of the map
induced by `F` at `a`. -/
theorem ker_map_eq_map_ker_of_homeomorph (h : ∀ w, g (e' w) = e (F w)) (hc : e' a = c) :
    (map g c).ker = (map F a).ker.map (homeomorphMulEquivOfEq e' hc).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker]
  conv_lhs => rw [← (homeomorphMulEquivOfEq e' hc).apply_symm_apply y]
  rw [map_homeomorphMulEquivOfEq h hc, MulEquiv.map_eq_one_iff]

end FundamentalGroup

end
