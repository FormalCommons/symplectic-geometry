/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Product

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
* `FundamentalGroup.map_fst_map_prodMap`, `FundamentalGroup.map_snd_map_prodMap`: the
  coordinates of the image of a class under `f.prodMap g` are the images of its coordinates.

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

/-- If `Y` is simply connected, the first coordinate projection is injective on
`π₁(X × Y, (x, y))`. -/
theorem map_fst_injective [SimplyConnectedSpace Y] (x : X) (y : Y) :
    Function.Injective (map (.fst : C(X × Y, X)) (x, y)) :=
  fun _ _ h => prod_ext h (Subsingleton.elim _ _)

end FundamentalGroup

end
