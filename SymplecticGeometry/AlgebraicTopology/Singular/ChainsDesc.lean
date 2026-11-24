/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Linear maps after a map out of the singular chains

Tau Ceti's `TauCeti.chainsDesc g` is the linear map out of the singular `n`-chains with
coefficients in a ring `k` that takes each singular simplex `s` to `g s`. This file shows that
composing it with a `k`-linear map `L` gives the map with values `L (g s)`.

## Main results

* `TauCeti.map_chainsDesc`: `L (chainsDesc g z) = chainsDesc (fun s ↦ L (g s)) z`.
-/

public section

open scoped Simplicial

namespace TauCeti

universe u

/-- A `k`-linear map applied after the map out of the singular chains with coefficients in `k`
with values `g` on simplices is the map with values `L ∘ g` on simplices. -/
theorem map_chainsDesc {k : Type u} [Ring k] {X : TopCat.{u}} {n : ℕ} {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {F : Type*} [FunLike F V W] [LinearMapClass F k V W] (L : F)
    (g : (TopCat.toSSet.obj X) _⦋n⦌ → V) (z : ((singularChains k).obj X).X n) :
    L (chainsDesc g z) = chainsDesc (fun s ↦ L (g s)) z :=
  LinearMap.congr_fun (f := (L : V →ₗ[k] W) ∘ₗ chainsDesc g)
    (singularChains_linearMap_ext fun s ↦ by simp) z

end TauCeti

end
