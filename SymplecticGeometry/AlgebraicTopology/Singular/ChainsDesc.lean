/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Additive maps after a map out of the singular chains

Tau Ceti's `TauCeti.chainsDesc g` is the map out of the singular `n`-chains that takes each
singular simplex `s` to `g s`. This file shows that composing it with an additive map `L` gives
the map with values `L (g s)`, for integer coefficients.

## Main results

* `TauCeti.map_chainsDesc`: `L (chainsDesc g z) = chainsDesc (fun s ↦ L (g s)) z`.
-/

public section

open scoped Simplicial

namespace TauCeti

/-- An additive map applied after the map out of the integral singular chains with values `g` on
simplices is the map with values `L ∘ g` on simplices. -/
theorem map_chainsDesc {X : TopCat.{0}} {n : ℕ} {V W : Type} [AddCommGroup V] [AddCommGroup W]
    {F : Type*} [FunLike F V W] [AddMonoidHomClass F V W] (L : F)
    (g : (TopCat.toSSet.obj X) _⦋n⦌ → V) (z : ((singularChains ℤ).obj X).X n) :
    L (chainsDesc g z) = chainsDesc (fun s ↦ L (g s)) z :=
  DFunLike.congr_fun (f := (L : V →+ W).comp (chainsDesc g).toAddMonoidHom)
    (g := (chainsDesc fun s ↦ L (g s)).toAddMonoidHom)
    (singularChains_addMonoidHom_ext fun s ↦ by simp) z

end TauCeti

end
