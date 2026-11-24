/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic

/-!
# Linear maps after a map out of the singular chains

Tau Ceti's `TauCeti.chainsDesc g` is the linear map out of the singular `n`-chains with
coefficients in a ring `k` that takes each singular simplex `s` to `g s`. This file shows that
composing it with a `k`-linear map `L` gives the map with values `L (g s)`.

It also shows that `chainsDesc` of a family of functions on the simplices with values in a real
normed space, each `C^m` in a parameter `t` from a manifold, is `C^m` in `t` on every integral
chain: the chains on which it is `C^m` form a subgroup, and the quotient map by that subgroup
vanishes on every simplex, so it is zero.

## Main results

* `TauCeti.map_chainsDesc`: `L (chainsDesc g z) = chainsDesc (fun s ↦ L (g s)) z`.
* `TauCeti.contMDiff_chainsDesc`: if `t ↦ f t s` is `C^m` for every simplex `s`, then
  `t ↦ chainsDesc (f t) z` is `C^m` for every integral chain `z`.
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

open scoped Manifold ContDiff in
/-- If a family `f t` of values in a real normed space `F` on the singular `n`-simplices of `X`
is `C^m` in the parameter `t` on each simplex, then the map out of the integral `n`-chains with
values `f t` on simplices is `C^m` in `t` on each chain. -/
theorem contMDiff_chainsDesc {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {K : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : WithTop ℕ∞}
    {X : TopCat.{0}} {n : ℕ} {f : N → (TopCat.toSSet.obj X) _⦋n⦌ → F}
    (hf : ∀ s, ContMDiff K 𝓘(ℝ, F) m fun t ↦ f t s) (z : ((singularChains ℤ).obj X).X n) :
    ContMDiff K 𝓘(ℝ, F) m fun t ↦ chainsDesc (f t) z := by
  -- The chains on which the map is `C^m` in the parameter.
  let S : AddSubgroup (((singularChains ℤ).obj X).X n) :=
    { carrier := {z | ContMDiff K 𝓘(ℝ, F) m fun t ↦ chainsDesc (f t) z}
      add_mem' {a b} ha hb := by simpa only [Set.mem_ofPred_eq, map_add, Pi.add_def] using ha.add hb
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using contMDiff_const
      neg_mem' {a} ha := by simpa only [Set.mem_ofPred_eq, map_neg, Pi.neg_def] using ha.neg }
  have hS : QuotientAddGroup.mk' S = 0 := singularChains_addMonoidHom_ext fun s ↦ by
    simpa [S, QuotientAddGroup.eq_zero_iff, chainsDesc_simplexChain_one] using hf s
  exact (QuotientAddGroup.eq_zero_iff z).mp (DFunLike.congr_fun hS z)

end TauCeti

end
