/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import SymplecticGeometry.LinearAlgebra.Alternating.Basic
public import SymplecticGeometry.Logic.Equiv.Fin.Basic
public import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Continuous alternating maps

A continuous alternating map of degree one is determined by its values on the one-element
families `![w]`. This file states that as the extensionality lemma
`ContinuousAlternatingMap.ext_fin_one`, so that a proof that two such maps agree can start with
`ext w` and work with a vector `w` instead of a family `v : Fin 1 → M`. In degree two,
`ContinuousAlternatingMap.ext_fin_two` does the same with the pairs `![v, w]`, so that a proof
that two two-forms agree can start with `ext v w`. Both follow from `AlternatingMap.ext_fin_one`
and `AlternatingMap.ext_fin_two` for the underlying alternating maps.

A continuous alternating map vanishes on a family two of whose members are multiples of one
vector (`ContinuousAlternatingMap.map_eq_zero_of_eq_smul`), as an alternating map does
(`AlternatingMap.map_eq_zero_of_eq_smul`).

Fixing the first `r` arguments of a continuous alternating map `f` of `r + m` arguments to `u`
gives the continuous alternating map `f.appendLeft u : w ↦ f (Fin.append u w)` of `m` arguments.
Its algebraic part is Tau Ceti's `AlternatingMap.currySum`, reindexed from `Fin r ⊕ Fin m` to
`Fin (r + m)` by `finSumFinEquiv`; only its continuity is proved here. As a function of `u` it is
again alternating (`ContinuousAlternatingMap.appendLeftAlternatingMap`).
-/

public section

namespace ContinuousAlternatingMap

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]

/-- Two continuous alternating maps of one vector are equal when they agree on every one-element
family `![w]`. -/
@[ext]
theorem ext_fin_one {f g : M [⋀^Fin 1]→L[R] N} (h : ∀ w, f ![w] = g ![w]) : f = g :=
  toAlternatingMap_injective <| AlternatingMap.ext_fin_one h

/-- Two continuous alternating maps of two vectors are equal when they agree on every pair
`![v, w]`. -/
@[ext]
theorem ext_fin_two {f g : M [⋀^Fin 2]→L[R] N} (h : ∀ v w, f ![v, w] = g ![v, w]) : f = g :=
  toAlternatingMap_injective <| AlternatingMap.ext_fin_two h

/-- A continuous alternating map vanishes on a family `v` whose members `v i` and `v j`, for
`i ≠ j`, are multiples `a • x` and `b • x` of the same vector `x`. -/
theorem map_eq_zero_of_eq_smul {ι : Type*} (f : M [⋀^ι]→L[R] N) {v : ι → M} {i j : ι}
    (hij : i ≠ j) {x : M} {a b : R} (hi : v i = a • x) (hj : v j = b • x) : f v = 0 :=
  f.toAlternatingMap.map_eq_zero_of_eq_smul hij hi hj


section AppendLeft

variable {R W N : Type*} [CommSemiring R] [AddCommMonoid W] [Module R W] [TopologicalSpace W]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N] {r m : ℕ}

/-- The alternating map of `m` arguments obtained from an alternating map `f` of `r + m`
arguments by fixing its first `r` arguments to `u`: `w ↦ f (Fin.append u w)`. -/
def appendLeft (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) : W [⋀^Fin m]→L[R] N :=
  { (f.toAlternatingMap.domDomCongr finSumFinEquiv.symm).currySum u with
    cont := by
      have h : ⇑((f.toAlternatingMap.domDomCongr finSumFinEquiv.symm).currySum u) =
          fun w ↦ f (Fin.append u w) := by
        funext w
        simp
      simp only [MultilinearMap.toFun_eq_coe, AlternatingMap.coe_multilinearMap, h]
      refine f.cont.comp <| continuous_pi fun p ↦ ?_
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
      · simpa only [Fin.append_left] using continuous_const
      · simpa only [Fin.append_right] using continuous_apply j }

/-- The alternating map underlying `f.appendLeft u` is the currying of `f`, reindexed by
`finSumFinEquiv`, along the sum `Fin r ⊕ Fin m` at `u`. -/
theorem toAlternatingMap_appendLeft (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    (f.appendLeft u).toAlternatingMap =
      (f.toAlternatingMap.domDomCongr finSumFinEquiv.symm).currySum u := (rfl)

/-- The value of `f.appendLeft u` on `w` is that of `f` on `Fin.append u w`. -/
@[simp]
theorem appendLeft_apply (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) (w : Fin m → W) :
    f.appendLeft u w = f (Fin.append u w) := by
  rw [← coe_toAlternatingMap, toAlternatingMap_appendLeft, AlternatingMap.currySum_apply,
    AlternatingMap.domDomCongr_apply, Fin.sumElim_comp_finSumFinEquiv_symm, coe_toAlternatingMap]

/-- Fixing the first arguments is additive in the alternating map. -/
@[simp]
theorem appendLeft_add [ContinuousAdd N] (f g : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    (f + g).appendLeft u = f.appendLeft u + g.appendLeft u := by
  ext w
  simp

/-- Fixing the first arguments commutes with scalar multiplication of the alternating map. -/
@[simp]
theorem appendLeft_smul {S : Type*} [Monoid S] [DistribMulAction S N] [ContinuousConstSMul S N]
    [SMulCommClass R S N] (c : S) (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    (c • f).appendLeft u = c • f.appendLeft u := by
  ext w
  simp

variable [ContinuousAdd N] [ContinuousConstSMul R N]

/-- `u ↦ f.appendLeft u`, an alternating map of the `r` fixed arguments with values in continuous
alternating maps of the other `m`. -/
def appendLeftAlternatingMap (f : W [⋀^Fin (r + m)]→L[R] N) :
    W [⋀^Fin r]→ₗ[R] W [⋀^Fin m]→L[R] N where
  toFun u := f.appendLeft u
  map_update_add' u i x y := toAlternatingMap_injective <| by
    simp only [toAlternatingMap_appendLeft, toAlternatingMap_add, AlternatingMap.map_update_add]
  map_update_smul' u i c x := toAlternatingMap_injective <| by
    simp only [toAlternatingMap_appendLeft, toAlternatingMap_smul,
      AlternatingMap.map_update_smul, RingHom.id_apply]
  map_eq_zero_of_eq' u i j hu hij := toAlternatingMap_injective <| by
    rw [toAlternatingMap_appendLeft, AlternatingMap.map_eq_zero_of_eq _ u hu hij,
      toAlternatingMap_zero]

/-- `f.appendLeftAlternatingMap` sends `u` to `f.appendLeft u`. -/
@[simp]
theorem appendLeftAlternatingMap_apply (f : W [⋀^Fin (r + m)]→L[R] N) (u : Fin r → W) :
    f.appendLeftAlternatingMap u = f.appendLeft u := (rfl)

end AppendLeft

end ContinuousAlternatingMap

end
