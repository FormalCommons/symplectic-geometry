/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Dimension.Finrank
import SymplecticGeometry.LinearAlgebra.Alternating.Basic
import SymplecticGeometry.Logic.Equiv.Fin.Basic
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Data.Fin.VecNotation
import TauCeti.Topology.Algebra.Module.Alternating.Basic

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
(`AlternatingMap.map_eq_zero_of_eq_smul`). In degree three, its value does not change under a
cyclic rotation of the arguments (`ContinuousAlternatingMap.map_vecCons_rotate`), since
`AlternatingMap.map_perm` multiplies it by the sign of the rotation, which is `1`.

Fixing the first `r` arguments of a continuous alternating map `f` of `r + m` arguments to `u`
gives the continuous alternating map `f.appendLeft u : w ↦ f (Fin.append u w)` of `m` arguments.
Its algebraic part is Tau Ceti's `AlternatingMap.currySum`, reindexed from `Fin r ⊕ Fin m` to
`Fin (r + m)` by `finSumFinEquiv`; only its continuity is proved here. As a function of `u` it is
again alternating (`ContinuousAlternatingMap.appendLeftAlternatingMap`).

Adding to the first `r` arguments of a continuous alternating map of degree `r + m` vectors of a
submodule `V` of rank at most `m` does not change its value once its last `m` arguments lie in
`V` (`ContinuousAlternatingMap.map_append_add_of_mem`). It follows from
`AlternatingMap.map_append_add_of_mem`, whose proof rests on
`AlternatingMap.map_eq_zero_of_finrank_lt`: an alternating map vanishes on a family with more
members in `V` than the rank of `V`.

A two-form `T` on a product `M₁ × M₂` splits, for a basis `bs` of `M₁`, into its values on pairs
of vectors of `M₂`, on a vector of `M₂` and a basis vector of `M₁`, and on increasing pairs of
basis vectors of `M₁` (`ContinuousAlternatingMap.apply_vecCons_prod_eq_sum`). The part along `M₁`
is expanded by Tau Ceti's `ContinuousAlternatingMap.apply_vecCons_eq_sum_repr`, and its double
sum folded onto the increasing pairs by Tau Ceti's `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`.
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

/-- A continuous alternating map of three vectors takes the same value on `![a, b, c]` and on its
cyclic rotation `![b, c, a]`, as a cyclic permutation of three arguments is even. -/
theorem map_vecCons_rotate {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (f : M [⋀^Fin 3]→L[R] N) (a b c : M) : f ![a, b, c] = f ![b, c, a] := by
  have h : ![a, b, c] = ![b, c, a] ∘ (finRotate 3).symm := by
    ext i
    fin_cases i <;> rfl
  rw [h, ← coe_toAlternatingMap, AlternatingMap.map_perm, Equiv.Perm.sign_symm, sign_finRotate]
  simp

/-- Let `V` be a submodule of `W` of rank at most `m`. A continuous alternating map `f` of
`r + m` vectors takes the same value on `Fin.append (v + u) w` and on `Fin.append v w` when every
`u i` and every `w j` lies in `V`. -/
theorem map_append_add_of_mem {K W N : Type*} [Ring K] [IsDomain K] [StrongRankCondition K]
    [AddCommGroup W] [Module K W] [TopologicalSpace W] [AddCommGroup N] [Module K N]
    [Module.IsTorsionFree K N] [TopologicalSpace N] {r m : ℕ} (f : W [⋀^Fin (r + m)]→L[K] N)
    {V : Submodule K W} [Module.Finite K V] (hV : Module.finrank K V ≤ m) (v : Fin r → W)
    {u : Fin r → W} (hu : ∀ i, u i ∈ V) {w : Fin m → W} (hw : ∀ j, w j ∈ V) :
    f (Fin.append (v + u) w) = f (Fin.append v w) :=
  f.toAlternatingMap.map_append_add_of_mem hV v hu hw

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

section Prod

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module R M₂] [TopologicalSpace M₂] [AddCommGroup N] [Module R N]
  [TopologicalSpace N] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **A two-form on a product in coordinates along the first factor.** For a basis `bs` of
`M₁`, with coordinates `cᵢ = bs.coord i`, a two-form `T` on `M₁ × M₂` takes the value
`T((0, w₁), (0, w₂)) + ∑ᵢ (cᵢ(u₂) T((0, w₁), (bsᵢ, 0)) - cᵢ(u₁) T((0, w₂), (bsᵢ, 0)))
+ ∑_{i<j} (cᵢ(u₁) cⱼ(u₂) - cᵢ(u₂) cⱼ(u₁)) T((bsᵢ, 0), (bsⱼ, 0))` on `(u₁, w₁)` and
`(u₂, w₂)`. -/
theorem apply_vecCons_prod_eq_sum (bs : Module.Basis ι R M₁) (T : (M₁ × M₂) [⋀^Fin 2]→L[R] N)
    (u₁ u₂ : M₁) (w₁ w₂ : M₂) :
    T ![(u₁, w₁), (u₂, w₂)] = T ![(0, w₁), (0, w₂)] +
      ∑ i, (bs.coord i u₂ • T ![(0, w₁), (bs i, 0)] - bs.coord i u₁ • T ![(0, w₂), (bs i, 0)]) +
      ∑ i, ∑ j with i < j, (bs.coord i u₁ * bs.coord j u₂ - bs.coord i u₂ * bs.coord j u₁) •
        T ![(bs i, 0), (bs j, 0)] := by
  -- Split both vectors into their parts along `M₁` and along `M₂`.
  have hsplit : T ![(u₁, w₁), (u₂, w₂)] = T ![(u₁, 0), (u₂, 0)] - T ![(0, w₂), (u₁, 0)] +
      T ![(0, w₁), (u₂, 0)] + T ![(0, w₁), (0, w₂)] := by
    rw [show ((u₁, w₁) : M₁ × M₂) = (u₁, 0) + (0, w₁) by simp,
      show ((u₂, w₂) : M₁ × M₂) = (u₂, 0) + (0, w₂) by simp, T.vecCons_add,
      T.apply_vecCons_add_right, T.apply_vecCons_add_right,
      T.apply_vecCons_swap (u₁, 0) (0, w₂)]
    abel
  -- Expand a second vector along `M₁` in the basis `bs`.
  have hbs (a : M₁ × M₂) (u : M₁) :
      T ![a, (u, 0)] = ∑ i, bs.coord i u • T ![a, (bs i, 0)] := by
    have hu : ((u, 0) : M₁ × M₂) = ∑ i, bs.repr u i • ((bs i, 0) : M₁ × M₂) :=
      Prod.ext (by simp [Prod.fst_sum, bs.sum_repr]) (by simp [Prod.snd_sum])
    have hlin := _root_.map_sum
      (T.toContinuousMultilinearMap.toMultilinearMap.toLinearMap ![a, (u, 0)] 1)
      (fun i ↦ bs.repr u i • ((bs i, 0) : M₁ × M₂)) Finset.univ
    have h₁ (z : M₁ × M₂) : Function.update ![a, (u, 0)] 1 z = ![a, z] := by
      funext k; fin_cases k <;> simp
    simp only [← hu, MultilinearMap.toLinearMap_apply, map_smul, h₁] at hlin
    simpa using hlin
  -- The part along `M₁` is a two-form on `M₁`, expanded in `bs`.
  have hbase : T ![(u₁, 0), (u₂, 0)] = ∑ i, ∑ j with i < j,
      (bs.coord i u₁ * bs.coord j u₂ - bs.coord i u₂ * bs.coord j u₁) •
        T ![(bs i, 0), (bs j, 0)] := by
    have h := (T.compContinuousLinearMap
      (ContinuousLinearMap.inl R M₁ M₂)).apply_vecCons_eq_sum_repr bs u₁ u₂
    simp only [compContinuousLinearMap_apply, Matrix.comp_vec2,
      ContinuousLinearMap.inl_apply] at h
    rw [h, ← Fintype.sum_prod_type' (f := fun i j ↦
        (bs.repr u₁ i * bs.repr u₂ j) • T ![(bs i, 0), (bs j, 0)]),
      TauCeti.sum_univ_prod_eq_sum_lt_add_swap _ fun i ↦ by
        rw [T.map_eq_zero_of_eq ![(bs i, 0), (bs i, 0)] (i := 0) (j := 1) rfl Fin.zero_ne_one,
          smul_zero],
      Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Finset.sum_filter, Prod.swap, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [T.apply_vecCons_swap (bs i, 0), sub_smul, smul_neg, mul_comm (bs.repr u₁ j)]
      abel
    · rfl
  rw [hsplit, hbase, hbs (0, w₁) u₂, hbs (0, w₂) u₁, Finset.sum_sub_distrib]
  abel

end Prod

end ContinuousAlternatingMap

end
