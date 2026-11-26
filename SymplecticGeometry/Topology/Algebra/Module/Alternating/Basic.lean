/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import SymplecticGeometry.LinearAlgebra.Alternating.Basic

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

Adding to the first `r` arguments of a continuous alternating map of degree `r + m` vectors of a
submodule `V` of rank at most `m` does not change its value once its last `m` arguments lie in
`V` (`ContinuousAlternatingMap.map_append_add_of_mem`). It follows from
`AlternatingMap.map_append_add_of_mem`, whose proof rests on
`AlternatingMap.map_eq_zero_of_finrank_lt`: an alternating map vanishes on a family with more
members in `V` than the rank of `V`.
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

end ContinuousAlternatingMap

end
