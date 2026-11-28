/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Pair.Homotopy

/-!
# Free compression of relative cubes

Tau Ceti's compression criterion `TauCeti.RelHomotopyGroup.subsingleton_iff` says that the
relative homotopy set `π_{n+1}(X, A, a)` is trivial exactly when every relative cube can be
deformed into `A` by a homotopy that is stationary on the boundary of the cube. This file gives a
criterion of the same kind in which the boundary is allowed to move: it is enough that every
relative cube can be deformed into `A` through maps of pairs `(I × Iⁿ, ∂(I × Iⁿ)) → (X, A)`.

The argument: such a deformation ends at a map `g` with values in `A`. Contracting the cube to
the corner `(1, 1)` deforms `g` within `A` to the constant map at the image of that corner, and
the track of the corner under the deformation is a path in `A` back to `a`, along which the
constant map moves to the constant relative cube at `a`. So the relative cube is homotopic
through maps of pairs to the constant one, and by
`TauCeti.RelHomotopyGroup.exists_transport_mk_eq_mk_of_homotopicWith` its class is carried to the
trivial class by a base-point change along a loop in `A`. Base-point change is a bijection fixing
the trivial class (`TauCeti.RelHomotopyGroup.transport_symm_transport`,
`TauCeti.RelHomotopyGroup.transport_default`), so the class is trivial.

The contraction of `g` adapts the homotopy of `TauCeti.RelGenLoop.homotopic_const_of_mem_range`
to all coordinates of the cube. The argument follows that of
`TauCeti.RelHomotopyGroup.pairClass_eq_default_of_range_subset`, without its hypothesis of simple
connectivity: contract to a constant cube through maps of pairs, then cancel the change of base
point with `TauCeti.RelHomotopyGroup.transport_default`.

## Main results

* `ContinuousMap.HomotopyWith.homotopicWith_const_of_forall_mem`: a map of pairs out of the cube
  that deforms through maps of pairs into `A` is homotopic through maps of pairs to a constant.
* `TauCeti.RelHomotopyGroup.mk_eq_default_iff_homotopicWith`: a relative cube represents the
  trivial class exactly when it is homotopic through maps of pairs to a map with values in `A`.
* `TauCeti.RelHomotopyGroup.subsingleton_iff_forall_homotopicWith`: for a based pair
  `(X, A, a)`, `π_{n+1}(X, A, a)` is trivial exactly when every relative cube is homotopic
  through maps of pairs to a map with values in `A`.
* `TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_forall_homotopicWith`: a sufficient
  condition for a subset `A` of a space, with the hypothesis on all maps of pairs out of the
  cube.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the compression criterion stated before Theorem 4.3.
-/

public section

open Set
open scoped unitInterval Topology Topology.Homotopy

universe u v

namespace ContinuousMap.HomotopyWith

open TauCeti

variable {N Y : Type*} [TopologicalSpace Y] {A : Set Y}

/-- If a map `p : I × I^N → Y` is homotopic, through maps sending `Cube.prodBoundary N` into a
set `A`, to a map with all its values in `A`, then `p` is homotopic through such maps to the
constant map at its value at the corner `(1, 1)`. -/
theorem homotopicWith_const_of_forall_mem {p g : C(I × (I^N), Y)}
    (H : p.HomotopyWith g fun f ↦ MapsTo f (Cube.prodBoundary N) A) (hg : ∀ y, g y ∈ A) :
    p.HomotopicWith (.const _ (p (1, fun _ ↦ 1))) fun f ↦ MapsTo f (Cube.prodBoundary N) A := by
  have hc : ((1, fun _ ↦ 1) : I × (I^N)) ∈ Cube.prodBoundary N :=
    Cube.mk_mem_prodBoundary (.inl rfl)
  -- Contract `g` within `A` to the corner `(1, 1)`, then follow the track of the corner under
  -- `H`, which stays in `A` since the corner is on the boundary, back to `p (1, 1)`.
  refine HomotopicWith.trans ⟨H⟩ <|
    HomotopicWith.trans (g := .const _ (g (1, fun _ ↦ 1))) ⟨?_⟩ ⟨?_⟩
  · exact
      { toFun x := g (max x.2.1 x.1, fun i ↦ max (x.2.2 i) x.1)
        continuous_toFun := by fun_prop
        map_zero_left y := by simp
        map_one_left y := by simp [max_eq_right unitInterval.le_one']
        prop' t y _ := hg _ }
  · exact
      { toFun x := H (σ x.1, (1, fun _ ↦ 1))
        continuous_toFun := by fun_prop
        map_zero_left y := by simp
        map_one_left y := by simp
        prop' t y _ := H.prop _ hc }

end ContinuousMap.HomotopyWith

namespace TauCeti

namespace RelHomotopyGroup

variable {N : Type v}

/-- **Free compression of a class.** Let `(X, A, a)` be a based pair. A relative cube
`p : I × I^N → X` represents the trivial class of the relative homotopy set `π_{n+1}(X, A, a)`,
where `n` is the cardinality of `N`, exactly when it is homotopic, through maps sending the
boundary `Cube.prodBoundary N` of the cube into `A`, to a map with values in `A`. Unlike
`TauCeti.RelHomotopyGroup.mk_eq_default_iff`, the homotopy need not be stationary on the boundary
of the cube. -/
theorem mk_eq_default_iff_homotopicWith [Finite N] {X : BasedTopPair.{u}} {p : RelGenLoop N X} :
    mk p = default ↔ ∃ g : C(I × (I^N), X.pair.fst), (∀ y, g y ∈ range X.pair.map) ∧
      (p : C(I × (I^N), X.pair.fst)).HomotopicWith g
        fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map) := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg, ⟨H⟩⟩ ↦ ?_⟩
  · rw [default_eq, mk_eq_mk] at h
    exact ⟨_, fun y ↦ by rw [RelGenLoop.coe_coe, RelGenLoop.const_apply]; exact mem_range_self _,
      h.homotopicWith⟩
  have := Fintype.ofFinite N
  have hconst : ContinuousMap.const _ ((p : C(I × (I^N), X.pair.fst)) (1, fun _ ↦ 1)) =
      ((RelGenLoop.const : RelGenLoop N X) : C(I × (I^N), X.pair.fst)) := by
    ext y
    simp only [ContinuousMap.const_apply, RelGenLoop.coe_coe, RelGenLoop.const_apply,
      RelGenLoop.apply_one]
  have hpc := H.homotopicWith_const_of_forall_mem hg
  rw [hconst] at hpc
  obtain ⟨γ, hγ⟩ := exists_transport_mk_eq_mk_of_homotopicWith hpc
  rw [← transport_symm_transport γ (mk p), hγ, ← default_eq, transport_default]

/-- **Free compression.** Let `(X, A, a)` be a based pair. The relative homotopy set
`π_{n+1}(X, A, a)`, where `n` is the cardinality of `N`, is trivial exactly when every relative
cube `I × I^N → X` is homotopic, through maps sending the boundary `Cube.prodBoundary N` of the
cube into `A`, to a map with values in `A`. Unlike `TauCeti.RelHomotopyGroup.subsingleton_iff`,
the homotopy need not be stationary on the boundary of the cube. -/
theorem subsingleton_iff_forall_homotopicWith [Finite N] {X : BasedTopPair.{u}} :
    Subsingleton (RelHomotopyGroup N X) ↔
      ∀ p : RelGenLoop N X, ∃ g : C(I × (I^N), X.pair.fst), (∀ y, g y ∈ range X.pair.map) ∧
        (p : C(I × (I^N), X.pair.fst)).HomotopicWith g
          fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map) := by
  refine ⟨fun _ p ↦ mk_eq_default_iff_homotopicWith.1 (Subsingleton.elim _ _),
    fun h ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain ⟨p, rfl⟩ := mk_surjective x
  obtain ⟨q, rfl⟩ := mk_surjective y
  rw [mk_eq_default_iff_homotopicWith.2 (h p), mk_eq_default_iff_homotopicWith.2 (h q)]

/-- **Free compression for a subset.** Let `A` be a subset of a space `X` and `a ∈ A`. If every
map of pairs `g : (I × I^N, Cube.prodBoundary N) → (X, A)` is homotopic, through maps of pairs,
to a map with values in `A`, then the relative homotopy set `π_{n+1}(X, A, a)` is trivial, where
`n` is the cardinality of `N`. -/
theorem subsingleton_ofSubset_of_forall_homotopicWith [Finite N] {X : TopCat.{u}} {A : Set X}
    (h : ∀ g : C(I × (I^N), X), MapsTo g (Cube.prodBoundary N) A →
      ∃ g' : C(I × (I^N), X), (∀ y, g' y ∈ A) ∧
        g.HomotopicWith g' fun f ↦ MapsTo f (Cube.prodBoundary N) A)
    (a : A) : Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset A, a⟩) := by
  refine subsingleton_iff_forall_homotopicWith.2 fun p ↦ ?_
  have hp := RelGenLoop.mapsTo_prodBoundary p.property
  rw [TopPair.range_ofSubset_map] at hp ⊢
  exact h _ hp

end RelHomotopyGroup

end TauCeti

end
