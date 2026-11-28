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
sufficient condition of the same kind in which the boundary is allowed to move: it is enough that
every relative cube can be deformed into `A` through maps of pairs
`(I × Iⁿ, ∂(I × Iⁿ)) → (X, A)`.

The argument: such a deformation ends at a map `g` with values in `A`. Contracting the cube to
the corner `(1, 1)` deforms `g` within `A` to the constant map at the image of that corner, and
the track of the corner under the deformation is a path in `A` back to `a`, along which the
constant map moves to the constant relative cube at `a`. So the relative cube is homotopic
through maps of pairs to the constant one, and by
`TauCeti.RelHomotopyGroup.exists_transport_mk_eq_mk_of_homotopicWith` its class is carried to the
trivial class by a base-point change along a loop in `A`. Base-point change is a bijection fixing
the trivial class (`TauCeti.RelHomotopyGroup.transport_symm_transport`,
`TauCeti.RelHomotopyGroup.transport_default`), so the class is trivial.

## Main results

* `ContinuousMap.HomotopyWith.homotopicWith_const_of_forall_mem`: a map of pairs out of the cube
  that deforms through maps of pairs into `A` is homotopic through maps of pairs to a constant.
* `TauCeti.RelHomotopyGroup.subsingleton_of_forall_homotopicWith`: for a based pair
  `(X, A, a)`, if every relative cube is homotopic through maps of pairs to a map with values in
  `A`, then `π_{n+1}(X, A, a)` is trivial.
* `TauCeti.RelHomotopyGroup.subsingleton_ofSubset_of_forall_homotopicWith`: the same for a
  subset `A` of a space, with the hypothesis on all maps of pairs out of the cube.

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
constant map at its value at the corner `(1, 1)`. The second map is contracted within `A` to that
corner, and the track of the corner under the given homotopy, which lies in `A`, leads back. -/
theorem homotopicWith_const_of_forall_mem {p g : C(I × (I^N), Y)}
    (H : p.HomotopyWith g fun f ↦ MapsTo f (Cube.prodBoundary N) A) (hg : ∀ y, g y ∈ A) :
    p.HomotopicWith (.const _ (p (1, fun _ ↦ 1))) fun f ↦ MapsTo f (Cube.prodBoundary N) A := by
  have hc : ((1, fun _ ↦ 1) : I × (I^N)) ∈ Cube.prodBoundary N :=
    Cube.mk_mem_prodBoundary (.inl rfl)
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

/-- **Free compression.** Let `(X, A, a)` be a based pair. If every relative cube `I × I^N → X`
is homotopic, through maps sending the boundary `Cube.prodBoundary N` of the cube into `A`, to a
map with values in `A`, then the relative homotopy set `π_{n+1}(X, A, a)` is trivial, where `n`
is the cardinality of `N`. Unlike `TauCeti.RelHomotopyGroup.subsingleton_iff`, the homotopy need
not be stationary on the boundary of the cube. -/
theorem subsingleton_of_forall_homotopicWith [Finite N] {X : BasedTopPair.{u}}
    (h : ∀ p : RelGenLoop N X, ∃ g : C(I × (I^N), X.pair.fst), (∀ y, g y ∈ range X.pair.map) ∧
      (p : C(I × (I^N), X.pair.fst)).HomotopicWith g
        fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map)) :
    Subsingleton (RelHomotopyGroup N X) := by
  have := Fintype.ofFinite N
  suffices hp : ∀ p : RelGenLoop N X, mk p = default by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨p, rfl⟩ := mk_surjective x
    obtain ⟨q, rfl⟩ := mk_surjective y
    rw [hp p, hp q]
  intro p
  obtain ⟨g, hg, ⟨H⟩⟩ := h p
  have hconst : ContinuousMap.const _ ((p : C(I × (I^N), X.pair.fst)) (1, fun _ ↦ 1)) =
      ((RelGenLoop.const : RelGenLoop N X) : C(I × (I^N), X.pair.fst)) := by
    ext y
    simp only [ContinuousMap.const_apply, RelGenLoop.coe_coe, RelGenLoop.const_apply,
      RelGenLoop.apply_one]
  have hpc := H.homotopicWith_const_of_forall_mem hg
  rw [hconst] at hpc
  obtain ⟨γ, hγ⟩ := exists_transport_mk_eq_mk_of_homotopicWith hpc
  rw [← transport_symm_transport γ (mk p), hγ, ← default_eq, transport_default]

/-- **Free compression for a subset.** Let `A` be a subset of a space `X` and `a ∈ A`. If every
map of pairs `g : (I × I^N, Cube.prodBoundary N) → (X, A)` is homotopic, through maps of pairs,
to a map with values in `A`, then the relative homotopy set `π_{n+1}(X, A, a)` is trivial, where
`n` is the cardinality of `N`. -/
theorem subsingleton_ofSubset_of_forall_homotopicWith [Finite N] {X : TopCat.{u}} {A : Set X}
    (h : ∀ g : C(I × (I^N), X), MapsTo g (Cube.prodBoundary N) A →
      ∃ g' : C(I × (I^N), X), (∀ y, g' y ∈ A) ∧
        g.HomotopicWith g' fun f ↦ MapsTo f (Cube.prodBoundary N) A)
    (a : A) : Subsingleton (RelHomotopyGroup N ⟨TopPair.ofSubset A, a⟩) := by
  refine subsingleton_of_forall_homotopicWith fun p ↦ ?_
  have hp := RelGenLoop.mapsTo_prodBoundary p.property
  rw [TopPair.range_ofSubset_map] at hp ⊢
  exact h _ hp

end RelHomotopyGroup

end TauCeti

end
