/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Topology.VectorBundle.Pullback
public import SymplecticGeometry.Data.Bundle

/-!
# Alternating maps and fibre operations on a pull-back bundle

Let `V` be a topological vector bundle over `B` and `f : X → B` a continuous map. An alternating
map `A : V (f x) [⋀^ι]→L[𝕜] G` is a point of two bundles of alternating maps: the one from
`f *ᵖ V` to the trivial bundle `Bundle.Trivial X G` over `X`, and the one from `V` to
`Bundle.Trivial B G` over `B`. This file shows that its coordinate expressions in the two agree
wherever `f x` lies in the base set of the trivialization of `V` at `f x₀`
(`ContinuousAlternatingMap.inCoordinates_pullback_trivial_of_mem`): a trivialization of the
pull-back is the pull-back of a trivialization of `V`, and the trivial bundle is trivialized by
the identity over both bases.

This is the counterpart for alternating maps of Tau Ceti's
`ContinuousLinearMap.inCoordinates_pullback_of_mem`, and its proof follows that one.

The file also has `simp` lemmas for vectors of the fibre `(f *ᵖ V) y`, which is `V (f y)` by
definition, with the group and module structures of `V (f y)` under another name (Tau Ceti's
`Bundle.Pullback.instAddCommGroup`, Mathlib's module structure). Since `Bundle.Pullback` is not
reducible, `simp` does not identify the two types, and the lemmas about one do not apply to
terms built in the other. The lemmas take each operation at the type of its arguments:
`Bundle.Pullback.neg_fiber`, `add_fiber`, `sub_fiber` and `smul_fiber` move an operation taken
in `V (f y)` on vectors of type `(f *ᵖ V) y` to `(f *ᵖ V) y`, and `neg_pullback`,
`add_pullback`, `sub_pullback` and `smul_pullback` move an operation taken in `(f *ᵖ V) y` on
vectors of type `V (f y)` to `V (f y)`. Each applies only where the two types differ, so the
two families do not undo each other. `zero_fiber` relates the two zeros; it is not a `simp`
lemma, since a zero alone has no argument whose type could decide between them. In an equation
the other side decides: `eq_zero_fiber_iff`, `zero_fiber_eq_iff`, `eq_zero_pullback_iff` and
`zero_pullback_eq_iff` replace a zero of the other type by the zero of the type of the
equation. `linearMap_sub_apply_fiber` and `linearMap_sub_apply_pullback` evaluate a difference
of two semilinear maps on one of the types at a vector of the other, as `LinearMap.sub_apply`
does at the same type, and `linearMap_zero_apply_fiber` and `linearMap_zero_apply_pullback` do
the same for the zero map, as `LinearMap.zero_apply` does. The equations between two vectors are in
`SymplecticGeometry/Data/Bundle.lean`, which this file imports so that the whole simp set comes
with it.

`smul_fiber` is Tau Ceti's `Bundle.Pullback.smul_eq` read from right to left, for Mathlib's
module structure on the fibres: the file of `smul_eq` gives the fibres a second scalar action,
`Bundle.Pullback.instSMul`, and importing it here would change the action that
`c • v` elaborates to in every file that imports this one.

Since `Bundle.Pullback` is not reducible, instance search also does not find an
`IsNormableSpace` instance of `E (f y)` on the fibre `(f *ᵖ E) y`.
`Bundle.Pullback.instIsNormableSpace` gives it, next to Tau Ceti's instances on these fibres
such as `Bundle.Pullback.instNormedSpace`. Together with `TangentSpace.instIsNormableSpace` of
`SymplecticGeometry/Geometry/Manifold/IsManifold/Basic.lean`, it covers the fibres
`(f *ᵖ TangentSpace I) q`.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

open Bundle

section Coordinates

variable {𝕜 B X F G K ι : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [FunLike K X B] [ContinuousMapClass K X B]

namespace ContinuousAlternatingMap

/-- The coordinates of an alternating map from a fibre of the pull-back `f *ᵖ V` to `G`, as a
point of the bundle of alternating maps from `f *ᵖ V` to `Bundle.Trivial X G`, are its
coordinates in the bundle of alternating maps from `V` to `Bundle.Trivial B G`, at the image
points, wherever `f x` lies in the base set of the trivialization of `V` at `f x₀`. -/
theorem inCoordinates_pullback_trivial_of_mem (f : K) (x₀ x : X)
    (A : V (f x) [⋀^ι]→L[𝕜] G) (hV : f x ∈ (trivializationAt F V (f x₀)).baseSet) :
    inCoordinates F G (E₁ := (f : X → B) *ᵖ V) (E₂ := Bundle.Trivial X G) x₀ x x₀ x A =
      inCoordinates F G (E₁ := V) (E₂ := Bundle.Trivial B G) (f x₀) (f x) (f x₀) (f x) A := by
  have hV' : x ∈ (trivializationAt F ((f : X → B) *ᵖ V) x₀).baseSet := hV
  -- The fibres of the pull-back carry the module instances of `V` under other names; `erw`
  -- sees through them.
  erw [inCoordinates_eq F G (E₂ := Bundle.Trivial X G) hV' (Set.mem_univ _),
    inCoordinates_eq F G (E₂ := Bundle.Trivial B G) hV (Set.mem_univ _)]
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.continuousLinearEquivAt_pullback]
  rfl

end ContinuousAlternatingMap

end Coordinates

namespace Bundle.Pullback

variable {B B' : Type*} {E : B → Type*} {f : B' → B} {y : B'}

section AddCommMonoid

variable [∀ b, AddCommMonoid (E b)]

/-- The zero of `E (f y)` is the zero of the fibre of `f *ᵖ E` at `y`. This is not a `simp`
lemma: its left-hand side is any zero of `E (f y)`. The lemmas below use it inside equations,
where the other side fixes the type. -/
theorem zero_fiber : @Eq ((f *ᵖ E) y) (0 : E (f y)) 0 := (rfl)

/-- A vector `v` of the fibre of `f *ᵖ E` at `y` equals the zero of `E (f y)` if and only if
it is the zero of that fibre. -/
@[simp]
theorem eq_zero_fiber_iff {v : (f *ᵖ E) y} : @Eq ((f *ᵖ E) y) v (0 : E (f y)) ↔ v = 0 :=
  Iff.rfl

/-- The zero of `E (f y)` equals a vector `v` of the fibre of `f *ᵖ E` at `y` if and only if
the zero of that fibre does. -/
@[simp]
theorem zero_fiber_eq_iff {v : (f *ᵖ E) y} : @Eq ((f *ᵖ E) y) (0 : E (f y)) v ↔ 0 = v :=
  Iff.rfl

/-- A vector `v` of `E (f y)` equals the zero of the fibre of `f *ᵖ E` at `y` if and only if
it is the zero of `E (f y)`. -/
@[simp]
theorem eq_zero_pullback_iff {v : E (f y)} : @Eq (E (f y)) v (0 : (f *ᵖ E) y) ↔ v = 0 :=
  Iff.rfl

/-- The zero of the fibre of `f *ᵖ E` at `y` equals a vector `v` of `E (f y)` if and only if
the zero of `E (f y)` does. -/
@[simp]
theorem zero_pullback_eq_iff {v : E (f y)} : @Eq (E (f y)) (0 : (f *ᵖ E) y) v ↔ 0 = v :=
  Iff.rfl

/-- The sum, taken in `E (f y)`, of two vectors `v` and `w` of the fibre of `f *ᵖ E` at `y` is
their sum in that fibre. -/
@[simp]
theorem add_fiber (v w : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@HAdd.hAdd (E (f y)) (E (f y)) (E (f y)) _ v w) (v + w) := (rfl)

/-- The sum, taken in the fibre of `f *ᵖ E` at `y`, of two vectors `v` and `w` of `E (f y)` is
their sum in `E (f y)`. -/
@[simp]
theorem add_pullback (v w : E (f y)) :
    @Eq (E (f y)) (@HAdd.hAdd ((f *ᵖ E) y) ((f *ᵖ E) y) ((f *ᵖ E) y) _ v w) (v + w) := (rfl)

end AddCommMonoid

section AddCommGroup

variable [∀ b, AddCommGroup (E b)]

/-- The negative, taken in `E (f y)`, of a vector `v` of the fibre of `f *ᵖ E` at `y` is the
negative of `v` in that fibre. -/
@[simp]
theorem neg_fiber (v : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@Neg.neg (E (f y)) _ v) (-v) := (rfl)

/-- The negative, taken in the fibre of `f *ᵖ E` at `y`, of a vector `v` of `E (f y)` is the
negative of `v` in `E (f y)`. -/
@[simp]
theorem neg_pullback (v : E (f y)) :
    @Eq (E (f y)) (@Neg.neg ((f *ᵖ E) y) _ v) (-v) := (rfl)

/-- The difference, taken in `E (f y)`, of two vectors `v` and `w` of the fibre of `f *ᵖ E` at
`y` is their difference in that fibre. -/
@[simp]
theorem sub_fiber (v w : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@HSub.hSub (E (f y)) (E (f y)) (E (f y)) _ v w) (v - w) := (rfl)

/-- The difference, taken in the fibre of `f *ᵖ E` at `y`, of two vectors `v` and `w` of
`E (f y)` is their difference in `E (f y)`. -/
@[simp]
theorem sub_pullback (v w : E (f y)) :
    @Eq (E (f y)) (@HSub.hSub ((f *ᵖ E) y) ((f *ᵖ E) y) ((f *ᵖ E) y) _ v w) (v - w) := (rfl)

end AddCommGroup

section Module

variable {R : Type*} [Semiring R] [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)]

/-- The multiple `c • v`, taken in `E (f y)`, of a vector `v` of the fibre of `f *ᵖ E` at `y` is
the multiple `c • v` in that fibre. -/
@[simp]
theorem smul_fiber (c : R) (v : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@HSMul.hSMul R (E (f y)) (E (f y)) _ c v) (c • v) := (rfl)

/-- The multiple `c • v`, taken in the fibre of `f *ᵖ E` at `y`, of a vector `v` of `E (f y)` is
the multiple `c • v` in `E (f y)`. -/
@[simp]
theorem smul_pullback (c : R) (v : E (f y)) :
    @Eq (E (f y)) (@HSMul.hSMul R ((f *ᵖ E) y) ((f *ᵖ E) y) _ c v) (c • v) := (rfl)

variable {S N : Type*} [Semiring S] {σ : R →+* S}

section Zero

variable [AddCommMonoid N] [Module S N]

/-- The zero semilinear map on `E (f y)`, applied to a vector `v` of the fibre of `f *ᵖ E` at
`y`, is `0`. This is `LinearMap.zero_apply` for a vector of the pull-back fibre. -/
@[simp]
theorem linearMap_zero_apply_fiber (v : (f *ᵖ E) y) : (0 : E (f y) →ₛₗ[σ] N) v = 0 :=
  LinearMap.zero_apply v

/-- The zero semilinear map on the fibre of `f *ᵖ E` at `y`, applied to a vector `v` of
`E (f y)`, is `0`. This is `LinearMap.zero_apply` for a vector of `E (f y)`. -/
@[simp]
theorem linearMap_zero_apply_pullback (v : E (f y)) : (0 : (f *ᵖ E) y →ₛₗ[σ] N) v = 0 :=
  LinearMap.zero_apply v

end Zero

section Sub

variable [AddCommGroup N] [Module S N]

/-- The difference of two semilinear maps `g` and `h` on `E (f y)`, applied to a vector `v` of
the fibre of `f *ᵖ E` at `y`, is `g v - h v`. This is `LinearMap.sub_apply` for a vector of the
pull-back fibre. -/
@[simp]
theorem linearMap_sub_apply_fiber (g h : E (f y) →ₛₗ[σ] N) (v : (f *ᵖ E) y) :
    (g - h) v = g v - h v :=
  LinearMap.sub_apply g h v

/-- The difference of two semilinear maps `g` and `h` on the fibre of `f *ᵖ E` at `y`, applied to
a vector `v` of `E (f y)`, is `g v - h v`. This is `LinearMap.sub_apply` for a vector of
`E (f y)`. -/
@[simp]
theorem linearMap_sub_apply_pullback (g h : (f *ᵖ E) y →ₛₗ[σ] N) (v : E (f y)) :
    (g - h) v = g v - h v :=
  LinearMap.sub_apply g h v

end Sub

end Module

/-- A fibre of the pull-back `f *ᵖ E` is normable over `𝕜` when the fibres of `E` are: it is
`E (f y)`, with the same topology and module structure. -/
instance instIsNormableSpace {𝕜 : Type*} [NormedField 𝕜] [∀ b, AddCommGroup (E b)]
    [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [∀ b, IsNormableSpace 𝕜 (E b)] :
    IsNormableSpace 𝕜 ((f *ᵖ E) y) :=
  inferInstanceAs (IsNormableSpace 𝕜 (E (f y)))

end Bundle.Pullback

end
