/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.Hom
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
`ContinuousLinearMap.inCoordinates_pullback_bilinear_of_mem` is the same comparison for a
continuous bilinear form on `V (f x)`, read in the bundles of bilinear forms on `f *ᵖ V` and on
`V`; its proof evaluates both sides at two vectors by Mathlib's `inCoordinates_apply_eq₂`.

`Bundle.Trivialization.linearMapAt_pullback` says that a pulled-back linear trivialization reads
a vector over `x` as the original one reads it over `f x`: the `linearMapAt` form of Tau Ceti's
`Bundle.Trivialization.linearEquivAt_pullback`. `VectorBundle.continuousLinearEquivAt_pullback`
says that the preferred chart of `f *ᵖ E` at `x` is that of `E` at `f x`: the form for preferred
charts of Tau Ceti's `Bundle.Trivialization.continuousLinearEquivAt_pullback`.

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

`Bundle.Pullback.castEquiv f h χ` carries a continuous linear equivalence `χ : F ≃L[R] E a` to
the fibre `(f *ᵖ E) b` along an equation `h : a = f b`, as for a frame of `E` at a point read
through a chosen preimage under `f`. `Bundle.Pullback.lift_mk_castEquiv` says that it lifts back
to `χ`, and `Bundle.Pullback.castEquiv_trans_symm` that it preserves transitions.

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

namespace ContinuousLinearMap

/-- The coordinates of a continuous bilinear form on a fibre of the pull-back `f *ᵖ V`, as a
point of the bundle of bilinear forms on `f *ᵖ V`, are its coordinates in the bundle of bilinear
forms on `V`, at the image points, wherever `f x` lies in the base set of the trivialization of
`V` at `f x₀`. -/
theorem inCoordinates_pullback_bilinear_of_mem (f : K) (x₀ x : X)
    (β : V (f x) →L[𝕜] V (f x) →L[𝕜] 𝕜) (hV : f x ∈ (trivializationAt F V (f x₀)).baseSet) :
    inCoordinates F ((f : X → B) *ᵖ V) (F →L[𝕜] 𝕜)
        (fun y ↦ ((f : X → B) *ᵖ V) y →L[𝕜] Trivial X 𝕜 y) x₀ x x₀ x β =
      inCoordinates F V (F →L[𝕜] 𝕜) (fun b ↦ V b →L[𝕜] Trivial B 𝕜 b)
        (f x₀) (f x) (f x₀) (f x) β := by
  have hV' : x ∈ (trivializationAt F ((f : X → B) *ᵖ V) x₀).baseSet := hV
  have hs (u : F) : (trivializationAt F ((f : X → B) *ᵖ V) x₀).symm x u =
      (trivializationAt F V (f x₀)).symm (f x) u :=
    (trivializationAt F V (f x₀)).symm_pullback f hV u
  ext v w
  -- The fibres of the pull-back carry the module instances of `V` under other names; `erw`
  -- sees through them.
  erw [inCoordinates_apply_eq₂ (E₃ := Trivial X 𝕜) hV' hV' (Set.mem_univ _),
    inCoordinates_apply_eq₂ (E₃ := Trivial B 𝕜) hV hV (Set.mem_univ _)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization, hs]
  -- Both sides are now the same expression, up to those instances.
  rfl

end ContinuousLinearMap

end Coordinates

namespace Bundle.Trivialization

variable {𝕜 B B' F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [∀ b, AddCommGroup (E b)]
  [∀ b, Module 𝕜 (E b)] [TopologicalSpace (TotalSpace F E)]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- A pulled-back linear trivialization reads a vector of the fibre over `x` as the original
trivialization reads it over `f x`. This is the counterpart for `linearMapAt` of Tau Ceti's
`Bundle.Trivialization.linearEquivAt_pullback`. -/
@[simp]
theorem linearMapAt_pullback (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (f : K) (x : B')
    (v : ((f : B' → B) *ᵖ E) x) : (e.pullback f).linearMapAt 𝕜 x v = e.linearMapAt 𝕜 (f x) v := by
  rw [linearMapAt_apply (e.pullback f), linearMapAt_apply e (b := f x) (y := (v : E (f x)))]
  -- `x ∈ f ⁻¹' e.baseSet` is `f x ∈ e.baseSet` and `Pullback.lift f ⟨x, v⟩` is `⟨f x, v⟩`, by
  -- definition; the fibre types differ by the synonym `*ᵖ`, so `simp` does not rewrite them.
  rfl

end Bundle.Trivialization

namespace VectorBundle

variable {𝕜 B B' F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] [TopologicalSpace B']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*) [∀ b, AddCommMonoid (E b)]
  [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

/-- The preferred chart of the pull-back `f *ᵖ E` at `x` is the preferred chart of `E` at `f x`:
the preferred trivialization of the pull-back is the pull-back of that of `E`
(`FiberBundle.pullback_trivializationAt'`). This is the form for preferred charts of Tau Ceti's
`Bundle.Trivialization.continuousLinearEquivAt_pullback`. -/
@[simp]
theorem continuousLinearEquivAt_pullback (f : K) (x : B') :
    continuousLinearEquivAt 𝕜 F ((f : B' → B) *ᵖ E) x = continuousLinearEquivAt 𝕜 F E (f x) := by
  ext v
  rw [continuousLinearEquivAt, Trivialization.continuousLinearEquivAt_apply, trivializationAt,
    FiberBundle.pullback_trivializationAt']
  -- The pulled-back chart sends `⟨x, v⟩` to the image of `⟨f x, v⟩` under the chart of `E`, by
  -- definition. Tau Ceti's `Bundle.Trivialization.continuousLinearEquivAt_pullback` asks for
  -- fibres that are groups, and `Bundle.Trivialization.pullback_apply` for a `ContinuousMap`.
  rfl

end VectorBundle

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

section CastEquiv

variable {R F : Type*} [Semiring R] [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]

/-- A continuous linear equivalence `F ≃ E a` read as one onto the fibre at `b` of the pull-back
`f *ᵖ E`, which is `E (f b)`, where `a = f b`. -/
def castEquiv (f : B' → B) {a : B} {b : B'} (h : a = f b) (χ : F ≃L[R] E a) :
    F ≃L[R] (f *ᵖ E) b :=
  cast (congrArg (fun c ↦ F ≃L[R] E c) h) χ

@[simp]
theorem castEquiv_rfl (f : B' → B) (b : B') (χ : F ≃L[R] E (f b)) :
    castEquiv f rfl χ = χ :=
  (rfl)

/-- The vector `castEquiv f h χ v` of the pull-back, lifted to `E`, is the vector `χ v` over
`a`. -/
theorem lift_mk_castEquiv (f : B' → B) {a : B} {b : B'} (h : a = f b) (χ : F ≃L[R] E a)
    (v : F) :
    Pullback.lift f (TotalSpace.mk' F b (castEquiv f h χ v)) = TotalSpace.mk' F a (χ v) := by
  subst h
  rfl

/-- The transition between two equivalences carried to the pull-back is the transition between
the original ones. -/
theorem castEquiv_trans_symm (f : B' → B) {a : B} {b : B'} (h : a = f b)
    (α β : F ≃L[R] E a) :
    (castEquiv f h α).trans (castEquiv f h β).symm = α.trans β.symm := by
  subst h
  rfl

end CastEquiv

end Bundle.Pullback

end
