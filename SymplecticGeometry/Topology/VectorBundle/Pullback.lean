/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Alternating maps and negatives on a pull-back bundle

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

The file also has `Bundle.Pullback.neg_fiber`: the negative, taken in `V (f y)`, of a vector of
type `(f *ᵖ V) y` is its negative for Tau Ceti's group structure
`Bundle.Pullback.instAddCommGroup` on that fibre. Since `Bundle.Pullback` is not reducible,
`simp` does not see this equation by itself.

## References

* D. Husemoller, *Fibre Bundles*, 3rd ed., Graduate Texts in Mathematics 20, Springer, 1994,
  Chapter 2 (induced bundles).
-/

public section

open Bundle

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

namespace Bundle.Pullback

variable {B' : Type*} {E : B → Type*} [∀ b, AddCommGroup (E b)] {f : B' → B} {y : B'}

/-- The negative, taken in `E (f y)`, of a vector `v` of the fibre of `f *ᵖ E` at `y` is the
negative of `v` in that fibre. -/
@[simp]
theorem neg_fiber (v : (f *ᵖ E) y) :
    @Eq ((f *ᵖ E) y) (@Neg.neg (E (f y)) _ v) (-v) := (rfl)

end Bundle.Pullback

end
