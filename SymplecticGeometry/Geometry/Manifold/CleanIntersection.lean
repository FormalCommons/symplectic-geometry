/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import SymplecticGeometry.Data.Set.Image
import SymplecticGeometry.Topology.Connected.Clopen

/-!
# Clean intersections of maps

Two maps `f : N → M` and `g : P → M` of manifolds intersect cleanly along a map `c : C → N` when
`c` is a smooth embedding whose range is a union of components of the intersection
`f ⁻¹' range g`, open and closed in it, and when at every point the tangent space of the
intersection is the intersection of the tangent spaces: whenever `g y = f (c x)`, the range of the
derivative of `f ∘ c` at `x` is the intersection of the ranges of the derivatives of `f` at `c x`
and of `g` at `y`. For embeddings `f` and `g` this is the usual clean intersection of the
submanifolds `range f` and `range g` along `f '' range c`; letting `range c` be only a part of the
intersection allows components of different dimensions to be treated one dimension at a time.

## Main definitions and results

* `SymplecticGeometry.IsCleanIntersection I J K L f g c`: `f` and `g` intersect cleanly along `c`.
* `SymplecticGeometry.IsCleanIntersection.of_range_eq`: the constructor for the case where
  `range c` is the whole intersection `f ⁻¹' range g`. In that case
  `Set.range_comp_eq_range_inter_of_range_eq_preimage`, from `SymplecticGeometry.Data.Set.Image`,
  gives `range (f ∘ c) = range f ∩ range g`.
* `SymplecticGeometry.IsCleanIntersection.self_id`: an injective map satisfies the predicate with
  itself along the identity.
* `SymplecticGeometry.IsCleanIntersection.isPreconnected_preimage`: for a topological embedding
  `f`, a set `T` of `N` with `range g ∩ f '' T` preconnected has preconnected preimage `c ⁻¹' T`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third
  edition][McDuffSalamon2017], §5.4.
-/

public section

open Set
open scoped ContDiff Manifold

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {G H'' P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} [TopologicalSpace P] [ChartedSpace H'' P]
  {E₀ H₀ C : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {L : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace C] [ChartedSpace H₀ C]

variable (I J K L) in
/-- The maps `f : N → M` and `g : P → M` intersect cleanly along `c : C → N`: `c` is a smooth
embedding whose range lies in `f ⁻¹' range g` and is open and closed in it, for the topology that
`N` induces, and whenever `g y = f (c x)`, the range of the derivative of `f ∘ c` at `x` is the
intersection of the ranges of the derivatives of `f` at `c x` and of `g` at `y`.

Nothing is assumed of `f` and `g`: they need not be smooth, nor immersions. When they are smooth
embeddings, this is the usual clean intersection of `range f` and `range g` along `f '' range c`;
for other maps the condition on derivatives says less, since `mfderiv` may vanish, as it does at
every point where a map is not differentiable. -/
structure IsCleanIntersection (f : N → M) (g : P → M) (c : C → N) : Prop where
  /-- The parametrization of the intersection is a smooth embedding. -/
  isSmoothEmbedding : Manifold.IsSmoothEmbedding L J ∞ c
  /-- The range of `c` lies in the intersection. -/
  range_subset : range c ⊆ f ⁻¹' range g
  /-- The range of `c` is open and closed in the intersection. -/
  isClopen_range : IsClopen ((↑) ⁻¹' range c : Set (f ⁻¹' range g))
  /-- The tangent space of the intersection is the intersection of the tangent spaces. -/
  range_mfderiv_comp : ∀ (x : C) (y : P), g y = f (c x) →
    (mfderiv L I (f ∘ c) x).range =
      (mfderiv J I f (c x)).range ⊓ (mfderiv K I g y).range

namespace IsCleanIntersection

variable {f : N → M} {g : P → M} {c : C → N}

/-- If `c` is a smooth embedding onto the whole intersection `f ⁻¹' range g`, and at each of its
points the range of the derivative of `f ∘ c` is the intersection of those of `f` and `g`, then
`f` and `g` intersect cleanly along `c`. -/
theorem of_range_eq (hc : Manifold.IsSmoothEmbedding L J ∞ c) (hrange : range c = f ⁻¹' range g)
    (hd : ∀ (x : C) (y : P), g y = f (c x) →
      (mfderiv L I (f ∘ c) x).range =
        (mfderiv J I f (c x)).range ⊓ (mfderiv K I g y).range) :
    IsCleanIntersection I J K L f g c where
  isSmoothEmbedding := hc
  range_subset := hrange.le
  isClopen_range := by
    rw [hrange, Subtype.coe_preimage_self]
    exact isClopen_univ
  range_mfderiv_comp := hd

/-- For an injective map `f`, the pair `f`, `f` satisfies `IsCleanIntersection` along the identity
of `N`: the intersection `f ⁻¹' range f` is all of `N`, and both derivative ranges are that of
`mfderiv J I f`. This is a clean self-intersection in the usual sense only when `f` is a smooth
embedding: `t ↦ t ^ 3` on `ℝ` satisfies the predicate, although its derivative vanishes at `0`. -/
theorem self_id [IsManifold J ∞ N] (hf : Function.Injective f) :
    IsCleanIntersection I J J J f f id :=
  of_range_eq .id (by rw [range_id, preimage_range]) fun x y hxy => by
    rw [hf hxy, Function.comp_id, id_eq, inf_idem]

/-- Let `f` and `g` intersect cleanly along `c`, with `f` a topological embedding. If `T` is a set
of `N` such that `range g ∩ f '' T` is preconnected in `M`, then `c ⁻¹' T` is preconnected in `C`.
-/
theorem isPreconnected_preimage (hc : IsCleanIntersection I J K L f g c)
    (hf : Topology.IsEmbedding f) {T : Set N} (hT : IsPreconnected (range g ∩ f '' T)) :
    IsPreconnected (c ⁻¹' T) := by
  -- `f` identifies `T ∩ f ⁻¹' range g` with `range g ∩ f '' T`. As `range c` is open and closed
  -- in `f ⁻¹' range g`, it cuts out a preconnected set, which `c` identifies with `c ⁻¹' T`.
  have hT' : IsPreconnected (T ∩ f ⁻¹' range g) := by
    rwa [← hf.isInducing.isPreconnected_image, image_inter_preimage, inter_comm]
  have hcT : c '' (c ⁻¹' T) = T ∩ f ⁻¹' range g ∩ range c := by
    rw [image_preimage_eq_range_inter, inter_right_comm, inter_assoc,
      inter_eq_left.2 hc.range_subset, inter_comm]
  rw [← hc.isSmoothEmbedding.isEmbedding.isInducing.isPreconnected_image, hcT]
  exact hT'.inter_of_isClopen_preimage_val inter_subset_right hc.isClopen_range

end IsCleanIntersection

end SymplecticGeometry

end
