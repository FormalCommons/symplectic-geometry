/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Affine

/-!
# Straight-line homotopies inside a subset

Mathlib's `ContinuousMap.Homotopy.affine f g` is the straight-line homotopy
`(t, x) ↦ AffineMap.lineMap (f x) (g x) t` between two continuous maps into a real topological
vector space `E`. This file restricts it to maps into a subset `s` of `E`: if each segment from
`f x` to `g x` lies in `s`, the same formula is a homotopy of maps into `↥s`.

## Main definitions

* `ContinuousMap.Homotopy.affineOfSegmentSubset`: the straight-line homotopy between two maps
  `X → ↥s` whose segments lie in `s`.
* `ContinuousMap.Homotopy.affineOfConvex`: the same homotopy, for a convex set `s`.
-/

public section

open Set

variable {X E : Type*} [TopologicalSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] {s : Set E}

namespace ContinuousMap.Homotopy

/-- The straight-line homotopy `(t, x) ↦ AffineMap.lineMap (f x) (g x) t` between two continuous
maps `f g : X → ↥s`, for a subset `s` that contains each segment from `f x` to `g x`. -/
noncomputable def affineOfSegmentSubset (f g : C(X, s))
    (h : ∀ x, segment ℝ (f x : E) (g x) ⊆ s) : f.Homotopy g where
  toFun p := ⟨affine ((ContinuousMap.subtypeVal s).comp f) ((ContinuousMap.subtypeVal s).comp g) p,
    h p.2 <| by simpa using lineMap_mem_segment ℝ (f p.2 : E) (g p.2) p.1.property⟩
  continuous_toFun := (affine _ _).continuous.subtype_mk _
  map_zero_left x := Subtype.ext <| apply_zero (affine _ _) x
  map_one_left x := Subtype.ext <| apply_one (affine _ _) x

/-- The value of `affineOfSegmentSubset f g h` at `(t, x)`, as a point of `E`, is
`AffineMap.lineMap (f x) (g x) t`. -/
@[simp]
theorem coe_affineOfSegmentSubset_apply (f g : C(X, s)) (h : ∀ x, segment ℝ (f x : E) (g x) ⊆ s)
    (p : unitInterval × X) :
    (affineOfSegmentSubset f g h p : E) = AffineMap.lineMap (f p.2 : E) (g p.2) (p.1 : ℝ) :=
  affine_apply _ _ p

/-- The straight-line homotopy `(t, x) ↦ AffineMap.lineMap (f x) (g x) t` between two continuous
maps into a convex set. -/
noncomputable def affineOfConvex (hs : Convex ℝ s) (f g : C(X, s)) : f.Homotopy g :=
  affineOfSegmentSubset f g fun x ↦ hs.segment_subset (f x).property (g x).property

/-- The value of `affineOfConvex hs f g` at `(t, x)`, as a point of `E`, is
`AffineMap.lineMap (f x) (g x) t`. -/
@[simp]
theorem coe_affineOfConvex_apply (hs : Convex ℝ s) (f g : C(X, s)) (p : unitInterval × X) :
    (affineOfConvex hs f g p : E) = AffineMap.lineMap (f p.2 : E) (g p.2) (p.1 : ℝ) :=
  coe_affineOfSegmentSubset_apply f g _ p

end ContinuousMap.Homotopy

end
