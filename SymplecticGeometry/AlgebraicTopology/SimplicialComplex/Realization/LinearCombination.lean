/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Module.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Maps out of a realization that are affine on each simplex

Given values `f : ι → E` at the vertices of an abstract simplicial complex `K`, in a real
topological vector space `E`, the point of the realization with barycentric coordinates `x` is
sent to `∑ i, x i • f i`, that is, `Finsupp.linearCombination ℝ f x`. This map is affine on each
closed simplex and takes the value `f i` at the vertex `i`.

This file proves that the map is continuous for the weak topology of the realization, and that it
takes a point into every convex set that contains the values at the vertices of its carrier.
The continuity proof follows that of Tau Ceti's `AbstractSimplicialComplex.continuous_secantMap`,
which treats the same map, written through the values of a map on the realization, for a normed
space `E`.

## Main results

* `AbstractSimplicialComplex.continuous_linearCombination`: the map is continuous.
* `AbstractSimplicialComplex.linearCombination_mem_of_convex`: the image of a point lies in every
  convex set that contains the values at the vertices of its carrier.
-/

public section

open Set Function TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E] {K : AbstractSimplicialComplex ι}

/-- On a closed simplex `σ`, the linear combination with barycentric weights is the finite sum over
the vertices of `σ`. -/
theorem linearCombination_faceInclusion (f : ι → E) (σ : Face K) (x : StandardSimplex σ.val) :
    Finsupp.linearCombination ℝ f (faceInclusion K σ x).val = ∑ a ∈ σ.val, x.val a • f a := by
  rw [faceInclusion_val, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset x.val (StandardSimplex.support_subset x) (fun v t => t • f v)
      fun _ _ => zero_smul ℝ _]

/-- The map from a realization to a real topological vector space that sends a point to the
combination of given vertex values, weighted by its barycentric coordinates, is continuous. -/
theorem continuous_linearCombination [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (f : ι → E) : Continuous fun x : Realization K => Finsupp.linearCombination ℝ f x.val := by
  refine continuous_iff_faceInclusion.mpr fun σ => ?_
  have hcoord (a : ι) : Continuous fun x : StandardSimplex σ.val => x.val a :=
    (continuous_apply a).comp continuous_induced_dom
  simp_rw [comp_def, linearCombination_faceInclusion]
  exact continuous_finsetSum _ fun a _ => (hcoord a).smul continuous_const

/-- The combination of vertex values `f i`, weighted by the barycentric coordinates of a point
`x` of the realization, lies in every convex set that contains `f i` for each vertex `i` of the
carrier of `x`. -/
theorem linearCombination_mem_of_convex {s : Set E} (hs : Convex ℝ s) (f : ι → E)
    (x : Realization K) (hf : ∀ i ∈ x.val.support, f i ∈ s) :
    Finsupp.linearCombination ℝ f x.val ∈ s := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine hs.sum_mem (fun i _ => Realization.nonneg K x i) ?_ hf
  simpa [Finsupp.sum] using Realization.sum_eq_one K x

end AbstractSimplicialComplex

end
