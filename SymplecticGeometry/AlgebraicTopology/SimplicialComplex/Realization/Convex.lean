/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.LinearExtension

/-!
# Linear extensions over a realization and convex sets

The linear extension `K.linearExtension p` of vertex data `p : ι → E` sends a point of the
realization of `K` to a convex combination of the values of `p` at the vertices of its carrier.
So it takes that point into every convex set that contains those values.

## Main results

* `AbstractSimplicialComplex.linearExtension_mem_of_convex`: the linear extension at a point lies
  in every convex set that contains the vertex data at the vertices of its carrier.
-/

public section

namespace AbstractSimplicialComplex

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E] {K : AbstractSimplicialComplex ι}

/-- The linear extension of vertex data `p` at a point `x` of the realization lies in every convex
set that contains `p i` for each vertex `i` in the barycentric support of `x`. -/
theorem linearExtension_mem_of_convex {s : Set E} (hs : Convex ℝ s) (p : ι → E)
    (x : Realization K) (hp : ∀ i ∈ x.val.support, p i ∈ s) : K.linearExtension p x ∈ s := by
  rw [linearExtension_apply, Finsupp.linearCombination_apply, Finsupp.sum]
  refine hs.sum_mem (fun i _ => Realization.nonneg K x i) ?_ hp
  simpa [Finsupp.sum] using Realization.sum_eq_one K x

end AbstractSimplicialComplex

end
