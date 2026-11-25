/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction

/-!
# Maps into a realization that are locally supported on finitely many vertices

A map `f : X → K.Realization` into the weak realization of an abstract simplicial complex is
continuous when each barycentric coordinate `x ↦ f x i` is continuous and, near each point of
`X`, the points `f y` are all supported on one finite set of vertices
(`AbstractSimplicialComplex.continuous_of_forall_eventually_support_subset`). Near such a point
the map lands in the compact set of points supported on that finite set
(`AbstractSimplicialComplex.isCompact_setOf_support_subset`), on which the weak topology is that
of coordinatewise convergence
(`AbstractSimplicialComplex.isClosedEmbedding_realization_coe_restrict`).

## References

* A. Hatcher, *Algebraic Topology*, Appendix A, Proposition A.1.
-/

public section

open Set Topology Filter

namespace AbstractSimplicialComplex

variable {ι X : Type*} [TopologicalSpace X] {K : AbstractSimplicialComplex ι}

/-- A map into the weak realization of a simplicial complex is continuous if its barycentric
coordinates are continuous and, near each point, its values are supported on one finite set of
vertices. -/
theorem continuous_of_forall_eventually_support_subset {f : X → K.Realization}
    (hf : ∀ i, Continuous fun x => (f x : ι →₀ ℝ) i)
    (hloc : ∀ x₀, ∃ s : Finset ι, ∀ᶠ y in 𝓝 x₀, (f y : ι →₀ ℝ).support ⊆ s) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨s, hs⟩ := hloc x₀
  let S : Set K.Realization := {p | (p.val.support : Set ι) ⊆ s}
  have hS : IsCompact S := K.isCompact_setOf_support_subset _ s.finite_toSet
  let U : Set X := {y | (f y : ι →₀ ℝ).support ⊆ s}
  have hUS (y : U) : f y ∈ S := by
    simp only [S, Set.mem_ofPred_eq]
    exact_mod_cast y.property
  let g : U → S := fun y => ⟨f y, hUS y⟩
  have hg : Continuous g := by
    refine (K.isClosedEmbedding_realization_coe_restrict hS).isEmbedding.continuous_iff.2 ?_
    exact continuous_pi fun i => (hf i).comp continuous_subtypeVal
  refine ContinuousOn.continuousAt ?_ hs
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtypeVal.comp hg

end AbstractSimplicialComplex

end
