/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.LocalAtTarget

/-!
# Second countability of manifolds

A σ-compact space with charts in `H`, for a model with corners `I : ModelWithCorners 𝕜 E H` on a
second countable space `E`, is second countable
(`ModelWithCorners.secondCountableTopology_of_sigmaCompact`). It combines Mathlib's
`ModelWithCorners.secondCountableTopology` and `ChartedSpace.secondCountable_of_sigmaCompact`.
It is not an instance, since `SecondCountableTopology M` does not determine `I`.

A space `X` with an inducing map `f` into a space with charts in a second countable `H`, where
the image of `f` has compact closure, is second countable
(`Topology.IsInducing.secondCountableTopology_of_isCompact_closure`): finitely many chart domains
cover the closure of the image, and their preimages are second countable open sets that cover `X`.
-/

public section

namespace ModelWithCorners

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [SecondCountableTopology E]

/-- A σ-compact space with charts in the model space `H` of a model with corners on a second
countable space is second countable. -/
theorem secondCountableTopology_of_sigmaCompact (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] : SecondCountableTopology M :=
  haveI := I.secondCountableTopology
  ChartedSpace.secondCountable_of_sigmaCompact H M

end ModelWithCorners

open Set in
/-- A space with an inducing map into a space with charts in a second countable `H`, whose image
has compact closure, is second countable. -/
theorem Topology.IsInducing.secondCountableTopology_of_isCompact_closure {H M X : Type*}
    [TopologicalSpace H] [SecondCountableTopology H] [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace X] {f : X → M} (hf : IsInducing f) (hK : IsCompact (closure (range f))) :
    SecondCountableTopology X := by
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x ↦ (chartAt H x).source)
    fun x _ ↦ chart_source_mem_nhds H x
  have (x : t) : SecondCountableTopology (f ⁻¹' (chartAt H (x : M)).source) := by
    have := (chartAt H (x : M)).secondCountableTopology_source
    exact (hf.restrictPreimage _).secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun x : t ↦ (chartAt H (x : M)).open_source.preimage hf.continuous) ?_
  refine eq_univ_of_forall fun y ↦ ?_
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 (ht (subset_closure (mem_range_self y)))
  exact mem_iUnion.2 ⟨⟨x, hx⟩, hy⟩

end
