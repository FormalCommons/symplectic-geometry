/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.LocalAtTarget

/-!
# Second countability of manifolds

A σ-compact space with charts in `H`, for a model with corners `I : ModelWithCorners 𝕜 E H` on a
second countable space `E`, is second countable
(`ModelWithCorners.secondCountableTopology_of_sigmaCompact`). It combines Mathlib's
`ModelWithCorners.secondCountableTopology` and `ChartedSpace.secondCountable_of_sigmaCompact`.
It is not an instance, since `SecondCountableTopology M` does not determine `I`.

In a space with charts in a second countable `H`, a Lindelöf set `s`, such as the image of a
second countable space under a continuous map, has inside each open neighbourhood `O` a second
countable open neighbourhood (`IsLindelof.exists_opens_secondCountableTopology`): countably many
chart domains meet `s` in sets covering it, and their union, cut down to `O`, is covered by
countably many second countable open sets. Theorems stated for second countable manifolds then
apply near `s` in any manifold.

A space `X` with an inducing map `f` into such a space, where the image of `f` has compact
closure, is second countable
(`Topology.IsInducing.secondCountableTopology_of_isCompact_closure`): the closure is compact,
hence Lindelöf, so `f` lands in one of the second countable open sets above, and `X` is second
countable as a subspace of it.
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

open Set TopologicalSpace in
/-- In a space with charts in a second countable `H`, a Lindelöf set `s` inside an open set `O`
has an open neighbourhood `U ⊆ O` that is second countable: countably many chart domains, cut
down to `O`, cover `s`. -/
theorem IsLindelof.exists_opens_secondCountableTopology {H M : Type*} [TopologicalSpace H]
    [SecondCountableTopology H] [TopologicalSpace M] [ChartedSpace H M] {s O : Set M}
    (hs : IsLindelof s) (hO : IsOpen O) (hsO : s ⊆ O) :
    ∃ U : Opens M, s ⊆ U ∧ (U : Set M) ⊆ O ∧ SecondCountableTopology U := by
  obtain ⟨t, htc, -, hst⟩ := hs.elim_nhds_subcover (fun x ↦ (chartAt H x).source ∩ O)
    fun x hx ↦ Filter.inter_mem (chart_source_mem_nhds H x) (hO.mem_nhds (hsO hx))
  let U : Opens M := ⟨⋃ x ∈ t, (chartAt H x).source ∩ O,
    isOpen_biUnion fun x _ ↦ (chartAt H x).open_source.inter hO⟩
  refine ⟨U, hst, iUnion₂_subset fun _ _ ↦ inter_subset_right, ?_⟩
  have := htc.to_subtype
  have (x : t) : SecondCountableTopology (((↑) : U → M) ⁻¹' (chartAt H (x : M)).source) := by
    have := (chartAt H (x : M)).secondCountableTopology_source
    exact (Topology.IsInducing.subtypeVal.restrictPreimage _).secondCountableTopology
  refine secondCountableTopology_of_countable_cover
    (fun x : t ↦ (chartAt H (x : M)).open_source.preimage continuous_subtypeVal) ?_
  refine eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.1 hy
  exact mem_iUnion.2 ⟨⟨x, hx⟩, hy.1⟩

open Set in
/-- A space with an inducing map into a space with charts in a second countable `H`, whose image
has compact closure, is second countable. -/
theorem Topology.IsInducing.secondCountableTopology_of_isCompact_closure {H M X : Type*}
    [TopologicalSpace H] [SecondCountableTopology H] [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace X] {f : X → M} (hf : IsInducing f) (hK : IsCompact (closure (range f))) :
    SecondCountableTopology X := by
  obtain ⟨U, hU, -, _⟩ := hK.isLindelof.exists_opens_secondCountableTopology (H := H)
    isOpen_univ (subset_univ _)
  exact (hf.codRestrict fun x ↦ hU (subset_closure (mem_range_self x))).secondCountableTopology

end
