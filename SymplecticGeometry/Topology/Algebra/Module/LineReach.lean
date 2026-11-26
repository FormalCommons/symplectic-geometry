/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Points that reach a closed set along a line

Let `A` be a closed set in a topological space `E` with a continuous addition and a continuous
scalar action of a topological space `R`, and let `K ⊆ R` be compact. The pairs `(c, v)` with
`c + s • v ∈ A` for some `s ∈ K` form a closed set
(`IsClosed.setOfPred_exists_mem_fst_add_smul_snd_mem`): it is the projection, along the compact
factor `K`, of a closed subset of `(E × E) × K`, and Mathlib's `isClosedMap_fst_of_compactSpace`
says that such a projection is closed. For a fixed `v`, the points `c` with `c + s • v ∈ A` for
some `s ∈ K` are the preimage of that set under `c ↦ (c, v)`, so they form a closed set too
(`IsClosed.setOfPred_exists_mem_add_smul_mem`).

In a normed space over a proper normed field, `K` is typically `Metric.closedBall 0 ρ`.
-/

public section

open Set

variable {R E : Type*} [TopologicalSpace R] [TopologicalSpace E] [Add E] [ContinuousAdd E]
  [SMul R E] [ContinuousSMul R E] {A : Set E}

/-- The pairs `(c, v)` from which a closed set can be reached by a move `s • v` with `s` in a
compact set `K` of scalars form a closed set. -/
theorem IsClosed.setOfPred_exists_mem_fst_add_smul_snd_mem (hA : IsClosed A) {K : Set R}
    (hK : IsCompact K) : IsClosed {q : E × E | ∃ s ∈ K, q.1 + s • q.2 ∈ A} := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  convert isClosedMap_fst_of_compactSpace (X := E × E) (Y := K) _
    (hA.preimage (f := fun q : (E × E) × K ↦ q.1.1 + (q.2 : R) • q.1.2) (by fun_prop)) using 1
  ext q
  simp only [mem_ofPred_eq, mem_image, mem_preimage, Prod.exists, exists_and_right,
    exists_eq_right, Subtype.exists, exists_prop]

/-- The points from which a closed set can be reached by a move `s • v` with `s` in a compact
set `K` of scalars form a closed set. -/
theorem IsClosed.setOfPred_exists_mem_add_smul_mem (hA : IsClosed A) (v : E) {K : Set R}
    (hK : IsCompact K) : IsClosed {c : E | ∃ s ∈ K, c + s • v ∈ A} := by
  simpa only [preimage_ofPred_eq] using
    (hA.setOfPred_exists_mem_fst_add_smul_snd_mem hK).preimage
      (by fun_prop : Continuous fun c : E ↦ (c, v))

end
