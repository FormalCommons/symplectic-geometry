/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Zero sets of continuous sections

For a topological vector bundle `E → B` and a map `b : M → B`, the set of points where a
continuous section of `E` along `b` vanishes is closed in `M`. In a local trivialization the
section becomes a continuous map into the model fibre, and it vanishes exactly where that map
does.

The argument adapts the closedness step in the proof of Tau Ceti's
`TauCeti.finite_sectionZero_of_contMDiff`.

## Main results

* `VectorBundle.isClosed_setOf_eq_zero`: the zero set of a continuous section along a map is
  closed.
-/

public section

open Bundle Topology

namespace VectorBundle

variable {𝕜 M B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace M] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (𝕜) in
include 𝕜 in
/-- The zero set of a continuous section of a topological vector bundle along a map
`b : M → B` is closed in `M`. -/
theorem isClosed_setOf_eq_zero {b : M → B} {s : ∀ y, E (b y)}
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)) : IsClosed {x | s x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  let e := trivializationAt F E (b x)
  have hxe : b x ∈ e.baseSet := mem_baseSet_trivializationAt F E (b x)
  have heq (y : M) (hy : b y ∈ e.baseSet) : (e ⟨b y, s y⟩).2 = 0 ↔ s y = 0 :=
    e.snd_apply_eq_zero_iff 𝕜 hy
  have hc : ContinuousAt (fun y ↦ (e ⟨b y, s y⟩).2) x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.2 hxe))).snd.comp
      hs.continuousAt
  have hb : ContinuousAt b x := ((FiberBundle.continuous_proj F E).comp hs).continuousAt
  filter_upwards [hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (mt (heq x hxe).1 hx)),
    hb.preimage_mem_nhds (e.open_baseSet.mem_nhds hxe)] with y hy hye
  exact mt (heq y hye).2 hy

end VectorBundle

end
