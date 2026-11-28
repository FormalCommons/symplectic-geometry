/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
import TauCeti.Topology.VectorBundle.Trivialization
import SymplecticGeometry.Topology.FiberBundle.Basic

/-!
# Zero sets of continuous sections

For a topological vector bundle `E → B` and a map `b : M → B`, a section of `E` along `b` that
is continuous and nonzero at a point is nonzero near it, so the set of points where a continuous
section vanishes is closed in `M`. In a local trivialization the section becomes a map into the
model fibre, continuous where the section is, and it vanishes exactly where that map does.

The argument adapts the closedness step in the proof of Tau Ceti's
`TauCeti.finite_sectionZero_of_contMDiff`.

## Main results

* `VectorBundle.eventually_ne_zero`: a section along a map that is continuous and nonzero at a
  point is nonzero near it;
* `VectorBundle.isClosed_setOfPred_eq_zero`: the zero set of a continuous section along a map is
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
/-- A section of a topological vector bundle along a map `b : M → B` that is continuous at `x`
and does not vanish at `x` does not vanish near `x`. -/
theorem eventually_ne_zero {b : M → B} {s : ∀ y, E (b y)} {x : M}
    (hs : ContinuousAt (fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)) x) (hx : s x ≠ 0) :
    ∀ᶠ y in 𝓝 x, s y ≠ 0 := by
  let e := trivializationAt F E (b x)
  have hxe : b x ∈ e.baseSet := mem_baseSet_trivializationAt F E (b x)
  -- In the trivialization at `b x` the section becomes a map into `F`, continuous at `x`, that
  -- vanishes exactly where the section does.
  have hc : ContinuousAt (fun y ↦ (e ⟨b y, s y⟩).2) x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds (e.mem_source.2 hxe))).snd.comp hs
  have hb : ContinuousAt b x := (FiberBundle.continuous_proj F E).continuousAt.comp hs
  filter_upwards [hc.eventually_ne ((e.snd_apply_ne_zero_iff 𝕜 hxe).2 hx),
    hb.eventually_mem_baseSet_trivializationAt F E] with y hy hye
  exact (e.snd_apply_ne_zero_iff 𝕜 hye).1 hy

variable (𝕜) in
include 𝕜 in
/-- The zero set of a continuous section of a topological vector bundle along a map
`b : M → B` is closed in `M`. -/
theorem isClosed_setOfPred_eq_zero {b : M → B} {s : ∀ y, E (b y)}
    (hs : Continuous fun y ↦ (⟨b y, s y⟩ : TotalSpace F E)) : IsClosed {x | s x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  exact fun x hx ↦ eventually_ne_zero 𝕜 hs.continuousAt hx

end VectorBundle

end
