/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# `C^n` sections of a vector bundle core in its charts

For a vector bundle core `Z` over a manifold `B` whose glued bundle is a `C^n` vector bundle
(for instance when `Z.IsContMDiff IB n`), a section `s` of `Z` is `C^n` exactly when, for every
index `i`, its coordinates `x ↦ Z.coordChange (Z.indexAt x) i x (s x)` in the chart `i` are `C^n`
on the base set of that chart (`VectorBundleCore.contMDiff_section_iff`). The base sets of a core
are open and cover `B`, so this follows from Mathlib's
`Bundle.Trivialization.contMDiffOn_section_iff` for each chart `Z.localTriv i` and
`contMDiffOn_iUnion_iff_of_isOpen`.

## Implementation notes

The proof follows that of Tau Ceti's `Projectivization.contMDiff_section_twistCore_iff`, for the
line bundles `𝒪(k)` on projective space, with the standard affine opens replaced by the base sets
of a general core.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace VectorBundleCore

variable {𝕜 B F ι : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : VectorBundleCore 𝕜 B F ι)

/-- **`C^n` sections of a vector bundle core in its charts.** A section `s` of a `C^n` vector
bundle glued from a core `Z` is `C^n` exactly when, for every index `i`, its coordinates
`x ↦ Z.coordChange (Z.indexAt x) i x (s x)` in the chart `i` are `C^n` on `Z.baseSet i`. -/
theorem contMDiff_section_iff [ContMDiffVectorBundle n F Z.Fiber IB] (s : ∀ x, Z.Fiber x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) ↔
      ∀ i, ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ Z.coordChange (Z.indexAt x) i x (s x))
        (Z.baseSet i) := by
  have key (i : ι) := by
    have : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
    exact (Z.localTriv i).contMDiffOn_section_iff (IB := IB) (n := n) (s := s)
      (Z.isOpen_baseSet i) subset_rfl
  have hcover : ⋃ i, Z.baseSet i = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨Z.indexAt x, Z.mem_baseSet_at x⟩
  rw [← contMDiffOn_univ, ← hcover, contMDiffOn_iUnion_iff_of_isOpen Z.isOpen_baseSet]
  refine forall_congr' fun i ↦ (key i).trans ?_
  simp only [localTriv_apply]

end VectorBundleCore

end
