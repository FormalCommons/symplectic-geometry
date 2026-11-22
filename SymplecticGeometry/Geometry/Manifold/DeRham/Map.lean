/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullbacks of closed forms

A complement to Tau Ceti's `TauCeti/Geometry/Manifold/DeRham/Map.lean`: the membership form of
the fact that a smooth map pulls closed forms back to closed forms,
`TauCeti.SmoothForm.mpullback_mem_closedForms`. It lets a caller state closedness of
`SmoothForm.mpullback f hf φ` directly, without passing through the subtype map
`TauCeti.closedForms.mpullback`.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §2 (pullback
  commutes with the exterior derivative).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']

/-- The pullback of a closed smooth form along a smooth map is closed. -/
theorem mpullback_mem_closedForms (f : M → M') (hf : ContMDiff I I' ∞ f) {k : ℕ}
    {φ : SmoothForm I' M' ℝ k} (hφ : φ ∈ closedForms I' M' k) :
    SmoothForm.mpullback f hf φ ∈ closedForms I M k := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, SmoothForm.mextDerivₗ_mpullback,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I' φ).mp hφ, map_zero]

end TauCeti.SmoothForm

end
