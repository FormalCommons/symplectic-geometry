/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Bijective
import TauCeti.Geometry.Manifold.DeRham.PoincarePairing.Basic

/-!
# Exactness of differences of top forms on a closed connected manifold

On a compact, preconnected, boundaryless, Hausdorff oriented manifold of dimension `k`, two
smooth `k`-forms differ by an exact form exactly when their oriented integrals agree
(`TauCeti.sub_mem_exactForms_iff_integralTopForm_eq`). Every form on a compact manifold is
compactly supported, so this follows from Tau Ceti's top-degree Poincaré lemma
`TauCeti.mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero`, together with
`TauCeti.exactCompactlySupportedForms_eq_exactForms` and
`TauCeti.integralTopForm_sub_of_mem_compactlySupportedForms`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §5.
-/

public section

open scoped ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]
  [PreconnectedSpace M] {k : ℕ}

/-- On a compact, preconnected, boundaryless, Hausdorff manifold of dimension `k` with an
orientation `o`, the difference `σ - τ` of two smooth top forms is exact exactly when `σ` and `τ`
have equal integrals over `M`. -/
theorem sub_mem_exactForms_iff_integralTopForm_eq (o : Manifold.Orientation I M (Fin k))
    {σ τ : SmoothForm I M ℝ k} :
    σ - τ ∈ exactForms I M k ↔ integralTopForm o σ.val = integralTopForm o τ.val := by
  rw [← exactCompactlySupportedForms_eq_exactForms,
    mem_exactCompactlySupportedForms_iff_integralTopForm_eq_zero o
      (by simp [compactlySupportedForms_eq_top]),
    integralTopForm_sub_of_mem_compactlySupportedForms o
      (by simp [compactlySupportedForms_eq_top]) (by simp [compactlySupportedForms_eq_top]),
    sub_eq_zero]

end TauCeti

end
