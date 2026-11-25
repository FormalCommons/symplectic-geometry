/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap

/-!
# Symplectic maps on a set, pointwise

A map `φ` that is symplectic on a set `s` from `σ` to `σ'`, in the sense of Tau Ceti's
`TauCeti.SmoothTwoForm.IsSymplecticMapOn`, pulls `σ'` back to `σ` at each point of `s`
(`TauCeti.SmoothTwoForm.IsSymplecticMapOn.mpullback_apply`). This is the pointwise form, on a
set and with no regularity of `φ`, of Tau Ceti's
`TauCeti.SmoothTwoForm.isSymplecticMap_iff_mpullback_eq`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M E' H' M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {σ : SmoothTwoForm I M} {σ' : SmoothTwoForm I' M'} {φ : M → M'} {s : Set M}

/-- A symplectic map on `s` from `σ` to `σ'` pulls `σ'` back to `σ` at each point of `s`. -/
theorem IsSymplecticMapOn.mpullback_apply (h : σ.IsSymplecticMapOn σ' φ s) {x : M}
    (hx : x ∈ s) : TauCeti.mpullback I I' φ σ'.val x = σ.val x := by
  ext v
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  have h' := h.apply hx (v 0) (v 1)
  rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, ← hv] at h'
  rw [← h', TauCeti.mpullback_apply, hv]
  congr 1
  funext i
  fin_cases i <;> rfl

end TauCeti.SmoothTwoForm

end
