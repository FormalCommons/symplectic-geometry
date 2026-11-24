/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport

/-!
# Compactly supported de Rham cohomology: exact forms on a compact manifold

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/DeRham/CompactSupport.lean`,
copied from Tau Ceti's main branch at commit `8ea6f162b84fee7b5439dc2b58e51e86aaa1b722`, which
the pinned version of Tau Ceti does not have yet. It contains one declaration,
`TauCeti.exactCompactlySupportedForms_eq_exactForms`: on a compact manifold, the compactly
supported exact forms are the exact forms.

Apart from this module docstring, nothing is changed from Tau Ceti's text.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17,
  "Cohomology with Compact Support".
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Complex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- On a compact manifold every form is compactly supported, so the compactly supported exact
forms are exactly the exact forms. -/
@[simp]
theorem exactCompactlySupportedForms_eq_exactForms [CompactSpace M] (k : ℕ) :
    exactCompactlySupportedForms I M k = exactForms I M k := by
  cases k with
  | zero => rw [exactCompactlySupportedForms_zero, exactForms_zero]
  | succ k =>
      rw [exactCompactlySupportedForms_succ, exactForms_succ, compactlySupportedForms_eq_top,
        Submodule.map_top]

end Complex

end TauCeti
