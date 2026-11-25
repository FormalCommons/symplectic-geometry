/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
import SymplecticGeometry.Geometry.Manifold.Immersion.Basic

/-!
# Lagrangian immersions from an empty manifold

This file adds to Tau Ceti's `TauCeti/Geometry/Symplectic/Lagrangian/Manifold.lean`, which
defines Lagrangian immersions (`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion`).
From an empty source, the immersion and isotropy conditions hold vacuously, so only the
dimension count `2 * dim N = dim M` is left.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianImmersion_iff_of_isEmpty`: a map from an
  empty manifold is a Lagrangian immersion exactly when the source has half the dimension of
  the target.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4.
-/

public section

open Module Manifold
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

/-- A map from an empty manifold `N` is a Lagrangian immersion exactly when the model space of
`N` has half the dimension of that of `M`. -/
theorem isLagrangianImmersion_iff_of_isEmpty [IsEmpty N] :
    hσ.IsLagrangianImmersion J f ↔ 2 * finrank ℝ E' = finrank ℝ E :=
  ⟨fun h ↦ h.two_mul_finrank, fun h ↦
    ⟨IsImmersion.of_isEmpty J I ∞ f, isIsotropicMap_iff_forall.2 isEmptyElim, h⟩⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
