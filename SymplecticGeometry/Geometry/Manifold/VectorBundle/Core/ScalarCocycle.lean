/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import SymplecticGeometry.Topology.VectorBundle.Core.ScalarCocycle

import SymplecticGeometry.Geometry.Manifold.Algebra.ZPow

/-!
# Smoothness of the line bundles of a scalar cocycle

The line bundle `SymplecticGeometry.ScalarCocycle.lineBundleCore c k` of a scalar cocycle `c`
on a manifold is a `C^n` vector bundle core when the functions `g i j` of `c` are `C^n` on
the overlaps (`SymplecticGeometry.ScalarCocycle.isContMDiff_lineBundleCore`): its coordinate
changes are multiplication by the powers `g j i ^ k`, which are `C^n` where `g j i` does not
vanish.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978], Chapter 0,
  §5 (line bundles given by transition functions).
-/

public section

open Set
open scoped Manifold ContDiff

namespace SymplecticGeometry

namespace ScalarCocycle

variable {𝕜 X ι : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  (c : ScalarCocycle 𝕜 X ι)

/-- The line bundle of a scalar cocycle that is `C^n` on the overlaps is a `C^n` vector bundle
core. With Mathlib's `VectorBundleCore.instContMDiffVectorBundle` this makes it a
`ContMDiffVectorBundle n`. -/
theorem isContMDiff_lineBundleCore {F H : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H} [ChartedSpace H X] {n : WithTop ℕ∞}
    (hg : ∀ i j, ContMDiffOn I 𝓘(𝕜) n (c.g i j) (c.U i ∩ c.U j)) (k : ℤ) :
    (c.lineBundleCore k).IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    rw [c.lineBundleCore_baseSet, c.lineBundleCore_baseSet,
      funext (c.lineBundleCore_coordChange k i j)]
    exact (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).contMDiff.comp_contMDiffOn
      (((hg j i).zpow (Or.inl fun _ hx ↦ c.g_ne_zero hx.1 hx.2)).mono fun _ hx ↦ ⟨hx.2, hx.1⟩)

end ScalarCocycle

end SymplecticGeometry

end
