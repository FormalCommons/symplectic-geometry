/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.SymplecticGroup
public import TauCeti.Topology.Algebra.SymplecticGroup
import TauCeti.Geometry.Manifold.SmoothApprox.Basic

/-!
# Smooth representatives of maps into the symplectic group

Every continuous map from a compact Hausdorff manifold, possibly with boundary, into the group
`GLSymplectic κ ℝ` of real symplectic matrices is homotopic to one that is smooth as a map into
Tau Ceti's Lie group `Matrix.symplecticGroup κ ℝ`. This is Tau Ceti's Whitney approximation,
`ContinuousMap.exists_contMDiff_homotopic_of_isCompact_closure_range`, transported along
`symplecticGroupContinuousMulEquiv`.

The file is apart from `Basic.lean` so that the files that only need the smooth structure of the
group do not import Whitney approximation.

## Main results

* `ContinuousMap.exists_homotopic_contMDiff_symplecticGroup`: a continuous map from a compact
  manifold to the symplectic group is homotopic to a smooth one.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218, 2013, Theorem 6.26
  (Whitney approximation).
-/

public section

noncomputable section

open TauCeti TauCeti.GLSymplectic
open scoped Manifold ContDiff

namespace ContinuousMap

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [CompactSpace N] [T2Space N] {κ : Type*} [Fintype κ] [DecidableEq κ]

open scoped Matrix.Norms.Operator in
/-- **Smooth representatives of maps into the symplectic group.** A continuous map `f` from a
compact Hausdorff manifold, possibly with boundary, to `Sp(2k)` is homotopic to a map `g` that is
smooth as a map into Tau Ceti's manifold `Matrix.symplecticGroup κ ℝ`. -/
theorem exists_homotopic_contMDiff_symplecticGroup (f : C(N, GLSymplectic κ ℝ)) :
    ∃ g : C(N, GLSymplectic κ ℝ), f.Homotopic g ∧
      letI := Matrix.linftyOpTopologicalSpace (κ ⊕ κ) (κ ⊕ κ) ℝ
      ContMDiff I 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ) ∞
        fun x ↦ (symplecticGroupContinuousMulEquiv κ ℝ).symm (g x) := by
  -- Tau Ceti's charts on the symplectic group are stated for the topology of the operator norm
  -- on matrices, which is the product topology, but not reducibly so.
  let := Matrix.linftyOpTopologicalSpace (κ ⊕ κ) (κ ⊕ κ) ℝ
  let e := symplecticGroupContinuousMulEquiv κ ℝ
  let f' : C(N, Matrix.symplecticGroup κ ℝ) := (ContinuousMap.mk _ e.symm.continuous).comp f
  obtain ⟨g, hg, hfg⟩ := f'.exists_contMDiff_homotopic_of_isCompact_closure_range (I := I)
    (J := 𝓘(ℝ, Lie.SymplecticGroupModel κ ℝ)) ⊤ (isCompact_range f'.continuous).closure
  refine ⟨(ContinuousMap.mk _ e.continuous).comp g, ?_,
    hg.congr fun x ↦ ?_⟩
  · convert (ContinuousMap.Homotopic.refl (ContinuousMap.mk _ e.continuous)).comp hfg using 1
    ext1 x
    exact (e.apply_symm_apply (f x)).symm
  · -- The two sides use the two topologies on matrices, so `rw` cannot see the composite.
    change e.symm (e (g x)) = g x
    exact e.symm_apply_apply (g x)

end ContinuousMap

end
