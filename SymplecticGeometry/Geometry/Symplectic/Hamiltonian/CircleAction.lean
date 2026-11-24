/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.PoincarePairing.Nondegenerate
public import SymplecticGeometry.Geometry.Manifold.DeRham.Wedge
public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
public import TauCeti.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Average
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantForm
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.WeaklyHamiltonian
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical
import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Hamiltonian circle actions

-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped Manifold ContDiff

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **A Hamiltonian circle action has a fixed point.** -/
theorem exists_mem_fixedPoints_of_isMomentMap [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [Nonempty M] [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ) :
    ∃ p : M, p ∈ MulAction.fixedPoints Circle M := by
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (h.contMDiff circlePeriodOneGenerator).continuous.continuousOn
  refine ⟨p, ?_⟩
  have hcrit := (hp.isLocalMax Filter.univ_mem).mem_criticalPoints (I := I)
  rw [h.mem_criticalPoints_iff (hσ.nondegenerate_bilinFormAt p),
    InfinitesimalAction.fundamental_apply] at hcrit
  have : ContMDiffSMul (𝓡 1) I 2 Circle M := ContMDiffSMul.of_le (M := M) ENat.LEInfty.out
  exact mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero.2 hcrit

end SymplecticGeometry
