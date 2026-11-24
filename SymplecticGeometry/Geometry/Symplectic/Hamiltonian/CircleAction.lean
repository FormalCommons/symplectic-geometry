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
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
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


section Integral

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H' G] [Group G] [LieGroup J ∞ G] [T2Space G]
  [CompactSpace G] [PathConnectedSpace G] [MulAction G M] [ContMDiffSMul J I ∞ G M]

/-- **The vanishing integral.** Let a compact path-connected Lie group `G` act on a compact
connected boundaryless manifold `M` of dimension `2 n + 2`, preserving a closed two-form `σ`, and
let the action have a fixed point. Then for every closed one-form `γ` and every `ξ` in the Lie
algebra of `G`, with fundamental vector field `X_ξ`, the integral of `γ ∧ ι_{X_ξ} σ ∧ σ ^ n` over
`M` vanishes, for any orientation of `M`. -/
theorem integralTopForm_wedge_interior_wedge_wedgePow_eq_zero [I.Boundaryless] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] {n : ℕ}
    (o : Manifold.Orientation I M (Fin (1 + (1 + 2 * n))))
    {σ : SmoothTwoForm I M} (hσ : σ.IsClosed)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) σ = σ)
    {p : M} (hp : p ∈ MulAction.fixedPoints G M) (ξ : GroupLieAlgebra J G)
    {γ : SmoothForm I M ℝ 1} (hγ : γ ∈ closedForms I M 1) :
    integralTopForm o (RoughForm.wedge (γ : RoughForm I M ℝ 1)
      (RoughForm.wedge (RoughForm.interior (k := 1) (fundamentalVectorField I ξ)
        (σ : RoughForm I M ℝ 2)) (σ.wedgePow n : RoughForm I M ℝ (2 * n)))) = 0 := by
  have hE : Module.finrank ℝ E = 2 * n + 2 := by
    have := o.card_eq
    simp only [Fintype.card_fin] at this
    omega
  borelize G
  have := topologicalGroup_of_lieGroup J ∞ (G := G)
  -- The average `γ'` of `γ` over `G` is closed, invariant and cohomologous to `γ`.
  set γ' := SmoothForm.measureAverage J (haarProb G) γ
  have hγc : γ.IsClosed := (SmoothForm.isClosed_def γ).2 ((mem_closedForms I γ).1 hγ)
  have hγ'c : mextDeriv γ'.val = 0 :=
    (SmoothForm.isClosed_def _).1 (SmoothForm.IsClosed.measureAverage J (haarProb G) hγc)
  have hγ'inv (g : G) : SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) γ' = γ' :=
    Subtype.ext <| by
      rw [SmoothForm.coe_mpullback, SmoothForm.mpullback_smul_measureAverage J (haarProb G) γ g]
  have hγγ' : γ - γ' ∈ exactForms I M 1 := by
    simpa using neg_mem (SmoothForm.measureAverage_sub_mem_exactForms_one J (haarProb G) hγ)
  -- The form `ι_{X_ξ} σ ∧ σ ^ n` is closed, as `X_ξ` is a symplectic vector field.
  let X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
    ⟨fundamentalVectorField I ξ, contMDiff_fundamentalVectorField (m := ∞) (n := ∞) (by simp) ξ⟩
  have hX : X ∈ σ.symplecticVectorFields :=
    (SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ).2
      (mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ)
  have hη : SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow n) ∈ closedForms I M (1 + 2 * n) :=
    SmoothForm.wedge_mem_closedForms ((mem_closedForms I _).2 (by
      rw [SmoothTwoForm.coe_interiorₗ]; exact SmoothTwoForm.mem_symplecticVectorFields_iff.1 hX))
      (SmoothForm.wedgePow_mem_closedForms ((mem_closedForms I σ).2 ((SmoothForm.isClosed_def σ).1 hσ)) n)
  have hcoe : RoughForm.wedge (RoughForm.interior (k := 1) (fundamentalVectorField I ξ)
      (σ : RoughForm I M ℝ 2)) (σ.wedgePow n : RoughForm I M ℝ (2 * n)) =
      (SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow n) : RoughForm I M ℝ (1 + 2 * n)) := by
    rw [SmoothForm.coe_wedge, SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
  rw [hcoe, integralTopForm_wedge_eq_of_sub_mem_exactForms_left o hγ hγγ' hη, ← hcoe]
  -- The function `γ'(X_ξ)` is constant and vanishes at the fixed point `p`, so the integrand is
  -- zero.
  have hγ'X (x : M) : γ'.val x ![fundamentalVectorField I ξ x] = 0 := by
    rw [apply_fundamentalVectorField_eq_of_preconnectedSpace hγ'c hγ'inv ξ x p,
      fundamentalVectorField_eq_zero_of_forall_smul_eq hp ξ]
    exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl
  have h0 : RoughForm.wedge (γ' : RoughForm I M ℝ 1) (RoughForm.wedge (RoughForm.interior
      (k := 1) (fundamentalVectorField I ξ) (σ : RoughForm I M ℝ 2))
        (σ.wedgePow n : RoughForm I M ℝ (2 * n))) = 0 :=
    funext fun x ↦ SmoothForm.wedge_interior_wedge_wedgePow_apply_eq_zero hE _ σ _ (hγ'X x)
  rw [h0, integralTopForm_zero]

end Integral
end SymplecticGeometry
