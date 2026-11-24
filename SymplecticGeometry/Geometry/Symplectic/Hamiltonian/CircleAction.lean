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
import TauCeti.Geometry.Manifold.DeRham.Algebra
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


/-- **A symplectic action with a fixed point is Hamiltonian.** Let a compact path-connected Lie
group `G` act on a compact connected boundaryless symplectic manifold `(M, σ)` of dimension `2 n`,
`n ≥ 1`, preserving `σ`, and suppose that the wedge product with `[σ ^ (n - 1)]` is injective on
`H¹(M)`. If the action has a fixed point, then it has a moment map. -/
theorem exists_isMomentMap_of_mem_fixedPoints [I.Boundaryless] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] {n : ℕ} (hn : 1 ≤ n) (hE : Module.finrank ℝ E = 2 * n)
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) g) σ = σ)
    (hL : Function.Injective (deRhamCohomology.wedge I M (2 * (n - 1)) 1
      (deRhamCohomology.mk I _ ⟨σ.wedgePow (n - 1), SmoothForm.wedgePow_mem_closedForms
        ((mem_closedForms I σ).mpr ((SmoothForm.isClosed_def σ).1 hσ.isClosed)) _⟩)))
    {p : M} (hp : p ∈ MulAction.fixedPoints G M) :
    ∃ μ : M → Module.Dual ℝ (GroupLieAlgebra J G),
      σ.IsMomentMap (InfinitesimalAction.fundamental J G I M) μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [SmoothTwoForm.exists_isMomentMap_iff]
  intro ξ
  let X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
    ⟨fundamentalVectorField I ξ, contMDiff_fundamentalVectorField (m := ∞) (n := ∞) (by simp) ξ⟩
  have hX : X ∈ σ.symplecticVectorFields :=
    (SmoothTwoForm.mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ.isClosed).2
      (mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ)
  have hXc : σ.interiorₗ X ∈ closedForms I M 1 := (mem_closedForms I _).2 (by
    rw [SmoothTwoForm.coe_interiorₗ]; exact SmoothTwoForm.mem_symplecticVectorFields_iff.1 hX)
  have hσc : σ ∈ closedForms I M 2 :=
    (mem_closedForms I σ).2 ((SmoothForm.isClosed_def σ).1 hσ.isClosed)
  -- By the vanishing integral and the nondegeneracy of the pairing, `ι_X σ ∧ σ ^ m` is exact.
  let o : Manifold.Orientation I M (Fin (1 + (1 + 2 * m))) :=
    (hσ.isNondegenerate.volumeOrientation hE).reindex (finCongr (by omega))
  have hη : SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow m) ∈ exactForms I M (1 + 2 * m) := by
    refine mem_exactForms_of_forall_integralTopForm_wedge_eq_zero o
      (SmoothForm.wedge_mem_closedForms hXc (SmoothForm.wedgePow_mem_closedForms hσc m))
      fun γ hγ ↦ ?_
    rw [SmoothForm.coe_wedge, SmoothTwoForm.coe_interiorₗ, ContMDiffSection.coeFn_mk]
    exact integralTopForm_wedge_interior_wedge_wedgePow_eq_zero o hσ.isClosed hinv hp ξ hγ
  -- Hence `[σ ^ m] ∧ [ι_X σ] = ± [ι_X σ ∧ σ ^ m] = 0`, and `[ι_X σ] = 0` by injectivity.
  have hcls : σ.interiorClass ⟨X, hX⟩ = 0 := by
    refine hL ?_
    rw [map_zero]
    have hcomm := deRhamCohomology.wedge_comm (σ.interiorClass ⟨X, hX⟩)
      (deRhamCohomology.mk I _ ⟨σ.wedgePow m, SmoothForm.wedgePow_mem_closedForms hσc m⟩)
    rw [SmoothTwoForm.interiorClass_apply, deRhamCohomology.wedge_mk,
      (deRhamCohomology.mk_eq_zero_iff I _ _).2 hη, one_mul, pow_mul, neg_one_sq, one_pow,
      one_smul] at hcomm
    -- The two degrees `1 + 2 m` and `2 m + 1` agree.
    have key {i j : ℕ} (h : i = j) (x : deRhamCohomology I M j)
        (hx : GradedMonoid.mk i (0 : deRhamCohomology I M i) = GradedMonoid.mk j x) : x = 0 := by
      subst h
      exact (eq_of_heq (Sigma.mk.inj hx).2).symm
    rw [SmoothTwoForm.interiorClass_apply]
    exact key (by omega) _ hcomm
  obtain ⟨φ, hφ⟩ := (SmoothTwoForm.interiorClass_eq_zero_iff _).1 hcls
  rw [Submodule.coe_mk, ContMDiffSection.coeFn_mk] at hφ
  exact ⟨fun y ↦ φ.val y 0, SmoothForm.contMDiff_apply_zero φ,
    by rw [InfinitesimalAction.fundamental_apply]; exact hφ⟩

/-- **The Frankel–Ono criterion.** Let `(M, σ)` be a compact connected boundaryless symplectic
manifold of dimension `2 n`, `n ≥ 1`, on which the wedge product with `[σ ^ (n - 1)]` is injective
from `H¹(M)` to `H^{2n-1}(M)`, and let the circle act smoothly on `M`, preserving `σ`. Then the
action is Hamiltonian, `ι_{X_ξ} σ = -d⟨μ, ξ⟩` for a map `μ : M → 𝔤*`, exactly when it has a fixed
point.

Milestone: *Frankel–Ono Hamiltonianity criterion*. -/
theorem exists_isMomentMap_iff_exists_mem_fixedPoints [I.Boundaryless] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] {n : ℕ} (hn : 1 ≤ n) (hE : Module.finrank ℝ E = 2 * n)
    {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
    [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
    (hinv : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    (hL : Function.Injective (deRhamCohomology.wedge I M (2 * (n - 1)) 1
      (deRhamCohomology.mk I _ ⟨σ.wedgePow (n - 1), SmoothForm.wedgePow_mem_closedForms
        ((mem_closedForms I σ).mpr ((SmoothForm.isClosed_def σ).1 hσ.isClosed)) _⟩))) :
    (∃ μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle),
        σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) (fun x ↦ -μ x)) ↔
      ∃ p : M, p ∈ MulAction.fixedPoints Circle M := by
  refine ⟨fun ⟨μ, h⟩ ↦ exists_mem_fixedPoints_of_isMomentMap hσ.isNondegenerate h,
    fun ⟨p, hp⟩ ↦ ?_⟩
  obtain ⟨μ, h⟩ := exists_isMomentMap_of_mem_fixedPoints (J := 𝓡 1) hn hE hσ hinv hL hp
  exact ⟨fun x ↦ -μ x, by simpa only [neg_neg] using h⟩
end Integral
end SymplecticGeometry
