/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import SymplecticGeometry.Geometry.Manifold.DeRham.PoincarePairing.Nondegenerate
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Average
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import SymplecticGeometry.Geometry.Manifold.GroupAction.InvariantForm
import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.WeaklyHamiltonian
import TauCeti.Geometry.Manifold.DeRham.Algebra
import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ConvexHull
import TauCeti.Geometry.Symplectic.Manifold.Volume
import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Hamiltonian circle actions

A smooth action of a Lie group `G` on a symplectic manifold `(M, σ)` that preserves `σ` is
Hamiltonian when it has a moment map. This file proves the Frankel–Ono criterion: under a
cohomological condition on `σ`, which holds for instance on closed Kähler manifolds by the hard
Lefschetz theorem, a circle action preserving `σ` on a closed connected manifold has a moment map
exactly when some point is fixed by the whole circle.

One direction holds without the condition, and for every compact connected commutative Lie
group: it is Tau Ceti's `TauCeti.SmoothTwoForm.IsMomentMap.nonempty_fixedPoints`.

For the other direction we follow the proof of McDuff–Salamon, with an integral identity in place
of the Poincaré dual of an orbit. Let `X = X_ξ` be the fundamental vector field of some `ξ`, so
that `ι_X σ` is closed, and let `M` have dimension `2 n + 2`.

* For every closed one-form `γ`, the integral of `γ ∧ ι_X σ ∧ σ ^ n` vanishes when the action has
  a fixed point `p`. The integral depends only on the class of `γ`, and averaging `γ` over the
  compact connected group gives a cohomologous invariant form `γ'`
  (`TauCeti.SmoothForm.exists_invariant_sub_mem_exactForms_one`, stated for a boundaryless
  manifold whose model may have boundary). By Cartan's formula the function
  `γ'(X)` is constant (`TauCeti.apply_fundamentalVectorField_eq_of_preconnectedSpace`), and it
  vanishes at `p`, where `X` does. A top-degree computation
  (`TauCeti.SmoothForm.wedge_interior_wedge_wedgePow_apply_eq_zero`) then makes the integrand
  `γ' ∧ ι_X σ ∧ σ ^ n` vanish.
* By the nondegeneracy of the Poincaré pairing in degrees `(1, 2 n + 1)`
  (`TauCeti.mem_exactForms_of_forall_integralTopForm_wedge_eq_zero`), the form
  `ι_X σ ∧ σ ^ n` is exact. If the wedge product with `[σ ^ n]` is injective on `H¹(M)`, it
  follows that `[ι_X σ] = 0`, so `X` is a Hamiltonian vector field
  (`TauCeti.SmoothTwoForm.interiorClass_eq_zero_iff`), and the Hamiltonians of all the `X_ξ`
  assemble into a moment map (`TauCeti.SmoothTwoForm.exists_isMomentMap_iff`).

The first two steps hold for any compact path-connected Lie group, and are stated so.

## Main results

* `SymplecticGeometry.integralTopForm_wedge_interior_wedge_wedgePow_eq_zero`: for a symplectic
  action of a compact path-connected Lie group with a fixed point, `∫_M γ ∧ ι_X σ ∧ σ ^ n = 0`
  for every closed one-form `γ`.
* `SymplecticGeometry.exists_isMomentMap_of_mem_fixedPoints`: under the cohomological condition,
  such an action with a fixed point has a moment map.
* `SymplecticGeometry.exists_isMomentMap_iff_exists_mem_fixedPoints`: the Frankel–Ono criterion.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  Theorem 5.1.6 and its proof.
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
theorem integralTopForm_wedge_interior_wedge_wedgePow_eq_zero [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] {n : ℕ}
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
  -- Averaging gives a closed invariant `γ'` cohomologous to `γ`.
  obtain ⟨γ', hγ'cl, hγ'inv, hγ'γ⟩ :=
    SmoothForm.exists_invariant_sub_mem_exactForms_one J (haarProb G) hγ
  have hγ'c : mextDeriv γ'.val = 0 := (mem_closedForms I γ').1 hγ'cl
  have hγγ' : γ - γ' ∈ exactForms I M 1 := by simpa using neg_mem hγ'γ
  -- The form `ι_{X_ξ} σ ∧ σ ^ n` is closed, as `X_ξ` is a symplectic vector field.
  set X := (InfinitesimalAction.fundamental J G I M).toSectionLinearMap ξ
  have hη : SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow n) ∈ closedForms I M (1 + 2 * n) :=
    SmoothForm.wedge_mem_closedForms
      (SmoothTwoForm.interiorₗ_fundamental_toSectionLinearMap_mem_closedForms hσ hinv ξ)
      (SmoothForm.wedgePow_mem_closedForms
        ((mem_closedForms I σ).2 ((SmoothForm.isClosed_def σ).1 hσ)) n)
  have hcoe : RoughForm.wedge (RoughForm.interior (k := 1) (fundamentalVectorField I ξ)
      (σ : RoughForm I M ℝ 2)) (σ.wedgePow n : RoughForm I M ℝ (2 * n)) =
      (SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow n) : RoughForm I M ℝ (1 + 2 * n)) := by
    rw [SmoothForm.coe_wedge, SmoothTwoForm.coe_interiorₗ,
      InfinitesimalAction.coe_fundamental_toSectionLinearMap]
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
theorem exists_isMomentMap_of_mem_fixedPoints [BoundarylessManifold I M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] {n : ℕ} (hn : 1 ≤ n) (hE : Module.finrank ℝ E = 2 * n)
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
  set X := (InfinitesimalAction.fundamental J G I M).toSectionLinearMap ξ
  have hX : X ∈ σ.symplecticVectorFields :=
    SmoothTwoForm.fundamental_toSectionLinearMap_mem_symplecticVectorFields hσ.isClosed hinv ξ
  have hXc : σ.interiorₗ X ∈ closedForms I M 1 :=
    SmoothTwoForm.interiorₗ_fundamental_toSectionLinearMap_mem_closedForms hσ.isClosed hinv ξ
  have hσc : σ ∈ closedForms I M 2 :=
    (mem_closedForms I σ).2 ((SmoothForm.isClosed_def σ).1 hσ.isClosed)
  -- By the vanishing integral and the nondegeneracy of the pairing, `ι_X σ ∧ σ ^ m` is exact.
  let o : Manifold.Orientation I M (Fin (1 + (1 + 2 * m))) :=
    (hσ.isNondegenerate.volumeOrientation hE).reindex (finCongr (by omega))
  have hη : SmoothForm.wedge (σ.interiorₗ X) (σ.wedgePow m) ∈ exactForms I M (1 + 2 * m) := by
    refine mem_exactForms_of_forall_integralTopForm_wedge_eq_zero o
      (SmoothForm.wedge_mem_closedForms hXc (SmoothForm.wedgePow_mem_closedForms hσc m))
      fun γ hγ ↦ ?_
    rw [SmoothForm.coe_wedge, SmoothTwoForm.coe_interiorₗ,
      InfinitesimalAction.coe_fundamental_toSectionLinearMap]
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
  rw [Submodule.coe_mk, InfinitesimalAction.coe_fundamental_toSectionLinearMap] at hφ
  exact ⟨fun y ↦ φ.val y 0, SmoothForm.contMDiff_apply_zero φ,
    by rw [InfinitesimalAction.fundamental_apply]; exact hφ⟩

/-- **The Frankel–Ono criterion.** Let `(M, σ)` be a compact connected boundaryless symplectic
manifold of dimension `2 n`, `n ≥ 1`, on which the wedge product with `[σ ^ (n - 1)]` is injective
from `H¹(M)` to `H^{2n-1}(M)`, and let the circle act smoothly on `M`, preserving `σ`. Then the
action is Hamiltonian, `ι_{X_ξ} σ = -d⟨μ, ξ⟩` for a map `μ : M → 𝔤*`, exactly when it has a fixed
point.

Milestone: *Frankel–Ono Hamiltonianity criterion*. -/
theorem exists_isMomentMap_iff_exists_mem_fixedPoints [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] {n : ℕ} (hn : 1 ≤ n)
    (hE : Module.finrank ℝ E = 2 * n)
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
  refine ⟨fun ⟨μ, h⟩ ↦ h.nonempty_fixedPoints hσ.isNondegenerate, fun ⟨p, hp⟩ ↦ ?_⟩
  obtain ⟨μ, h⟩ := exists_isMomentMap_of_mem_fixedPoints (J := 𝓡 1) hn hE hσ hinv hL hp
  exact ⟨fun x ↦ -μ x, by simpa only [neg_neg] using h⟩

end Integral

end SymplecticGeometry
