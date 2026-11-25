/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical

/-!
# Critical points of a circle moment map

Let a circle act smoothly on a Hausdorff boundaryless manifold `M`, with moment map `μ` for a
two-form `σ`, and let `H = ⟨μ, ξ₁⟩` be its component along the period-one generator
`ξ₁ = circlePeriodOneGenerator`. Where `σ` is nondegenerate, `x` is a critical point of `H`
exactly when the whole circle fixes `x`: by Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_iff`, `dH_x = 0` exactly when the
fundamental vector field of `ξ₁` vanishes at `x`, and by
`SymplecticGeometry.mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero` this happens
exactly at the fixed points of the action.

Since the Lie algebra of `Circle` is spanned by `ξ₁`, the cocycle of any map `μ` to its dual
vanishes, and the kernel of the differential of a moment map `μ` is that of `dH`. These are the
facts that Tau Ceti's reduction of a level of a moment map
(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`) asks for
in the circle case.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_circlePeriodOneGenerator_iff`: at a
  point where `σ` is nondegenerate, `x` is critical for `⟨μ, ξ₁⟩` exactly when `x` is a fixed
  point of the circle action.
* `TauCeti.SmoothTwoForm.momentCocycle_circle_eq_zero`: the cocycle of a map to the dual of the
  Lie algebra of `Circle` vanishes.
* `TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_circle`: the kernel of the differential of
  a circle moment map `μ` at `x` is that of `d⟨μ, ξ₁⟩`.
* `TauCeti.SmoothTwoForm.IsMomentMap.apply_smul_circle`: a circle moment map is invariant under
  the action, since `⟨μ, ξ₁⟩` is conserved along the curves `t ↦ exp(t ξ₁) • x`, which are
  integral curves of its Hamiltonian vector field and cover the orbits.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9.
-/

public section

open Manifold TauCeti SymplecticGeometry
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

section Cocycle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The cocycle of a circle moment map vanishes.** For any two-form `σ`, infinitesimal action
`a` of the Lie algebra of `Circle` and map `μ` to its dual, the cocycle
`σ(Z_M, Z'_M) - μ_{⁅Z, Z'⁆}` is zero at every point, since the Lie algebra of `Circle` is
one-dimensional. -/
theorem momentCocycle_circle_eq_zero (σ : SmoothTwoForm I M)
    (a : InfinitesimalAction (GroupLieAlgebra (𝓡 1) Circle) I M)
    (μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)) (x : M) :
    σ.momentCocycle a μ x = 0 := by
  refine momentCocycle_eq_zero_iff.2 fun Z Z' ↦ ?_
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_ne_zero_circle circlePeriodOneGenerator_ne_zero Z
  obtain ⟨d, rfl⟩ := exists_smul_eq_of_ne_zero_circle circlePeriodOneGenerator_ne_zero Z'
  rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero, map_zero,
    ← SmoothForm.bilinFormAt_apply, ← InfinitesimalAction.eval_apply,
    ← InfinitesimalAction.eval_apply, map_smul, map_smul, map_smul, LinearMap.smul_apply,
    map_smul, SmoothForm.isAlt_bilinFormAt, smul_zero, smul_zero]

/-- **The level tangent space of a circle moment map.** For a moment map `μ` of an infinitesimal
action of the Lie algebra of `Circle`, the kernel of the differential `dμ_x : T_x M → 𝔤*` is the
kernel of the differential of the single function `⟨μ, circlePeriodOneGenerator⟩`. -/
theorem IsMomentMap.ker_differential_circle {σ : SmoothTwoForm I M}
    {a : InfinitesimalAction (GroupLieAlgebra (𝓡 1) Circle) I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)} (h : σ.IsMomentMap a μ) (x : M) :
    LinearMap.ker (h.differential x) =
      LinearMap.ker (mfderiv I 𝓘(ℝ) (fun y ↦ μ y circlePeriodOneGenerator) x).toLinearMap := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hv
    have := LinearMap.congr_fun hv circlePeriodOneGenerator
    -- The tangent space of `ℝ` is `ℝ` by definition; `simpa` states the equation in `ℝ`.
    exact (by simpa using this : _ = (0 : ℝ))
  · intro hv
    refine linearMap_ext_of_ne_zero_circle circlePeriodOneGenerator_ne_zero ?_
    simp only [IsMomentMap.differential_apply, mvfderiv_apply_eq_mfderiv_apply,
      LinearMap.zero_apply]
    exact hv

end Cocycle

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MulAction Circle M]
  [ContMDiffSMul (𝓡 1) I ∞ Circle M] {σ : SmoothTwoForm I M}
  {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}

/-- **Critical points of a circle Hamiltonian.** For a smooth circle action on a Hausdorff
boundaryless manifold with moment map `μ` for `σ`, and a point `x` at which `σ` is
nondegenerate, `x` is a critical point of `H = ⟨μ, circlePeriodOneGenerator⟩` exactly when every
element of the circle fixes `x`. -/
theorem mem_criticalPoints_circlePeriodOneGenerator_iff [T2Space M] [BoundarylessManifold I M]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ)
    {x : M} (hσ : (σ.bilinFormAt x).Nondegenerate) :
    x ∈ criticalPoints I (fun y ↦ μ y circlePeriodOneGenerator) ↔
      x ∈ MulAction.fixedPoints Circle M := by
  rw [hμ.mem_criticalPoints_iff hσ, InfinitesimalAction.fundamental_apply,
    mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero (I' := I)]

/-- **A circle moment map is invariant.** For a smooth circle action with moment map `μ` for `σ`,
`μ (g • x) = μ x` for every `g` in the circle. -/
theorem apply_smul_circle
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ) (g : Circle)
    (x : M) : μ (g • x) = μ x := by
  refine linearMap_ext_of_ne_zero_circle circlePeriodOneGenerator_ne_zero ?_
  obtain ⟨t, rfl⟩ := mulInvariantExp_smul_circlePeriodOneGenerator_surjective g
  -- `t ↦ exp(t ξ₁) • x` is an integral curve of the Hamiltonian vector field of `⟨μ, ξ₁⟩`, along
  -- which `⟨μ, ξ₁⟩` is conserved.
  have hX := hμ.isHamiltonianVectorField circlePeriodOneGenerator
  rw [InfinitesimalAction.fundamental_apply] at hX
  have h := hX.apply_eq_of_isMIntegralCurve
    (isMIntegralCurve_mulInvariantExp_smul_smul (I' := I) circlePeriodOneGenerator x)
    (fun _ ↦ hμ.mdifferentiableAt _ _) 0 t
  simpa using h

end TauCeti.SmoothTwoForm.IsMomentMap

end
