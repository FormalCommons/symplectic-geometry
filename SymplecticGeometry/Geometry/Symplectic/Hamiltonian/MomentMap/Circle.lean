/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Critical
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.FinrankOne

/-!
# Critical points of a circle moment map

Let a circle act smoothly on a manifold `M`, with moment map `μ` for a two-form `σ`, and let
`H = ⟨μ, ξ₁⟩` be its component along the period-one generator `ξ₁ = circlePeriodOneGenerator`.
If `M` is Hausdorff and boundaryless, then where `σ` is nondegenerate, `x` is a critical point of
`H` exactly when the whole circle fixes `x`: by Tau Ceti's
`TauCeti.SmoothTwoForm.IsMomentMap.mem_criticalPoints_iff`, `dH_x = 0` exactly when the
fundamental vector field of `ξ₁` vanishes at `x`, and by
`SymplecticGeometry.mem_fixedPoints_circle_iff_fundamentalVectorField_eq_zero` this happens
exactly at the fixed points of the action.

So a point that the circle does not fix has `dH ≠ 0` where `σ` is nondegenerate, and for `σ`
nondegenerate a level of `H` without fixed points is a regular value of `H`. For a moment map
`-μ`, the sign convention of the converse of minimal coupling, the same holds for `H`, since `-H`
has the critical points of `H` (`TauCeti.criticalPoints_neg`).

Since the Lie algebra of `Circle` is spanned by `ξ₁`, the kernel of the differential of a moment
map `μ` is that of `dH`. A moment map `μ` is invariant under the action, and since the coadjoint
action of the abelian group `Circle` is trivial (`TauCeti.Lie.coadjointRepresentation_eq_one`),
it is a group-level moment map in Tau Ceti's sense. The kernel identity and this equivariance are
what Tau Ceti's equivariant reduction of a level
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`)
needs in the circle case; that theorem derives the vanishing of the cocycle itself.

Separately, for the same reason the cocycle of any map `μ` to the dual of the Lie algebra of
`Circle` vanishes. This is one hypothesis of the non-equivariant reduction
`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`.

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
* `TauCeti.SmoothTwoForm.IsMomentMap.mfderiv_ne_zero_of_notMem_fixedPoints`: `dH` does not vanish
  at a point that the circle does not fix and at which `σ` is nondegenerate.
* `TauCeti.SmoothTwoForm.IsMomentMap.isRegularValue_of_notMem_fixedPoints`: for `σ`
  nondegenerate, a level of `H` that contains no fixed point is a regular value of `H`.
* `TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_circle`: a circle moment map is a
  coadjoint-equivariant moment map.

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
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one finrank_groupLieAlgebra_circle
    circlePeriodOneGenerator_ne_zero Z
  obtain ⟨d, rfl⟩ := exists_smul_eq_of_finrank_eq_one finrank_groupLieAlgebra_circle
    circlePeriodOneGenerator_ne_zero Z'
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
    refine LinearMap.ext_of_finrank_eq_one finrank_groupLieAlgebra_circle
      circlePeriodOneGenerator_ne_zero ?_
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
  refine LinearMap.ext_of_finrank_eq_one finrank_groupLieAlgebra_circle
    circlePeriodOneGenerator_ne_zero ?_
  obtain ⟨t, rfl⟩ := mulInvariantExp_smul_circlePeriodOneGenerator_surjective g
  -- `t ↦ exp(t ξ₁) • x` is an integral curve of the Hamiltonian vector field of `⟨μ, ξ₁⟩`, along
  -- which `⟨μ, ξ₁⟩` is conserved.
  have hX := hμ.isHamiltonianVectorField circlePeriodOneGenerator
  rw [InfinitesimalAction.fundamental_apply] at hX
  have h := hX.apply_eq_of_isMIntegralCurve
    (isMIntegralCurve_mulInvariantExp_smul_smul (I' := I) circlePeriodOneGenerator x)
    (fun _ ↦ hμ.mdifferentiableAt _ _) 0 t
  simpa using h

/-! ### Points off the fixed set are regular for the Hamiltonian -/

/-- **A point off the fixed set is not critical for the Hamiltonian.** For a smooth circle action
on a Hausdorff boundaryless manifold with moment map `μ` for `σ`, if `σ` is nondegenerate at `x`
and some element of the circle moves `x`, then the differential of
`H = ⟨μ, circlePeriodOneGenerator⟩` does not vanish at `x`. -/
theorem mfderiv_ne_zero_of_notMem_fixedPoints [T2Space M] [BoundarylessManifold I M]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ)
    {x : M} (hσ : (σ.bilinFormAt x).Nondegenerate) (hx : x ∉ MulAction.fixedPoints Circle M) :
    mfderiv I 𝓘(ℝ) (fun y ↦ μ y circlePeriodOneGenerator) x ≠ 0 := by
  rwa [← hμ.mem_criticalPoints_circlePeriodOneGenerator_iff hσ,
    mem_criticalPoints_iff_mfderiv_eq_zero] at hx

/-- **A level without fixed points is a regular value of the Hamiltonian.** For a smooth circle
action on a Hausdorff boundaryless manifold with moment map `μ` for a nondegenerate two-form `σ`,
if no point of the level `H = c` of `H = ⟨μ, circlePeriodOneGenerator⟩` is fixed by the whole
circle, then `c` is a regular value of `H`. -/
theorem isRegularValue_of_notMem_fixedPoints [T2Space M] [BoundarylessManifold I M]
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ)
    (hσ : σ.IsNondegenerate) {c : ℝ}
    (hfix : ∀ x, μ x circlePeriodOneGenerator = c → x ∉ MulAction.fixedPoints Circle M) :
    IsRegularValue I 𝓘(ℝ) (fun y ↦ μ y circlePeriodOneGenerator) c := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  rw [isRegularPoint_iff_notMem_criticalPoints, mem_criticalPoints_iff_mfderiv_eq_zero]
  exact hμ.mfderiv_ne_zero_of_notMem_fixedPoints (hσ.nondegenerate_bilinFormAt x) (hfix x hx)

/-! ### Circle moment maps are coadjoint-equivariant -/

/-- **A circle moment map is coadjoint-equivariant.** A moment map `μ` of a smooth circle action
is a group-level moment map: the coadjoint action of the abelian group `Circle` is trivial, and
`μ` is invariant under the action. -/
theorem isEquivariantMomentMap_circle
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ) :
    σ.IsEquivariantMomentMap μ where
  toIsMomentMap := hμ
  apply_smul g x := by
    rw [Lie.coadjointRepresentation_eq_one, one_apply_eq_self, hμ.apply_smul_circle]

end TauCeti.SmoothTwoForm.IsMomentMap

end
