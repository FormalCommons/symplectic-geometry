/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Principal.BasicForm
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Circle
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.ReducedForm
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.FinrankOne

/-!
# Reduction of a level of a circle moment map through a principal bundle

Let a circle act smoothly on a finite-dimensional manifold `M`, preserving a symplectic form `σ`,
with moment map `μ`, and let `H = ⟨μ, circlePeriodOneGenerator⟩`. Let `P` be a smooth principal
circle bundle over a boundaryless base `B`, with the right action of the circle on its total
space. A smooth map `φ` from the total space to `M` that is equivariant, takes values in a level
`H = t`, has injective differential and has tangent images `ker dH` is level data for Tau Ceti's
reduction of a level of a group-level moment map
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq_mpullback`,
with `K = Circleᵐᵒᵖ` acting through `MulOpposite.unop`): a circle moment map is
coadjoint-equivariant
(`TauCeti.SmoothTwoForm.IsMomentMap.isEquivariantMomentMap_circle`); `μ` is constant on the image
of `φ` and `ker dμ = ker dH` (`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_circle`), since
the Lie algebra of `Circle` is one-dimensional; the vertical vectors of `P` are the multiples of
its fundamental field, which `dφ` sends to the orbit directions of `M`
(`TauCeti.mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul`); and the fibres of `P` are
orbits. So `φ^* σ` is the pull-back of a unique symplectic form on the base.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_projContMDiffMap_eq`:
  for `σ` symplectic, an equivariant map `φ` from the total space of `P` into a level of `H`, with
  injective differential and tangent images `ker dH`, has `φ^* σ = π^* τ` for a unique symplectic
  `τ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 5.1.9.
-/

public section

open Bundle Function Manifold MulOpposite TauCeti SymplecticGeometry
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MulAction Circle M] [ContMDiffSMul (𝓡 1) I ∞ Circle M]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {P : B → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle Circle P] [∀ b, MulAction Circleᵐᵒᵖ (P b)]
  [PrincipalBundle Circle P] [ContMDiffFiberBundle ∞ Circle P IB (𝓡 1)]

/-- **The pull-back of a symplectic form to a level descends to the base.** Let a circle act
smoothly on a finite-dimensional manifold `M`, preserving the symplectic form `σ`, with moment
map `μ`, and let `H = ⟨μ, circlePeriodOneGenerator⟩`. Let `P` be a smooth principal circle
bundle over a boundaryless base `B`, and `φ` a smooth map from its total space to `M` with
`φ (p • z) = z • φ p`, taking values in the level `H = t`, with injective differential whose
range is `ker dH`. Then there is a unique symplectic form `τ` on `B` whose pull-back along the
projection is `φ^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_projContMDiffMap_eq {σ : SmoothTwoForm I M}
    {μ : M → Module.Dual ℝ (GroupLieAlgebra (𝓡 1) Circle)}
    (hμ : σ.IsMomentMap (InfinitesimalAction.fundamental (𝓡 1) Circle I M) μ)
    (hσ : σ.IsSymplectic)
    (hσs : ∀ g : Circle, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (I' := I) g) σ = σ)
    {φ : ManifoldTotalSpace Circle P → M} (hφ : ContMDiff (IB.prod (𝓡 1)) I ∞ φ)
    (hφs : ∀ (g : Circle) p, φ (op g • p) = g • φ p) {t : ℝ}
    (ht : ∀ p, μ (φ p) circlePeriodOneGenerator = t)
    (hinj : ∀ p, Injective (mfderiv (IB.prod (𝓡 1)) I φ p))
    (hrange : ∀ p, LinearMap.range (mfderiv (IB.prod (𝓡 1)) I φ p).toLinearMap =
      LinearMap.ker (mfderiv I 𝓘(ℝ) (fun x ↦ μ x circlePeriodOneGenerator) (φ p)).toLinearMap) :
    ∃! τ : SmoothTwoForm IB B, τ.IsSymplectic ∧
      SmoothForm.mpullback (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1))
        (ManifoldTotalSpace.projContMDiffMap ∞ Circle P IB (𝓡 1)).contMDiff τ =
      SmoothForm.mpullback φ hφ σ := by
  -- `μ` is constant on the image of `φ`, since the Lie algebra is spanned by
  -- `circlePeriodOneGenerator`.
  obtain ⟨c, hc⟩ : ∃ c, ∀ p, μ (φ p) = c := by
    rcases isEmpty_or_nonempty (ManifoldTotalSpace Circle P) with hZ | ⟨⟨p₀⟩⟩
    · exact ⟨0, fun p ↦ isEmptyElim p⟩
    · exact ⟨μ (φ p₀), fun p ↦ LinearMap.ext_of_finrank_eq_one finrank_groupLieAlgebra_circle
        circlePeriodOneGenerator_ne_zero ((ht p).trans (ht p₀).symm)⟩
  -- `dφ` sends the fundamental fields of the bundle to those of `M`.
  have hX (p : ManifoldTotalSpace Circle P) :
      (mfderiv (IB.prod (𝓡 1)) I φ p).toLinearMap ∘ₗ
          PrincipalBundle.rightFundamentalLinearMap IB (𝓡 1) p =
        (InfinitesimalAction.fundamental (𝓡 1) Circle I M).eval (φ p) :=
    LinearMap.ext fun ξ ↦ by
      rw [LinearMap.comp_apply, PrincipalBundle.rightFundamentalLinearMap_apply,
        ContinuousLinearMap.coe_coe, InfinitesimalAction.eval_apply,
        InfinitesimalAction.fundamental_apply]
      exact mfderiv_rightFundamentalVectorField_of_map_op_smul_eq_smul
        ((hφ p).mdifferentiableAt (by simp))
        (PrincipalBundle.mdifferentiableAt_orbit (n := ∞) (by simp) p 1) (hφs · p) ξ
  have hann : lieAnnihilator ℝ (GroupLieAlgebra (𝓡 1) Circle) c = ⊤ := by
    simp
  refine hμ.isEquivariantMomentMap_circle.existsUnique_isSymplectic_mpullback_eq_mpullback
    (K := Circleᵐᵒᵖ) hσ hσs hφ hc (fun p ↦ ?_)
    (ManifoldTotalSpace.isSubmersion_projContMDiffMap ∞ Circle P IB (𝓡 1))
    (ManifoldTotalSpace.surjective_projContMDiffMap ∞ Circle P IB (𝓡 1)) (fun p ↦ ?_)
    (fun k ↦ contMDiff_const_smul k) (fun k p ↦ ?_) (fun p p' hpp' ↦ ?_) unop fun k p ↦ ?_
  · -- The level tangent space of `μ` is `ker dH`.
    rw [hμ.ker_differential_circle]
    exact hrange p
  · -- The vertical vectors are the fundamental fields, which `dφ` sends to the orbit
    -- directions; `dφ` is injective.
    rw [hann, LieSubalgebra.top_toSubmodule, Submodule.map_top, ← hX, LinearMap.range_comp,
      Submodule.comap_map_eq_of_injective (hinj p),
      PrincipalBundle.range_rightFundamentalLinearMap_eq_ker_mfderiv_proj,
      ManifoldTotalSpace.coe_projContMDiffMap]
  · simp
  · obtain ⟨g, hg⟩ := PrincipalBundle.exists_op_smul_eq_of_proj_eq hpp'.symm
    exact ⟨op g, hg⟩
  · simpa using hφs k.unop p

end TauCeti.SmoothTwoForm.IsMomentMap

end
