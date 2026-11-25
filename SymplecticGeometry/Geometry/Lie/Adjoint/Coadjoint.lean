/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.Tangent.Differential

import TauCeti.Geometry.Manifold.Algebra.SMul

/-!
# The derivative of coadjoint coefficients along a homomorphism

Let `G` be a Lie group, and `φ : K →* G` a homomorphism, differentiable at `1`, from a group `K`
that is also a manifold. For `ν ∈ 𝔤*` and `ζ ∈ 𝔤`, the coefficient `k ↦ (Ad*_{φ k} ν) ζ` of the
coadjoint representation of `G` restricted along `φ` has derivative `ξ ↦ ν ⁅ζ, dφ ξ⁆` at `1`.
This is the chain rule along `φ` combined with Tau Ceti's
`TauCeti.Lie.mvfderiv_coadjointRepresentation_apply_one`, the case where `φ` is the identity.

## Main results

* `TauCeti.Lie.mvfderiv_coadjointRepresentation_comp_apply_one`: the derivative at `1` of
  `k ↦ (Ad*_{φ k} ν) ζ` in the direction `ξ` is `ν ⁅ζ, dφ ξ⁆`.
* `TauCeti.Lie.mvfderiv_coadjointRepresentation_subtype_apply_one`: its case for the inclusion
  of a subgroup `K` whose left multiplication on `G` is smooth.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HK : Type*} [TopologicalSpace HK] {J : ModelWithCorners ℝ F HK}
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

/-- The derivative at `1` of the coefficient `k ↦ (Ad*_{φ k} ν) ζ` of the coadjoint representation
of `G` along a homomorphism `φ : K →* G` that is differentiable at `1` is, in the direction `ξ`,
`ν ⁅ζ, dφ ξ⁆`. -/
theorem mvfderiv_coadjointRepresentation_comp_apply_one (φ : K →* G)
    (hφ : MDifferentiableAt J I φ 1) (ν : Module.Dual ℝ (GroupLieAlgebra I G))
    (ζ : GroupLieAlgebra I G) (ξ : GroupLieAlgebra J K) :
    mvfderiv J (fun k : K ↦ coadjointRepresentation ℝ I G (φ k) ν ζ) 1 ξ =
      ν ⁅ζ, φ.groupLieAlgebraMap J I ξ⁆ := by
  rw [show (fun k : K ↦ coadjointRepresentation ℝ I G (φ k) ν ζ) =
      (fun g : G ↦ coadjointRepresentation ℝ I G g ν ζ) ∘ φ from rfl,
    mvfderiv_comp_apply_of_eq 1
      ((contMDiff_coadjointRepresentation_apply _ _).mdifferentiableAt (by simp)) hφ (map_one φ),
    ← MonoidHom.groupLieAlgebraMap_apply, mvfderiv_coadjointRepresentation_apply_one]

/-- The derivative at `1` of the coefficient `k ↦ (Ad*_k ν) ζ` of the coadjoint representation of
`G`, restricted to a subgroup `K` whose left multiplication on `G` is smooth, is, in the direction
`ξ`, `ν ⁅ζ, ξ'⁆`, where `ξ'` is the image of `ξ` in `𝔤`. -/
theorem mvfderiv_coadjointRepresentation_subtype_apply_one {K : Subgroup G} [ChartedSpace HK K]
    [ContMDiffSMul J I ∞ K G] (ν : Module.Dual ℝ (GroupLieAlgebra I G)) (ζ : GroupLieAlgebra I G)
    (ξ : GroupLieAlgebra J K) :
    mvfderiv J (fun k : K ↦ coadjointRepresentation ℝ I G k ν ζ) 1 ξ =
      ν ⁅ζ, K.subtype.groupLieAlgebraMap J I ξ⁆ := by
  have hK : MDifferentiableAt J I K.subtype 1 := by
    rw [Subgroup.coe_subtype]
    exact (K.contMDiff_subtypeVal_of_contMDiffSMul (I := I) (n := ∞)).mdifferentiableAt (by simp)
  exact mvfderiv_coadjointRepresentation_comp_apply_one K.subtype hK ν ζ ξ

end TauCeti.Lie

end
