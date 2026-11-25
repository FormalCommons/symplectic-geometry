/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct

/-!
# The vertical directions of the projection `G × Z → G ×_K Z`

Let `G` be a finite-dimensional real Lie group, `K` a closed subgroup with a Lie group structure
for which it acts smoothly on `G` by left multiplication, and `Z` a manifold on which `K` acts
smoothly. Tau Ceti's `TauCeti.Geometry.Lie.Subgroup.BalancedProduct` makes the balanced product
`G ×_K Z`, the quotient of `G × Z` by `h • (g, z) = (g h⁻¹, h • z)`, a smooth manifold
(`TauCeti.BalancedProduct.rightTranslationChartedSpace`) for which the projection
`π : (g, z) ↦ [g, z]` is a submersion. This file describes the kernel of `dπ`.

The action of `K` on `G` by `h • g = g h⁻¹` has the fundamental vector field
`ξ_G(g) = -d(L_g)(ξ')`, where `ξ'` is the image of `ξ ∈ Lie(K)` in `Lie(G)`: the orbit map of `g`
is `h ↦ g h⁻¹`, and inversion has differential `-1` at the identity
(`Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation`). The kernel of `dπ` at a
point is the tangent space of its `K`-orbit, spanned by the fundamental vector fields of the
diagonal action; this is Tau Ceti's
`ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt`, applied as in the
proof of Tau Ceti's `ProperSMul.ker_mfderiv_quotientMk`. So the kernel of `dπ` at `(g, z)`
consists of the vectors `(-d(L_g)(ξ'), ξ_Z(z))` for `ξ ∈ Lie(K)`.

## Main results

* `TauCeti.BalancedProduct.ker_mfderiv_quotientMk_rightTranslation`: on
  `K.RightTranslation × Z`, the kernel of `dπ` is the orbit tangent space of the diagonal action.
* `TauCeti.BalancedProduct.mem_ker_mfderiv_mk_toRightTranslation_iff`: on `G × Z`, a tangent
  vector at `(g, z)` is vertical exactly when it is `(-d(L_g)(ξ'), ξ_Z(z))` for some `ξ ∈ Lie(K)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 21 (the quotient manifold theorem) and Chapter 20 (infinitesimal
  generators of Lie group actions).
-/

public section

open Function Manifold TauCeti
open scoped ContDiff Manifold

namespace Subgroup.RightTranslation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {G : Type*} [Group G] {K : Subgroup G}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G] [ChartedSpace H G] [LieGroup I 1 G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK]
  {IK : ModelWithCorners 𝕜 EK HK} [ChartedSpace HK K] [ContMDiffSMul IK I 1 K G]

/-- **The fundamental vector fields of right translation.** For the action `h • g = g h⁻¹` of a
subgroup `K` on `G`, the fundamental vector field of `ξ ∈ Lie(K)` at `g` is `-d(L_g)(ξ')`, minus
the left-invariant vector field of the image `ξ'` of `ξ` in `Lie(G)`. -/
theorem fundamentalVectorField_toRightTranslation (ξ : GroupLieAlgebra IK K) (g : G) :
    fundamentalVectorField I ξ (K.toRightTranslation g) =
      -mulInvariantVectorField (K.subtype.groupLieAlgebraMap IK I ξ) g := by
  have hsub : MDifferentiableAt IK I K.subtype 1 := by
    have h := (ContMDiffSMul.contMDiff_smul_const (I := IK) (I' := I) (n := 1)
      (1 : G)).mdifferentiableAt (x := (1 : K)) one_ne_zero
    convert h using 1
    funext k
    simp [Subgroup.smul_def]
  have hinv : MDifferentiableAt I I (fun x : G ↦ x⁻¹) 1 :=
    (contMDiff_inv I 1).mdifferentiableAt one_ne_zero
  have hmul : MDifferentiableAt I I (fun x : G ↦ g * x) 1 :=
    (contMDiff_mul_left (I := I) (n := 1)).mdifferentiableAt one_ne_zero
  rw [fundamentalVectorField_apply]
  -- `K.RightTranslation` is `G` with the same charts, `K.toRightTranslation` is the identity, and
  -- `k • g = g k⁻¹`, so the orbit map of `g` is `k ↦ g k⁻¹`, a map into `G`.
  change mfderiv IK I ((fun x : G ↦ g * x) ∘ (fun x : G ↦ x⁻¹) ∘ K.subtype) 1 ξ = _
  rw [mfderiv_comp_apply_of_eq 1 hmul (hinv.comp_of_eq 1 hsub (by simp)) (by simp),
    mfderiv_comp_apply_of_eq 1 hinv hsub (by simp), ← MonoidHom.groupLieAlgebraMap_apply,
    GroupLieAlgebra.mfderiv_inv_one_apply, map_neg, GroupLieAlgebra.mulInvariantVectorField_apply]
  -- The two sides agree up to how the base point of their tangent space is written.
  rfl

end Subgroup.RightTranslation

namespace TauCeti.BalancedProduct

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]

/-- **The vertical directions of `K.RightTranslation × Z → G ×_K Z`.** The kernel of the
differential at `x` of the projection onto the balanced product is the orbit tangent space at `x`
of the diagonal action `h • (g, z) = (g h⁻¹, h • z)` of `K`, spanned by its fundamental vector
fields. -/
theorem ker_mfderiv_quotientMk_rightTranslation (x : K.RightTranslation × Z) :
    letI := rightTranslationChartedSpace K Z I IZ F
    (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (Quotient.mk (MulAction.orbitRel K (K.RightTranslation × Z))) x).ker =
      (InfinitesimalAction.fundamental 𝓘(ℝ, F) K (I.prod IZ)
        (K.RightTranslation × Z)).orbitTangent x := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  exact ProperSMul.ker_mfderiv_eq_orbitTangent_fundamental_of_isSubmersionAt (I := 𝓘(ℝ, F))
    (IsCancelSMul.stabilizer_eq_bot x)
    ((isSubmersion_quotientMk_rightTranslation (I := I) (IZ := IZ) (F := F)).isSubmersionAt x)
    (by simp)
    (Filter.Eventually.of_forall fun _ ↦ MulAction.orbitRel.Quotient.quotient_smul_eq)
    (Filter.Eventually.of_forall fun _ h ↦
      MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact h)))

/-- **The vertical directions of `G × Z → G ×_K Z`.** A tangent vector at `(g, z)` lies in the
kernel of the differential of `(g, z) ↦ [g, z]` exactly when it is `(-d(L_g)(ξ'), ξ_Z(z))` for
some `ξ` in the Lie algebra of `K`, where `ξ'` is the image of `ξ` in `Lie(G)` and `ξ_Z` is the
fundamental vector field of `ξ` on `Z`. -/
theorem mem_ker_mfderiv_mk_toRightTranslation_iff (g : G) (z : Z)
    (v : TangentSpace (I.prod IZ) (g, z)) :
    letI := rightTranslationChartedSpace K Z I IZ F
    v ∈ (mfderiv (I.prod IZ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EZ))
      (fun p : G × Z ↦ mk K (K.toRightTranslation p.1) p.2) (g, z)).ker ↔
      ∃ ξ : GroupLieAlgebra 𝓘(ℝ, F) K,
        v = (-mulInvariantVectorField (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) g,
          fundamentalVectorField IZ ξ z) := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  -- `K.RightTranslation` is `G` with the same charts and `K.toRightTranslation` is the identity,
  -- so the map is the projection of `K.RightTranslation × Z` onto the balanced product, and its
  -- kernel is the orbit tangent space at `(g, z)`.
  refine (SetLike.ext_iff.1
    (ker_mfderiv_quotientMk_rightTranslation (K.toRightTranslation g, z)) v).trans
    ((InfinitesimalAction.mem_orbitTangent_iff _ _).trans (exists_congr fun ξ ↦ ?_))
  have h : (Manifold.prodVectorField (fundamentalVectorField I ξ)
      (fundamentalVectorField IZ ξ) (K.toRightTranslation g, z) : E × EZ) =
      (-mulInvariantVectorField (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) g,
        fundamentalVectorField IZ ξ z) :=
    Prod.ext ((Manifold.prodVectorField_fst _ _ _).trans
      (Subgroup.RightTranslation.fundamentalVectorField_toRightTranslation ξ g))
      (Manifold.prodVectorField_snd _ _ _)
  rw [InfinitesimalAction.fundamental_prod, InfinitesimalAction.prod_apply,
    InfinitesimalAction.fundamental_apply, InfinitesimalAction.fundamental_apply]
  exact h ▸ eq_comm

end TauCeti.BalancedProduct

end
