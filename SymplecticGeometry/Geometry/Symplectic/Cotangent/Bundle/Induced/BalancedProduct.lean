/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct

import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct

/-!
# The induced form on `G ×_K N`, read on `G × N`

Let `G` be a real Lie group, `K` a closed subgroup acting on a manifold `N` with a two-form `σ`,
and `f : N → 𝔤*` a `K`-equivariant map whose restriction to the Lie algebra of `K` is a moment
map. Tau Ceti's `TauCeti.CotangentBundle.balancedProductInducedForm` is the descent of the induced
form `-d⟨f, θ⟩ + pr_N^* σ` to the balanced product `G ×_K N`, and Tau Ceti states its pullback
along the quotient map from `K.RightTranslation × N`. This file states it along the projection
`(g, n) ↦ [g, n]` from `G × N` itself, and the equivariance of Tau Ceti's moment map
`TauCeti.CotangentBundle.balancedProductInducedMomentMap`, which needs no smooth structure.

## Main results

* `TauCeti.CotangentBundle.balancedProductInducedMomentMap_smul`: the moment map
  `[g, n] ↦ Ad*_g (f n)` is equivariant for `k • [g, n] = [k g, n]` and the coadjoint action, for
  any action of `K` on a set `N`. Its proof is the equivariance step of the proof of Tau Ceti's
  `TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductInducedForm`, stated apart.
* `TauCeti.CotangentBundle.mpullback_mk_balancedProductInducedForm`: the induced form on
  `G ×_K N` pulls back to `TauCeti.CotangentBundle.inducedForm` along `G × N → G ×_K N`.
* `TauCeti.CotangentBundle.eval₂_balancedProductInducedForm_mfderiv_mk`: its values on images of
  tangent vectors of `G × N` are those of the induced form.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
-/

public section

open TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.CotangentBundle

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] {K : Subgroup G}

/-- **Equivariance of the moment map of `G ×_K N`.** For the action `k • [g, n] = [k g, n]` of `G`
on `G ×_K N` and the coadjoint action, `μ (k • y) = Ad*_k (μ y)` for the map
`μ [g, n] = Ad*_g (f n)`. Unlike
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.apply_smul`, this needs no smooth structure on `N`. -/
theorem balancedProductInducedMomentMap_smul {N : Type*} [MulAction K N] {f : N → E →L[ℝ] ℝ}
    (hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹)
    (k : G) (y : BalancedProduct K K.RightTranslation N) :
    balancedProductInducedMomentMap G hfK (k • y) =
      Lie.coadjointRepresentation ℝ I G k (balancedProductInducedMomentMap G hfK y) := by
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g n =>
    rw [BalancedProduct.smul_mk_toRightTranslation, balancedProductInducedMomentMap_mk,
      balancedProductInducedMomentMap_mk, map_mul]
    exact mul_apply_eq_comp _ _ _

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsClosed (K : Set G)]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [MulAction K N] [ContMDiffSMul 𝓘(ℝ, F) IN ∞ K N]
  {σ : SmoothTwoForm IN N} {f : N → E →L[ℝ] ℝ} {hf : ContMDiff IN 𝓘(ℝ, E →L[ℝ] ℝ) ∞ f}
  {hfK : ∀ (k : K) (n : N), f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (k : G)⁻¹}
  {hσK : ∀ k : K, SmoothForm.mpullback (fun n : N ↦ k • n)
    (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k) σ = σ}
  {hμ : σ.IsMomentMap (InfinitesimalAction.fundamental 𝓘(ℝ, F) K IN N)
    fun n ↦ (f n : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap}

/-- **The induced form on `G ×_K N` pulls back to the induced form on `G × N`** along the
projection `(g, n) ↦ [g, n]`: its pullback is `-d⟨f, θ⟩ + pr_N^* σ`. -/
@[simp]
theorem mpullback_mk_balancedProductInducedForm :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    ∀ hπ : ContMDiff (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN)) ∞
      (fun p : G × N ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2),
    SmoothForm.mpullback _ hπ (balancedProductInducedForm I G σ hf hfK hσK hμ) =
      inducedForm I G σ hf := by
  let := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  intro _
  have hq := (BalancedProduct.isSubmersion_quotientMk_rightTranslation (K := K) (Z := N)
    (I := I) (IZ := IN) (F := F)).contMDiff
  have hT : ContMDiff (I.prod IN) (I.prod IN) ∞ (Prod.map K.toRightTranslation (id : N → N)) :=
    (Subgroup.RightTranslation.contMDiff_toRightTranslation ∞).prodMap contMDiff_id
  -- The projection from `G × N` is Tau Ceti's quotient map after `K.toRightTranslation`.
  refine (SmoothForm.mpullback_mpullback _ _ hT hq _).symm.trans ?_
  rw [mpullback_quotientMk_balancedProductInducedForm,
    SmoothForm.mpullback_mpullback_of_comp_eq hT
      ((Subgroup.RightTranslation.contMDiff_toRightTranslation_symm ∞).prodMap contMDiff_id)
      contMDiff_id contMDiff_id (funext fun p ↦ Prod.ext (Equiv.symm_apply_apply _ _) rfl),
    SmoothForm.mpullback_id, LinearMap.id_apply, LinearMap.id_apply]

/-- **The induced form on `G ×_K N` on images of tangent vectors of `G × N`.** For the projection
`π : G × N → G ×_K N`, `(g, n) ↦ [g, n]`, it takes the values of the induced form on `G × N`:
`ω_(π x)(dπ u, dπ w) = (-d⟨f, θ⟩ + pr_N^* σ)_x(u, w)`. -/
theorem eval₂_balancedProductInducedForm_mfderiv_mk (x : G × N)
    (u w : TangentSpace (I.prod IN) x) :
    letI := BalancedProduct.rightTranslationChartedSpace K N I IN F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
      (F := F)
    SmoothBundleForm.eval₂ (balancedProductInducedForm I G σ hf hfK hσK hμ)
        (BalancedProduct.mk K (K.toRightTranslation x.1) x.2)
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (fun p : G × N ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) x u)
        (mfderiv (I.prod IN) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × EN))
          (fun p : G × N ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) x w) =
      SmoothBundleForm.eval₂ (inducedForm I G σ hf) x u w := by
  let := BalancedProduct.rightTranslationChartedSpace K N I IN F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := N) (I := I) (IZ := IN)
    (F := F)
  have hπ := (BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := N) (I := I)
    (IZ := IN) (F := F)).contMDiff
  rw [← SmoothForm.eval₂_mpullback _ hπ, mpullback_mk_balancedProductInducedForm hπ]

end TauCeti.CotangentBundle

end
