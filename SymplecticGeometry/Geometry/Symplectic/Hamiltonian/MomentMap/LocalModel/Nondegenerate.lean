/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent

import SymplecticGeometry.Geometry.Symplectic.Manifold.Opens
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.Nondegenerate

/-!
# The local model's descended form is symplectic near the zero section

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `Y = G ×_K (A × V)`, and `ω` the descent of `D.form` to `Y`, Tau Ceti's
`TauCeti.CotangentBundle.balancedProductInducedForm` (`LocalModel/Descent.lean`). This file shows
that `ω` is a symplectic form on a `G`-invariant open neighbourhood of the zero
section `{[g, 0] | g ∈ G}`.

* Along the zero section, `ω` is nondegenerate by Tau Ceti's criterion in
  Marle–Guillemin–Sternberg coordinates,
  `TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod`.
  Its hypotheses at `0 ∈ A × V` hold for the local model: the covector there is `τ`, its
  derivative is `(a, b) ↦ ι𝔪 a`, read through `A ≃ 𝔪*` and the projection `𝔤 → 𝔪` along
  `𝔥 ⊕ 𝔮`, the form on `A × V` is `σ` on the second factor, that projection maps `𝔤_τ` onto `𝔪`
  with kernel meeting `𝔤_τ` in `𝔥`, and `K` fixes `0`.
* The set where `ω` is nondegenerate is open
  (`TauCeti.SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt`) and `G`-invariant
  (`TauCeti.CotangentBundle.nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff`), and
  `ω` restricts to a symplectic form on it
  (`TauCeti.SmoothForm.IsClosed.isSymplectic_mpullback_subtypeVal`).

The last step follows the proof of Tau Ceti's
`TauCeti.CotangentBundle.exists_opens_isNondegenerate_mpullback_coisotropicModelForm`.

## Main results

* `LocalModelData.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_zero`:
  `ω` is nondegenerate at every point `[g, 0]` of the zero section.
* `LocalModelData.exists_opens_isSymplectic_mpullback_balancedProductInducedForm`:
  `ω` restricts to a symplectic form on a `G`-invariant open set containing the zero section.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.Lie TauCeti.Manifold TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The descended form is nondegenerate along the zero section**: at every point `[g, 0, 0]`. -/
theorem nondegenerate_bilinFormAt_balancedProductInducedForm_mk_zero (g : G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ((balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
        D.mpullback_smul_mpullback_snd_constSmooth
        D.isMomentMap_mpullback_snd_constSmooth).bilinFormAt
      (BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V)))).Nondegenerate := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  set π := Submodule.projectionOnto _ _ D.isCompl_𝔪_sup
  refine nondegenerate_bilinFormAt_balancedProductInducedForm_mk_of_dual_prod
    (n := ((0 : A), (0 : V))) (ν := D.τ) (π := π) (β := D.σ.toBilinForm)
    (by rw [toLinearMap_covectorCLM, Prod.mk_zero_zero, covector_zero])
    (D.equivDual𝔪.prodCongr (LinearEquiv.refl ℝ V)) (fun u ζ ↦ ?_) (fun u w ↦ ?_)
    D.σ.nondegenerate.1 D.map_projectionOnto_lieAnnihilator_eq_top (fun ζ hζ hπζ ↦ ?_)
    (fundamentalVectorField_eq_zero_of_forall_smul_eq fun k ↦ smul_zero k) g
  · -- The derivative of the covector at `0` is `(a, b) ↦ ι𝔪 a`.
    have hc : DifferentiableAt ℝ D.covectorCLM ((0 : A), (0 : V)) :=
      (D.contMDiff_covectorCLM.contDiff.differentiable (by simp)) _
    rw [mvfderiv_eq_fderiv_apply]
    refine (fderiv_clm_apply_const_apply hc ζ u).symm.trans ?_
    obtain ⟨a, b⟩ := u
    simp only [covectorCLM_apply, covector_def]
    refine (fderiv_localModelCovector_apply D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 ζ 0 a 0 b).trans ?_
    rw [map_zero, LinearMap.zero_apply, map_zero, add_zero, ι𝔪_apply]
    -- `LinearEquiv.prodCongr_apply` does not rewrite here, since `e` is read on the tangent space,
    -- whose module structure is that of `A × V` only up to unfolding.
    rfl
  · exact D.σ.eval₂_mpullback_snd_constSmooth _ u.1 w.1 u.2 w.2
  · rw [D.range_groupLieAlgebraMap_subtype, ← D.lieAnnihilator_inf_ker_projectionOnto]
    exact ⟨hζ, hπζ⟩

/-- **The descended form is symplectic near the zero section.** There is an open set `U` of
`G ×_K (A × V)` that contains every point `[g, 0, 0]` of the zero section and is invariant under
the action of `G`, on which the descended form of the local model restricts to a symplectic
form. -/
theorem exists_opens_isSymplectic_mpullback_balancedProductInducedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∃ U : TopologicalSpace.Opens (BalancedProduct K K.RightTranslation (A × V)),
      (∀ g : G, BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V)) ∈ U) ∧
      (∀ (k : G) (y), y ∈ U → k • y ∈ U) ∧
      SmoothTwoForm.IsSymplectic
        (SmoothForm.mpullback (Subtype.val : U → _) contMDiff_subtypeVal
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  -- `U` is the set of points at which the descended form is nondegenerate.
  exact ⟨⟨_, SmoothTwoForm.isOpen_setOf_nondegenerate_bilinFormAt
      (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
        D.mpullback_smul_mpullback_snd_constSmooth
        D.isMomentMap_mpullback_snd_constSmooth)⟩,
    D.nondegenerate_bilinFormAt_balancedProductInducedForm_mk_zero,
    fun k y hy ↦ (nondegenerate_bilinFormAt_balancedProductInducedForm_smul_iff k y).2 hy,
    (isClosed_balancedProductInducedForm ((SymplecticForm.isClosed_constSmooth D.σ).mpullback _ _)
      ).isSymplectic_mpullback_subtypeVal fun _ hy ↦ hy⟩

end LocalModelData

end SymplecticGeometry

end
