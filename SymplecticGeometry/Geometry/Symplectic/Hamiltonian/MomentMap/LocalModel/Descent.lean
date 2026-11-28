/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Action
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct

import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Induced.BalancedProduct
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# The descent of the local model's form to `G ×_K (A × V)`

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (A × V)`, with `A ≃ 𝔪*`. The two-form `D.form` on `G × (A × V)` is Tau Ceti's
induced form `-d⟨ν, θ⟩ + pr_V^* σ` of the covectors `ν = D.covector`
(`SymplecticGeometry.LocalModelData.form_eq_inducedForm`), and Tau Ceti's
`TauCeti.CotangentBundle.balancedProductInducedForm` descends it to the balanced product, given
three hypotheses: `ν` is `K`-equivariant
(`SymplecticGeometry.LocalModelData.covectorCLM_smul`), `pr_V^* σ` is
`K`-invariant (`SymplecticGeometry.LocalModelData.mpullback_smul_mpullback_snd_constSmooth`), and
the restriction of `ν` to the Lie algebra of `K` is a moment map of the action of `K` on
`(A × V, pr_V^* σ)`. This file proves the last one, and states the facts about the descended form
that are specific to the local model. Its pullback along `(g, p) ↦ [g, p]` from `G × (A × V)`
is `D.form`: this is the case of the local model of
`TauCeti.CotangentBundle.mpullback_mk_balancedProductInducedForm`, in
`SymplecticGeometry/Geometry/Symplectic/Cotangent/Bundle/Induced/BalancedProduct.lean`, read
through `SymplecticGeometry.LocalModelData.form_eq_inducedForm`.

The moment map property is the moment identity of the slice: for `ξ` in the Lie algebra of `K`,
with image `ξ' ∈ 𝔥`, the fundamental vector field at `(η, v)` is `(a, ρ ξ' v)`, and
`pr_V^* σ ((a, ρ ξ' v), (a₂, b₂)) = σ (ρ ξ' v, b₂)` is the derivative of `p ↦ ν p ξ'` along
`(a₂, b₂)`, since `ι𝔪` vanishes on `𝔥` and `ι𝔥 (dμ_V(v) b₂) ξ' = σ (ρ ξ' v, b₂)`.

## Main results

* `SymplecticGeometry.LocalModelData.isMomentMap_mpullback_snd_constSmooth`: the restriction of
  the covectors to the Lie algebra of `K` is a moment map of the action of `K` on `A × V`.
* `SymplecticGeometry.LocalModelData.mem_ker_mfderiv_mk_one_zero_iff`: at `(1, 0, 0)`, the
  vertical directions are the vectors `(ξ, 0, 0)` with `ξ ∈ 𝔥`.
* `SymplecticGeometry.LocalModelData.mpullback_mk_balancedProductInducedForm`,
  `SymplecticGeometry.LocalModelData.eval₂_balancedProductInducedForm_mfderiv_mk`: the descended
  form pulls back to `D.form` along `G × (A × V) → G ×_K (A × V)`, and its values on images of
  tangent vectors of `G × (A × V)`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.CotangentBundle TauCeti.Lie TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The moment map of `K` on the fibre `A × V`.** For the action of `K` on `A × V` and the
pullback `pr_V^* σ` of the symplectic form of `V`, the map `p ↦ ν p ∘ ι`, the restriction of the
covectors `ν` of the local model to the Lie algebra of `K` along the differential `ι` of the
inclusion `K → G`, is a moment map. This is the hypothesis `hμ` of
`TauCeti.CotangentBundle.balancedProductInducedForm`. -/
theorem isMomentMap_mpullback_snd_constSmooth :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    SmoothTwoForm.IsMomentMap
      (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff D.σ.constSmooth :
        SmoothTwoForm 𝓘(ℝ, A × V) (A × V))
      (InfinitesimalAction.fundamental 𝓘(ℝ, F) K 𝓘(ℝ, A × V) (A × V))
      fun p ↦
        (D.covectorCLM p : E →ₗ[ℝ] ℝ) ∘ₗ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  -- The component of `p ↦ ν p ∘ ι` at `ξ` is `p ↦ ν p (ι ξ)`.
  have hfun (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) :
      (fun p ↦ ((D.covectorCLM p : E →ₗ[ℝ] ℝ) ∘ₗ
        (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap) ξ) =
        fun p ↦ D.covector p (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) :=
    -- The composite applied to `ξ` is `D.covectorCLM p (ι ξ)` by definition of the composition.
    funext fun p ↦ D.covectorCLM_apply p _
  refine ⟨fun ξ ↦ (hfun ξ).symm ▸ D.contMDiff_covector_apply _,
    fun ξ ↦ SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x w ↦ ?_⟩
  obtain ⟨η, v⟩ := x
  rw [hfun, InfinitesimalAction.fundamental_apply, mvfderiv_eq_fderiv_apply]
  obtain ⟨a₂, b₂⟩ := w
  set ξ' := K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ
  have hξ' : ξ' ∈ D.𝔥 := D.groupLieAlgebraMap_subtype_mem_𝔥 ξ
  set X : A × V := fundamentalVectorField 𝓘(ℝ, A × V) ξ (η, v) with hX
  have hb : X.2 = (D.ρ ⟨ξ', hξ'⟩ : Module.End ℝ V) v := by
    rw [hX, fundamentalVectorField_apply, mfderiv_fiberDistribMulAction_smul_apply]
  rw [← Prod.mk.eta (p := X), SymplecticForm.eval₂_mpullback_snd_constSmooth, hb]
  simp only [covector_def]
  rw [fderiv_localModelCovector_apply, LinearMap.add_apply,
    D.ι𝔪_apply_of_mem_sup a₂ (Submodule.mem_sup_left hξ'), zero_add]
  exact ((D.ι𝔥_apply_coe _ ⟨ξ', hξ'⟩).trans
    (SymplecticForm.linearMomentMapCompPolar_apply _ _ _ _ _)).symm

/-- **The vertical space at `(1, 0, 0)`.** A tangent vector at `(1, 0, 0)` lies in the kernel of
the differential of the projection `(g, p) ↦ [g, p]` onto `G ×_K (A × V)` exactly when it is
`(ξ, 0, 0)` for some `ξ ∈ 𝔥`: at `p = 0` the infinitesimal action of `K` on `A × V` vanishes, and
the images in `𝔤` of the Lie algebra of `K` fill `𝔥`. -/
theorem mem_ker_mfderiv_mk_one_zero_iff [I.Boundaryless]
    (u : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    u ∈ (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
      ((1 : G), ((0 : A), (0 : V)))).ker ↔
      tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u ∈ D.𝔥.prod ⊥ := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  -- `K` fixes `0 ∈ A × V`, and the image of its Lie algebra in `𝔤` is `𝔥`.
  rw [BalancedProduct.ker_mfderiv_mk_toRightTranslation_one_of_forall_smul_eq F
    (fun k ↦ smul_zero k), D.range_groupLieAlgebraMap_subtype, tangentSpaceProdEquiv_apply]
  -- The two memberships differ only in reading `u` as a vector of `TangentSpace` or of
  -- `E × (A × V)`, which agree by definition.
  exact Iff.rfl


/-! ### The descended form, read on `G × (A × V)` -/

section Descended

variable [I.Boundaryless]

/-- The descended form of the local model, Tau Ceti's
`TauCeti.CotangentBundle.balancedProductInducedForm`, pulls back to `D.form` along the projection
`(g, p) ↦ [g, p]` from `G × (A × V)` onto `G ×_K (A × V)`. -/
theorem mpullback_mk_balancedProductInducedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ hπ : ContMDiff (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2),
    SmoothForm.mpullback _ hπ
        (balancedProductInducedForm I G _ D.contMDiff_covectorCLM
          D.covectorCLM_smul D.mpullback_smul_mpullback_snd_constSmooth
          D.isMomentMap_mpullback_snd_constSmooth) =
      D.form := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  intro hπ
  rw [TauCeti.CotangentBundle.mpullback_mk_balancedProductInducedForm hπ, form_eq_inducedForm]

/-- **The descended form of the local model on images of tangent vectors.** On the images under
the differential of the projection `π : G × (A × V) → G ×_K (A × V)`, Tau Ceti's
`TauCeti.CotangentBundle.balancedProductInducedForm` takes the values of `D.form`:
`ω_(π x)(dπ u, dπ w) = D.form_x(u, w)`. -/
theorem eval₂_balancedProductInducedForm_mfderiv_mk (x : G × (A × V))
    (u w : TangentSpace (I.prod 𝓘(ℝ, A × V)) x) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    SmoothBundleForm.eval₂
        (balancedProductInducedForm I G _ D.contMDiff_covectorCLM
          D.covectorCLM_smul D.mpullback_smul_mpullback_snd_constSmooth
          D.isMomentMap_mpullback_snd_constSmooth)
        (BalancedProduct.mk K (K.toRightTranslation x.1) x.2)
        (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) x u)
        (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) x w) =
      SmoothBundleForm.eval₂ D.form x u w := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  exact (TauCeti.CotangentBundle.eval₂_balancedProductInducedForm_mfderiv_mk x u w).trans
    (by rw [form_eq_inducedForm])

end Descended

end LocalModelData

end SymplecticGeometry

end
