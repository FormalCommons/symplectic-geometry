/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Action
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion

import SymplecticGeometry.Geometry.Lie.Adjoint.Coadjoint
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.Algebra.SMul
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.Descent

/-!
# The descent of the local model's form to `G ×_K (A × V)`

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (A × V)`, with `A ≃ 𝔪*`. The two-form `D.form` on `G × (A × V)` descends to the
balanced product when it is invariant under the action of `K` and vanishes on the vertical
directions of the projection `G × (A × V) → G ×_K (A × V)` (Tau Ceti's
`TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le`). The first condition is
`SymplecticGeometry.LocalModelData.mpullback_prodMap_mul_right_smul_form`; this file proves the
second, and then descends the form.

By `TauCeti.BalancedProduct.mem_ker_mfderiv_mk_toRightTranslation_iff`, the vertical vectors at
`(g, p)` are `(-d(L_g) ξ', X)`, where `ξ` is in the Lie algebra of `K`, `ξ' ∈ 𝔥` is its image in
`𝔤`, and `X = (a, ρ ξ' v)` is the fundamental vector field of `ξ` at `p = (η, v)`. Such a
vector lies in the kernel of the form by Tau Ceti's
`TauCeti.CotangentBundle.eval₂_inducedForm_eq_zero`, applied with `-ξ'`, whose two conditions on
`X` hold here:

* the derivative of `ν` along `X` is the infinitesimal coadjoint action, `dν_p(X) ζ = ν p ⁅ζ, ξ'⁆`,
  which is `ν p ⁅-ξ', ζ⁆`. This is the derivative at `1` of the equivariance
  `ν (k • p) = Ad*_k (ν p)` (`SymplecticGeometry.LocalModelData.covector_smul`), computed with
  `TauCeti.Lie.mvfderiv_coadjointRepresentation_subtype_apply_one`;
* `ι𝔪` vanishes on `ξ' ∈ 𝔥`, and the moment identity `dμ_V(v) b₂ ξ' = σ (ρ ξ' v, b₂)` gives
  `pr_V^* σ (X, (a₂, b₂)) = d(ν · ξ')_p (a₂, b₂)`, with the value of `pr_V^* σ` from
  `TauCeti.SymplecticForm.eval₂_mpullback_snd_constSmooth`.

The descended form `ω` on `G ×_K (A × V)` is then Tau Ceti's `TauCeti.SmoothForm.descendedForm`
along the surjective submersion `(g, p) ↦ [g, p]`. It is closed because `D.form` is, and it is
invariant under the action `k • [g, p] = [k g, p]` of `G` because `D.form` is invariant under left
translation of the factor `G`. This part adapts Tau Ceti's descent of the Kirillov form to a
coadjoint orbit, in `TauCeti/Geometry/Symplectic/Coadjoint/Orbit.lean`, one declaration at a
time: `isBasic_form` follows `Module.Dual.isBasic_leftInvariantKirillovForm`, `descendedForm`
follows `Module.Dual.coadjointOrbitForm`, `mpullback_mk_descendedForm` follows
`Module.Dual.mpullback_quotientMk_coadjointOrbitForm`, `eq_descendedForm_iff` follows
`Module.Dual.eq_coadjointOrbitForm_iff`, `eval₂_descendedForm_mfderiv` follows
`Module.Dual.eval₂_coadjointOrbitForm_mfderiv`, and `mpullback_smul_descendedForm` follows
`Module.Dual.mpullback_smul_coadjointOrbitForm`.

## Main results

* `SymplecticGeometry.LocalModelData.mvfderiv_covector_apply_fundamentalVectorField`: the
  derivative of `ν` along the infinitesimal action of the Lie algebra of `K` on `A × V` is the
  infinitesimal coadjoint action.
* `SymplecticGeometry.LocalModelData.ker_mfderiv_mk_le_ker_bilinFormAt_form`: the vertical
  directions of `G × (A × V) → G ×_K (A × V)` lie in the kernel of `D.form`, in the form of the
  hypothesis `hker` of `TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le`.
* `SymplecticGeometry.LocalModelData.mem_ker_mfderiv_mk_one_zero_iff`: at `(1, 0, 0)`, the
  vertical directions are the vectors `(ξ, 0, 0)` with `ξ ∈ 𝔥`.
* `SymplecticGeometry.LocalModelData.isBasic_form`: `D.form` is basic for the projection.
* `SymplecticGeometry.LocalModelData.descendedForm`: the descended form `ω` on `G ×_K (A × V)`.
* `SymplecticGeometry.LocalModelData.mpullback_mk_descendedForm`,
  `SymplecticGeometry.LocalModelData.eq_descendedForm_iff`: `ω` is the unique two-form whose
  pullback to `G × (A × V)` is `D.form`.
* `SymplecticGeometry.LocalModelData.isClosed_descendedForm`: `ω` is closed.
* `SymplecticGeometry.LocalModelData.mpullback_smul_descendedForm`: `ω` is invariant under the
  action of `G`.

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

/-- The derivative of the covectors `ν` of the local model along the infinitesimal action of the
Lie algebra of `K` on `A × V` is the infinitesimal coadjoint action: in the direction of the
fundamental vector field of `ξ` at `p`, the derivative of `y ↦ ν y ζ` is `ν p ⁅ζ, ξ'⁆`, where
`ξ'` is the image of `ξ` in `𝔤`. This is the derivative at `1` of `ν (k • p) = Ad*_k (ν p)`, with
the sign of `TauCeti.Lie.mvfderiv_coadjointRepresentation_apply_one`. -/
theorem mvfderiv_covector_apply_fundamentalVectorField (p : A × V)
    (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) (ζ : GroupLieAlgebra I G) :
    letI := D.fiberDistribMulAction
    mvfderiv 𝓘(ℝ, A × V) (fun y ↦ D.covector y ζ) p
        (fundamentalVectorField 𝓘(ℝ, A × V) ξ p) =
      D.covector p ⁅ζ, K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ⁆ := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  -- Along the orbit map `k ↦ k • p`, the component `y ↦ ν y ζ` becomes the coadjoint matrix
  -- coefficient `k ↦ (Ad*_k (ν p)) ζ`, by `covector_smul`.
  have hcomp : (fun y ↦ D.covector y ζ) ∘ (fun k : K ↦ k • p) =
      fun k : K ↦ coadjointRepresentation ℝ I G k (D.covector p) ζ :=
    funext fun k ↦ by rw [Function.comp_apply, covector_smul]
  have hν : MDifferentiableAt 𝓘(ℝ, A × V) 𝓘(ℝ) (fun y ↦ D.covector y ζ) p :=
    (D.contMDiff_covector_apply ζ).mdifferentiableAt (by simp)
  have horb : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, A × V) (fun k : K ↦ k • p) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := 𝓘(ℝ, F)) (n := ∞) p).mdifferentiableAt (by simp)
  rw [fundamentalVectorField_apply, ← mvfderiv_comp_apply_of_eq 1 hν horb (one_smul K p),
    hcomp, mvfderiv_coadjointRepresentation_subtype_apply_one]

/-- **The local model's form vanishes on vertical vectors.** At every point of `G × (A × V)`, the
kernel of the differential of the projection `(g, p) ↦ [g, p]` onto the balanced product
`G ×_K (A × V)` lies in the kernel of the two-form `D.form`: a vertical vector pairs to zero with
every tangent vector. This is the hypothesis `hker` of
`TauCeti.SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le`. -/
theorem ker_mfderiv_mk_le_ker_bilinFormAt_form [I.Boundaryless] (x : G × (A × V)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) x).ker ≤
      LinearMap.ker (D.form.bilinFormAt x) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  obtain ⟨g, η, v⟩ := x
  intro u hu
  obtain ⟨ξ, hξ⟩ := (BalancedProduct.mem_ker_mfderiv_mk_toRightTranslation_iff g (η, v) u).1 hu
  refine LinearMap.ext fun w ↦ ?_
  rw [SmoothForm.bilinFormAt_apply, LinearMap.zero_apply]
  -- `ξ'` is the image of `ξ` in `𝔤`, which lies in `𝔥`; `X = (a, b)` is the infinitesimal action of
  -- `ξ` at `(η, v)`, with `b = ρ ξ' v`. The vector `u` is `(-ξ'^L(g), X)`.
  set ξ' := K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ
  have hξ' : ξ' ∈ D.𝔥 := D.groupLieAlgebraMap_subtype_mem_𝔥 ξ
  set X : A × V := fundamentalVectorField 𝓘(ℝ, A × V) ξ (η, v) with hX
  have hb : X.2 = (D.ρ ⟨ξ', hξ'⟩ : Module.End ℝ V) v := by
    rw [hX, fundamentalVectorField_apply, mfderiv_fiberDistribMulAction_smul_apply]
  -- The covectors `ν`, read as continuous linear forms, and the derivatives of their components.
  -- The value `toContinuousLinearMap (ν y) ζ` is `ν y ζ` by definition; the statement of
  -- `LinearMap.coe_toContinuousLinearMap'` cannot be rewritten under `fderiv` here, as
  -- `GroupLieAlgebra I G` carries no normed instances.
  have hf := contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E)
    (contMDiff_localModelCovector_apply D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥)
  have hd (ζ : GroupLieAlgebra I G) (w : TangentSpace 𝓘(ℝ, A × V) (η, v)) :
      _ = fderiv ℝ (fun y ↦ localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 y ζ) (η, v) w :=
    (mvfderiv_toContinuousLinearMap_apply (E := E)
      (fun ζ ↦ (contMDiff_localModelCovector_apply D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 ζ (η, v)).mdifferentiableAt
        (by simp)) w ζ).trans
      (mvfderiv_eq_fderiv_apply _ _ w)
  -- The derivative of `ν` along `X` is the infinitesimal coadjoint action of `ξ'`.
  have h₁ (ζ : GroupLieAlgebra I G) :
      fderiv ℝ (fun y ↦ localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 y ζ) (η, v) X =
        localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 (η, v) ⁅-ξ', ζ⁆ := by
    have h := D.mvfderiv_covector_apply_fundamentalVectorField (η, v) ξ ζ
    simp only [covector_def] at h
    rw [mvfderiv_eq_fderiv_apply] at h
    rw [h, neg_lie, ← lie_skew]
  -- `ι𝔪` vanishes on `ξ' ∈ 𝔥`, and `ι𝔥 (dμ_V(v) b) ξ' = σ (ρ ξ' v, b)`.
  have h₂ (a : A) : D.ι𝔪 a ξ' = 0 := D.ι𝔪_apply_of_mem_sup a (Submodule.mem_sup_left hξ')
  have h₃ (b : V) : D.ι𝔥 (D.σ.linearMomentMapCompPolar D.ρ v b) ξ' =
      D.σ ((D.ρ ⟨ξ', hξ'⟩ : Module.End ℝ V) v) b :=
    (D.ι𝔥_apply_coe _ ⟨ξ', hξ'⟩).trans (SymplecticForm.linearMomentMapCompPolar_apply _ _ _ _ _)
  rw [form_def, localModelForm_def]
  refine eval₂_inducedForm_eq_zero hf (ξ := -ξ') ?_ (fun ζ ↦ ?_) (fun w ↦ ?_) w
  · rw [hξ]
  · rw [hξ]
    dsimp only
    refine (hd ζ X).trans ((h₁ ζ).trans ?_)
    exact (congrFun (LinearMap.coe_toContinuousLinearMap' (show E →ₗ[ℝ] ℝ from _)) _).symm
  · -- The components of `w` are vectors of `A` and `V`; read them there.
    obtain ⟨a₂, b₂⟩ := w
    rw [hξ]
    dsimp only
    rw [← Prod.mk.eta (p := X), SymplecticForm.eval₂_mpullback_snd_constSmooth]
    refine Eq.trans ?_ (congrArg Neg.neg (hd (-ξ') (a₂, b₂))).symm
    rw [fderiv_localModelCovector_apply, map_neg, LinearMap.add_apply, h₂, h₃, zero_add, hb,
      neg_neg]

/-- **The vertical space at `(1, 0, 0)`.** A tangent vector at `(1, 0, 0)` lies in the kernel of
the differential of the projection `(g, p) ↦ [g, p]` onto `G ×_K (A × V)` exactly when it is
`(ξ, 0, 0)` for some `ξ ∈ 𝔥`: at `p = 0` the infinitesimal action of `K` on `A × V` vanishes, and
the images in `𝔤` of the Lie algebra of `K` fill `𝔥`. By
`SymplecticGeometry.LocalModelData.forall_eval₂_form_one_zero_eq_zero_iff`, this is also the
kernel of `D.form` at `(1, 0, 0)`. -/
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
  -- `K` fixes `0 ∈ A × V`, so its fundamental vector fields vanish there.
  have h0 (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) :
      fundamentalVectorField 𝓘(ℝ, A × V) ξ ((0 : A), (0 : V)) = 0 :=
    fundamentalVectorField_eq_zero_of_forall_smul_eq (fun k ↦ smul_zero k) ξ
  rw [BalancedProduct.mem_ker_mfderiv_mk_toRightTranslation_iff, tangentSpaceProdEquiv_apply]
  simp only [h0, mulInvariantVectorField_one]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨neg_mem (D.groupLieAlgebraMap_subtype_mem_𝔥 ξ), (Submodule.mem_bot ℝ).2 rfl⟩
  · rintro ⟨hξ, hab⟩
    obtain ⟨ξ, hξ'⟩ := D.range_groupLieAlgebraMap_subtype.ge (neg_mem hξ)
    refine ⟨ξ, Prod.ext ?_ ((Submodule.mem_bot ℝ).1 hab)⟩
    simp only [ContinuousLinearMap.coe_coe] at hξ'
    rw [hξ', neg_neg]

/-! ### The descended form -/

section Descended

variable [I.Boundaryless]

/-- **The local model's form is basic** for the projection `(g, p) ↦ [g, p]` of `G × (A × V)` onto
the balanced product `G ×_K (A × V)`: it is invariant under the action
`k • (g, p) = (g k⁻¹, k • p)` of `K`, whose orbits are the fibres, and vanishes on vertical
vectors. -/
theorem isBasic_form :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    RoughForm.IsBasic (V := ℝ) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) D.form.val := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have hk (k : K) := ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, A × V))
    (n := ∞) (M := A × V) k
  refine SmoothTwoForm.isBasic_of_mpullback_eq_of_ker_mfderiv_le
    (τ := fun k : K ↦ Prod.map (· * (k : G)⁻¹) fun p : A × V ↦ k • p)
    (BalancedProduct.isSubmersion_mk_toRightTranslation.contMDiff.mdifferentiable (by simp))
    (fun k ↦ (contMDiff_mul_right.prodMap (hk k)).mdifferentiable (by simp))
    (fun k ↦ funext fun x ↦ ?_) (fun x y hxy ↦ .inr ?_) D.ker_mfderiv_mk_le_ker_bilinFormAt_form
    fun k ↦ (SmoothForm.mpullback_eq_iff _).1 (D.mpullback_prodMap_mul_right_smul_form k)
  · -- `[g k⁻¹, k • p] = [g, k⁻¹ • k • p] = [g, p]`.
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    rw [← Subgroup.coe_inv, BalancedProduct.mk_toRightTranslation_mul, inv_smul_smul]
  · obtain ⟨k, hk₁, hk₂⟩ :=
      BalancedProduct.mk_toRightTranslation_eq_mk_toRightTranslation_iff.1 hxy.symm
    exact ⟨k, Prod.ext hk₁ hk₂⟩

/-- **The descended form of the local model**: the two-form on the balanced product
`G ×_K (A × V)` whose pullback along the projection `(g, p) ↦ [g, p]` is `D.form`
(`SymplecticGeometry.LocalModelData.eq_descendedForm_iff`). -/
def descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (BalancedProduct K K.RightTranslation (A × V)) :=
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  SmoothForm.descendedForm BalancedProduct.isSubmersion_mk_toRightTranslation
    BalancedProduct.surjective_mk_toRightTranslation D.form D.isBasic_form

theorem descendedForm_def :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    D.descendedForm = SmoothForm.descendedForm BalancedProduct.isSubmersion_mk_toRightTranslation
      BalancedProduct.surjective_mk_toRightTranslation D.form D.isBasic_form :=
  (rfl)

/-- The descended form of the local model pulls back to `D.form` along the projection
`G × (A × V) → G ×_K (A × V)`. -/
@[simp]
theorem mpullback_mk_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ hπ : ContMDiff (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2),
    SmoothForm.mpullback _ hπ D.descendedForm = D.form := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  intro hπ
  rw [descendedForm_def]
  exact SmoothForm.mpullback_descendedForm

/-- **Uniqueness of the descended form**: it is the only two-form on `G ×_K (A × V)` whose pullback
along the projection is `D.form`. -/
theorem eq_descendedForm_iff :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {β : SmoothTwoForm 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (BalancedProduct K K.RightTranslation (A × V))}
      (hπ : ContMDiff (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)),
    β = D.descendedForm ↔ SmoothForm.mpullback _ hπ β = D.form := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  intro β hπ
  rw [descendedForm_def]
  exact SmoothForm.eq_descendedForm_iff

/-- The descended form of the local model evaluates on images under the differential of the
projection `π : G × (A × V) → G ×_K (A × V)` as `D.form`: `ω_(π x)(dπ u, dπ w) = D.form_x(u, w)`. -/
theorem eval₂_descendedForm_mfderiv (x : G × (A × V))
    (u w : TangentSpace (I.prod 𝓘(ℝ, A × V)) x) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    SmoothBundleForm.eval₂ D.descendedForm (BalancedProduct.mk K (K.toRightTranslation x.1) x.2)
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
  rw [descendedForm_def]
  exact SmoothTwoForm.eval₂_descendedForm_mfderiv x u w

/-- The descended form of the local model is closed. -/
theorem isClosed_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    D.descendedForm.IsClosed := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  rw [descendedForm_def, SmoothForm.isClosed_descendedForm_iff]
  exact D.isClosed_form

/-- **`G` preserves the descended form**: the action `k • [g, p] = [k g, p]` of `k ∈ G` on
`G ×_K (A × V)` pulls the descended form of the local model back to itself. -/
@[simp]
theorem mpullback_smul_descendedForm (k : G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ hk : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
      fun y : BalancedProduct K K.RightTranslation (A × V) ↦ k • y,
    SmoothForm.mpullback (k • ·) hk D.descendedForm = D.descendedForm := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  intro hk
  have hπ := (BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)).contMDiff
  rw [D.eq_descendedForm_iff hπ, SmoothForm.mpullback_mpullback_of_comp_eq hπ hk
    (contMDiff_mul_left.prodMap contMDiff_id) hπ
    (funext fun p ↦ BalancedProduct.smul_mk_toRightTranslation k p.1 p.2),
    mpullback_mk_descendedForm, mpullback_mul_left_form]

end Descended

end LocalModelData

end SymplecticGeometry

end
