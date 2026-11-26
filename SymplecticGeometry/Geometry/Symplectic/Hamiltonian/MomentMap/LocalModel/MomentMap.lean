/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Manifold
public import SymplecticGeometry.Geometry.Lie.ProdFstMulAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap

/-!
# The moment map of the local model, on `G × (A × V)` and on `G ×_K (A × V)`

Let `G` be a real Lie group with Lie algebra `𝔤`, `N` a manifold and `ν : N → 𝔤*` a family of
covectors with smooth components. Let `G` act smoothly on `G × N` by left multiplication of the
first factor, `g • (h, p) = (g * h, p)`: the statements take any such action, together with this
equation, and `SymplecticGeometry.prodFstMulAction` is one. This file proves that
`μ (g, p) = Ad*_g (ν p)` is a coadjoint-equivariant moment map of this action for the
two-form `-d⟨ν, θ⟩ + pr_N^* β` of `SymplecticGeometry.leftInvariantCovectorMapForm`, whatever the
two-form `β` on `N`, and specializes this to the two-form of the Marle–Guillemin–Sternberg local
model on `G × (A × V)`, whose covectors are `ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)`.

The first summand of the form is the pullback of the canonical form of `T*G` along
`Φ ∘ (id × ν)`, with `Φ` Tau Ceti's left trivialization; this map intertwines the action on
`G × N` with the cotangent lift of left multiplication
(`TauCeti.CotangentBundle.leftTrivialization_mul`), so Tau Ceti's cotangent moment map
`TauCeti.CotangentBundle.isEquivariantMomentMap_momentMap` pulls back to a moment map of this
summand (`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.mpullback`), which is `μ` by
`TauCeti.CotangentBundle.momentMap_leftTrivialization`. This argument adapts the proof of Tau
Ceti's `TauCeti.Module.Dual.isEquivariantMomentMap_leftInvariantKirillovForm`, the case of `N` a
point. The second summand `pr_N^* β` pairs the fundamental vector fields, which project to zero
on `N` (`TauCeti.mfderiv_snd_fundamentalVectorField_of_smul_eq`), with every tangent vector to
zero, so it does not change the moment map.

The last part of the file descends this moment map to the balanced product `G ×_K (A × V)`.
Since `ν (k • p) = Ad*_k (ν p)` for `k ∈ K`, the map `(g, p) ↦ Ad*_g (ν p)` is constant on the
classes `[g, p] = [g k⁻¹, k • p]`, and so defines `μ_Y [g, p] = Ad*_g (ν p)`, as Tau Ceti's
`TauCeti.BalancedProduct.liftRightTranslation` of `ν` for the coadjoint action. The projection
`G × (A × V) → G ×_K (A × V)` is a `G`-equivariant surjective submersion which pulls the descended
form back to the form upstairs, so Tau Ceti's
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.of_mpullback_eq`, with the identity for the map
into `G × (A × V)`, makes `μ_Y` an equivariant moment map of the descended form; its components
are smooth by `Manifold.IsSubmersion.contMDiff_comp_iff`.

## Main results

* `SymplecticGeometry.isEquivariantMomentMap_leftInvariantCovectorMapForm`: `(g, p) ↦ Ad*_g (ν p)`
  is an equivariant moment map of `-d⟨ν, θ⟩ + pr_N^* β`.
* `SymplecticGeometry.isEquivariantMomentMap_localModelForm`,
  `SymplecticGeometry.LocalModelData.isEquivariantMomentMap_form`: the cases of the local model's
  form, from linear data and from `SymplecticGeometry.LocalModelData`.
* `SymplecticGeometry.LocalModelData.descendedMomentMap`: the moment map `μ_Y` on
  `G ×_K (A × V)`, with its value `SymplecticGeometry.LocalModelData.descendedMomentMap_mk` on
  classes, its equivariance `SymplecticGeometry.LocalModelData.descendedMomentMap_smul`, and
  `SymplecticGeometry.LocalModelData.descendedMomentMap_mk_zero` along the zero
  section.
* `SymplecticGeometry.LocalModelData.contMDiff_descendedMomentMap_apply`: its components are
  smooth.
* `SymplecticGeometry.LocalModelData.isEquivariantMomentMap_descendedForm`: it is an equivariant
  moment map of the descended form `SymplecticGeometry.LocalModelData.descendedForm`.

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

/-! ### The moment map of `-d⟨ν, θ⟩ + pr_N^* β` -/

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

section CovectorMap

variable {N : Type*} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The moment map of `-d⟨ν, θ⟩ + pr_N^* β`.** For an action of `G` on `G × N` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map `(g, p) ↦ Ad*_g (ν p)` is
a coadjoint-equivariant moment map of the two-form `-d⟨ν, θ⟩ + pr_N^* β` of
`SymplecticGeometry.leftInvariantCovectorMapForm`, for every two-form `β` on `N`. -/
theorem isEquivariantMomentMap_leftInvariantCovectorMapForm [T2Space G] [I.Boundaryless]
    [MulAction G (G × N)] [ContMDiffSMul I (I.prod J) ∞ G (G × N)]
    (hsmul : ∀ (g : G) (q : G × N), g • q = (g * q.1, q.2))
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) :
    SmoothTwoForm.IsEquivariantMomentMap (leftInvariantCovectorMapForm hν β)
      fun q : G × N ↦ coadjointRepresentation ℝ I G q.1 (ν q.2) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hf := contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν
  have hφ := (leftTrivialization I G).contMDiff.comp (contMDiff_id.prodMap hf)
  -- The map `Φ ∘ (id × ν)` intertwines the action on `G × N` with the cotangent-lifted action, so
  -- the cotangent moment map pulls back along it.
  have h := (isEquivariantMomentMap_momentMap (IG := I) (G := G) (I := I) (M := G)).mpullback hφ
    fun g q ↦ by
      rw [Function.comp_apply, Function.comp_apply, hsmul]
      exact leftTrivialization_mul g q.1 _
  -- `GroupLieAlgebra I G` is `E` by definition but has no normed instances, so `ν p` is read as
  -- a linear form on the normed space `E` to make it a continuous linear map.
  have hμ : momentMap I G ∘ (leftTrivialization I G ∘ Prod.map id
      fun p ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p)) =
        fun q : G × N ↦ coadjointRepresentation ℝ I G q.1 (ν q.2) :=
    funext fun q ↦ (momentMap_leftTrivialization _).trans
      (congrArg _ (LinearMap.coe_toContinuousLinearMap _))
  rw [hμ] at h
  rw [leftInvariantCovectorMapForm_def, SmoothForm.mpullback_mpullback]
  -- The summand `pr_N^* β` pairs the fundamental vector fields with every vector to zero.
  exact
    { contMDiff := h.contMDiff
      isHamiltonianVectorField ξ := (h.isHamiltonianVectorField ξ).add_of_eval₂_eq_zero
        fun q v ↦ by
          rw [InfinitesimalAction.fundamental_apply, SmoothForm.eval₂_mpullback,
            mfderiv_snd_fundamentalVectorField_of_smul_eq hsmul,
            SmoothBundleForm.eval₂_zero_left]
      apply_smul := h.apply_smul }

end CovectorMap

/-! ### The local model -/

section LinearData

variable {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (τ : Module.Dual ℝ (GroupLieAlgebra I G)) (ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))
  (ι𝔥 : Module.Dual ℝ 𝔥 →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))

/-- **The moment map of the local model's form on `G × (A × V)`.** For an action of `G` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map `(g, p) ↦ Ad*_g (ν p)`, with
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥`, is a coadjoint-equivariant moment map of the two-form
`localModelForm σ ρ τ ι𝔪 ι𝔥`. -/
theorem isEquivariantMomentMap_localModelForm [T2Space G] [I.Boundaryless]
    [MulAction G (G × (A × V))]
    [ContMDiffSMul I (I.prod 𝓘(ℝ, A × V)) ∞ G (G × (A × V))]
    (hsmul : ∀ (g : G) (q : G × (A × V)), g • q = (g * q.1, q.2)) :
    SmoothTwoForm.IsEquivariantMomentMap (localModelForm σ ρ τ ι𝔪 ι𝔥)
      fun q : G × (A × V) ↦
        coadjointRepresentation ℝ I G q.1 (localModelCovector σ ρ τ ι𝔪 ι𝔥 q.2) := by
  rw [localModelForm_def]
  exact isEquivariantMomentMap_leftInvariantCovectorMapForm hsmul _ _

end LinearData

namespace LocalModelData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The moment map of the local model's form on `G × (A × V)`.** For an action of `G` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map
`(g, p) ↦ Ad*_g (D.covector p)` is a coadjoint-equivariant moment map of `D.form`. -/
theorem isEquivariantMomentMap_form [T2Space G] [I.Boundaryless]
    [MulAction G (G × (A × V))]
    [ContMDiffSMul I (I.prod 𝓘(ℝ, A × V)) ∞ G (G × (A × V))]
    (hsmul : ∀ (g : G) (q : G × (A × V)), g • q = (g * q.1, q.2)) :
    SmoothTwoForm.IsEquivariantMomentMap D.form
      fun q : G × (A × V) ↦ coadjointRepresentation ℝ I G q.1 (D.covector q.2) := by
  simp only [form_def, covector_def]
  exact isEquivariantMomentMap_localModelForm _ _ _ _ _ hsmul

/-! ### The moment map on `G ×_K (A × V)` -/

/-- **The moment map of the local model** on the balanced product `G ×_K (A × V)`:
`[g, p] ↦ Ad*_g (D.covector p)`, that is, `[g, η, v] ↦ Ad*_g (τ + ι𝔪 η + ι𝔥 (μ_V v))`. It is
well defined because `D.covector (k • p) = Ad*_k (D.covector p)` for `k ∈ K`. -/
def descendedMomentMap :
    letI := D.fiberDistribMulAction
    BalancedProduct K K.RightTranslation (A × V) → Module.Dual ℝ (GroupLieAlgebra I G) :=
  letI := D.fiberDistribMulAction
  letI : MulAction G (Module.Dual ℝ (GroupLieAlgebra I G)) :=
    MulAction.compHom _ (coadjointRepresentation ℝ I G)
  BalancedProduct.liftRightTranslation ⟨D.covector, fun k p ↦ D.covector_smul k p⟩

/-- The moment map of the local model at `[g, p]` is `Ad*_g (D.covector p)`. -/
@[simp]
theorem descendedMomentMap_mk (g : G) (p : A × V) :
    letI := D.fiberDistribMulAction
    D.descendedMomentMap (BalancedProduct.mk K (K.toRightTranslation g) p) =
      coadjointRepresentation ℝ I G g (D.covector p) := by
  let := D.fiberDistribMulAction
  let : MulAction G (Module.Dual ℝ (GroupLieAlgebra I G)) :=
    MulAction.compHom _ (coadjointRepresentation ℝ I G)
  -- With the coadjoint action as `g • ·`, `D.descendedMomentMap` unfolds to
  -- `liftRightTranslation` of the covectors, whose value on classes is `g • D.covector p`.
  rw [← Module.End.smul_def, ← MulAction.compHom_smul_def]
  exact BalancedProduct.liftRightTranslation_mk _ g p

/-- The moment map of the local model is equivariant for the action `k • [g, p] = [k g, p]`
of `G` on `G ×_K (A × V)` and the coadjoint action: `μ_Y (k • y) = Ad*_k (μ_Y y)`. -/
theorem descendedMomentMap_smul (k : G)
    (y : letI := D.fiberDistribMulAction; BalancedProduct K K.RightTranslation (A × V)) :
    letI := D.fiberDistribMulAction
    D.descendedMomentMap (k • y) = coadjointRepresentation ℝ I G k (D.descendedMomentMap y) := by
  let := D.fiberDistribMulAction
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g p =>
    rw [BalancedProduct.smul_mk_toRightTranslation, descendedMomentMap_mk, descendedMomentMap_mk,
      map_mul, mul_apply_eq_comp]

/-- Along the zero section, the moment map of the local model is `[g, 0, 0] ↦ Ad*_g τ`. -/
theorem descendedMomentMap_mk_zero (g : G) :
    letI := D.fiberDistribMulAction
    D.descendedMomentMap (BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V))) =
      coadjointRepresentation ℝ I G g D.τ := by
  let := D.fiberDistribMulAction
  rw [descendedMomentMap_mk, ← Prod.zero_eq_mk, covector_zero]

variable [T2Space G] [I.Boundaryless]

/-- The components of the moment map of the local model are smooth on `G ×_K (A × V)`. -/
theorem contMDiff_descendedMomentMap_apply (ξ : GroupLieAlgebra I G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) 𝓘(ℝ) ∞
      fun y ↦ D.descendedMomentMap y ξ := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  let := prodFstMulAction G (A × V)
  have := contMDiffSMul_prodFstMulAction (I := I) (J := 𝓘(ℝ, A × V)) (n := ∞) (G := G)
    (N := A × V)
  -- Upstairs, the components are those of the moment map of `D.form`, which are smooth.
  have h := (D.isEquivariantMomentMap_form fun g q ↦ prodFstMulAction_smul g q).contMDiff ξ
  refine (BalancedProduct.isSubmersion_mk_toRightTranslation.contMDiff_comp_iff
    BalancedProduct.surjective_mk_toRightTranslation le_rfl).1 (h.congr fun q ↦ ?_)
  simp only [Function.comp_apply, descendedMomentMap_mk]

/-- **The moment map of the local model on `G ×_K (A × V)`.** The map
`[g, p] ↦ Ad*_g (D.covector p)` is a coadjoint-equivariant moment map of the descended form
`D.descendedForm` for the action `k • [g, p] = [k g, p]` of `G`. The form need not be
nondegenerate; it is symplectic on the open set of
`SymplecticGeometry.LocalModelData.exists_opens_isSymplectic_mpullback_descendedForm`. -/
theorem isEquivariantMomentMap_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    haveI := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    D.descendedForm.IsEquivariantMomentMap D.descendedMomentMap := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace (ProperSMul.QuotientModelSpace F (E × (A × V))) :=
    FiniteDimensional.completeSpace ℝ _
  let := prodFstMulAction G (A × V)
  have := contMDiffSMul_prodFstMulAction (I := I) (J := 𝓘(ℝ, A × V)) (n := ∞) (G := G)
    (N := A × V)
  have hπ := BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  -- Descend the moment map of `D.form` along the projection, with the identity for `i`.
  refine (D.isEquivariantMomentMap_form fun g q ↦ prodFstMulAction_smul g q).of_mpullback_eq
    contMDiff_id hπ.contMDiff ?_ BalancedProduct.surjective_mk_toRightTranslation
    (hπ.surjective_mfderiv (by simp)) (fun _ _ ↦ rfl) (fun g q ↦ ?_)
    D.contMDiff_descendedMomentMap_apply (funext fun q ↦ ?_)
  · rw [mpullback_mk_descendedForm, SmoothForm.mpullback_id, LinearMap.id_apply]
  · rw [prodFstMulAction_smul, BalancedProduct.smul_mk_toRightTranslation]
  · simp only [Function.comp_apply, id_eq, descendedMomentMap_mk]

end LocalModelData

end SymplecticGeometry

end
