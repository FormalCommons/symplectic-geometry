/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data

import SymplecticGeometry.Geometry.Lie.Adjoint.Coadjoint
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import SymplecticGeometry.Geometry.Lie.Adjoint.Splitting
import SymplecticGeometry.Geometry.Lie.FundamentalVectorField

/-!
# The action of `K` on the splitting and on the fibre `𝔪* × V` of the local model

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (𝔪* × V)`, with its `Ad_K`-invariant splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and the
identification `A ≃ 𝔪*`. This file gives the action of `K` on the fibre `𝔪* × V` of the local
model. First its linear algebra: the sums `𝔪 ⊕ 𝔮` and `𝔥 ⊕ 𝔮` are invariant under `Ad_K`, so the
extensions by zero `ι𝔥 : 𝔥* → 𝔤*` and `ι𝔪 : 𝔪* → 𝔤*` intertwine the duals of the adjoint
representations of `K` on `𝔥` and `𝔪` with the coadjoint representation of `K` on `𝔤*`.
The representation of `K` on `A` is the dual of the adjoint representation on `𝔪`, transported
to `A` by `D.equivDual𝔪`. Also, the infinitesimal map `ρ : 𝔥 → sp(V, σ)` and the moment map
`μ_V : V → 𝔥*` are equivariant for the representation `rep` of `K` on `V`.

Then the action `k • (η, v) = (repA k η, rep k v)` on `A × V`, and its smoothness, so that the
balanced product `G ×_K (A × V)` is a manifold when the model of `G` is boundaryless (Tau Ceti's
`TauCeti.BalancedProduct.isManifold_rightTranslation`). The action depends on `D`, so it is a
definition, `SymplecticGeometry.LocalModelData.fiberDistribMulAction`, to be used with `letI`,
not an instance; this keeps the carrier `A × V` of `D.covector` and `D.form`, rather than a type
synonym. The representation on `A` is smooth because the functionals `η ↦ ι𝔪 η ξ`, for `ξ ∈ 𝔤`,
separate the points of `A`, and by `ι𝔪_repA` their values on `repA k η` are coefficients of the
coadjoint representation, which are smooth on `G` (Tau Ceti's
`TauCeti.Lie.contMDiff_coadjointRepresentation_apply`).

The invariance of the sums is that of a sup of subrepresentations (Mathlib's lattice of
`Subrepresentation`). The equivariance of the extensions by zero is the case of the splitting of
`TauCeti.Lie.dualMap_projectionOnto_dual`, which follows the route described in the module
docstring of Tau Ceti's `TauCeti/Geometry/Lie/Adjoint/Splitting.lean`. The equivariance of `ρ`
is that of the orbit derivatives of the linear representation `rep` of `K` on `V`, the
library's `TauCeti.mfderiv_linearEquiv_apply_adjointContinuousLinearMap`, read through
`D.mfderiv_rep_apply` and the naturality `MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`
of the adjoint action for the inclusion `K → G`. That of `μ_V` follows from it, since each
`rep k` preserves `σ`.

Last, the covectors `ν` of the local model are equivariant, which combines the equivariance of
`τ`, `ι𝔪` and `μ_V`; and the infinitesimal action of the Lie algebra of `K` on `A × V`. Its
component in `A` is computed through the functionals `η ↦ equivDual𝔪 η ζ`, `ζ ∈ 𝔪`, which turn
`k ↦ repA k η` into a coadjoint coefficient, whose derivative
`TauCeti.Lie.mvfderiv_coadjointRepresentation_subtype_apply_one` gives: the chain rule along
`K → G` and Tau Ceti's `TauCeti.Lie.mvfderiv_coadjointRepresentation_apply_one`, with that lemma's
sign. Its component in `V` is `D.mfderiv_rep_apply`, and Tau Ceti's
`MDifferentiableAt.mvfderiv_prodMk_apply` combines the two. The equivariance of `ν`, with the
fact that each `rep k` preserves `σ` (Tau Ceti's
`TauCeti.SymplecticForm.IsSymplectomorphism.mpullback_constSmooth`), makes the form of the local
model invariant under `(g, p) ↦ (g * k⁻¹, k • p)`, by
`SymplecticGeometry.mpullback_prodMap_mul_right_leftInvariantCovectorMapForm`.

## Main definitions

* `SymplecticGeometry.LocalModelData.repA`: the representation of `K` on `A ≃ 𝔪*`, the dual of
  `SymplecticGeometry.LocalModelData.adjoint𝔪`.
* `SymplecticGeometry.LocalModelData.fiberDistribMulAction`: the action of `K` on `A × V`.

## Main results

* `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔪_sup`,
  `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔥_sup`: `𝔪 ⊕ 𝔮` and `𝔥 ⊕ 𝔮` are
  invariant under the adjoint action of `K`.
* `SymplecticGeometry.LocalModelData.isCompl_sub𝔥_sup`,
  `SymplecticGeometry.LocalModelData.isCompl_sub𝔪_sup`: the splittings `𝔤 = 𝔥 ⊕ (𝔪 ⊕ 𝔮)` and
  `𝔤 = 𝔪 ⊕ (𝔥 ⊕ 𝔮)` as subrepresentations.
* `SymplecticGeometry.LocalModelData.ι𝔥_adjoint𝔥_dual`,
  `SymplecticGeometry.LocalModelData.ι𝔪_symm_adjoint𝔪_dual`: `ι𝔥` and `ι𝔪` are equivariant.
* `SymplecticGeometry.LocalModelData.ι𝔪_repA`: `ι𝔪 (repA k η) = Ad*_k (ι𝔪 η)`.
* `SymplecticGeometry.LocalModelData.ρ_adjoint𝔥`: `ρ (Ad_k ξ) = rep k ∘ ρ ξ ∘ rep k⁻¹`.
* `SymplecticGeometry.LocalModelData.momentMap_rep`,
  `SymplecticGeometry.LocalModelData.ι𝔥_momentMap_rep`: `μ_V` is equivariant, and
  `ι𝔥 (μ_V (rep k v)) = Ad*_k (ι𝔥 (μ_V v))`.
* `SymplecticGeometry.LocalModelData.contMDiff_repA_apply`,
  `SymplecticGeometry.LocalModelData.contMDiff_repA`: the representation on `A` is smooth.
* `SymplecticGeometry.LocalModelData.contMDiffSMul_fiberDistribMulAction`: the action of `K` on
  `A × V` is smooth.
* `SymplecticGeometry.LocalModelData.smulCommClass_fiberDistribMulAction`: the action of `K`
  on `A × V` commutes with real scalars.
* `SymplecticGeometry.LocalModelData.fiberDistribMulAction_smul_eq_toContinuousLinearMap`,
  `SymplecticGeometry.LocalModelData.mfderiv_fiberDistribMulAction_const_smul`: each `k` acts on
  `A × V` by a continuous linear map, which is its own differential at every point.
* `SymplecticGeometry.LocalModelData.covector_smul`: `ν (k • p) = Ad*_k (ν p)`.
* `SymplecticGeometry.LocalModelData.mpullback_prodMap_mul_right_smul_form`: the form `D.form`
  on `G × (A × V)` is invariant under `(g, p) ↦ (g * k⁻¹, k • p)` for `k ∈ K`.
* `SymplecticGeometry.LocalModelData.equivDual𝔪_mfderiv_repA_apply`,
  `SymplecticGeometry.LocalModelData.mfderiv_repA_apply`,
  `SymplecticGeometry.LocalModelData.mfderiv_fiberDistribMulAction_smul_apply`: the infinitesimal
  action of the Lie algebra of `K` on `A ≃ 𝔪*` and on `A × V`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.Lie
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-! ### The invariant sums -/

/-- The sum `𝔪 ⊕ 𝔮` is invariant under the adjoint action of `K`. -/
theorem adjointRepresentation_mem_𝔪_sup (k : K) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ D.𝔪 ⊔ D.𝔮) : adjointRepresentation ℝ I G k ξ ∈ D.𝔪 ⊔ D.𝔮 :=
  (D.sub𝔪 ⊔ D.sub𝔮).apply_mem_toSubmodule k hξ

/-- The sum `𝔥 ⊕ 𝔮` is invariant under the adjoint action of `K`. -/
theorem adjointRepresentation_mem_𝔥_sup (k : K) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ D.𝔥 ⊔ D.𝔮) : adjointRepresentation ℝ I G k ξ ∈ D.𝔥 ⊔ D.𝔮 :=
  (D.sub𝔥 ⊔ D.sub𝔮).apply_mem_toSubmodule k hξ

/-- The splitting `𝔤 = 𝔥 ⊕ (𝔪 ⊕ 𝔮)` as subrepresentations of the adjoint representation of `K`. -/
theorem isCompl_sub𝔥_sup : IsCompl D.sub𝔥 (D.sub𝔪 ⊔ D.sub𝔮) := by
  rw [← Subrepresentation.isCompl_toSubmodule, Subrepresentation.toSubmodule_sup,
    toSubmodule_sub𝔥, toSubmodule_sub𝔪, toSubmodule_sub𝔮]
  exact D.isCompl_𝔥_sup

/-- The splitting `𝔤 = 𝔪 ⊕ (𝔥 ⊕ 𝔮)` as subrepresentations of the adjoint representation of `K`. -/
theorem isCompl_sub𝔪_sup : IsCompl D.sub𝔪 (D.sub𝔥 ⊔ D.sub𝔮) := by
  rw [← Subrepresentation.isCompl_toSubmodule, Subrepresentation.toSubmodule_sup,
    toSubmodule_sub𝔥, toSubmodule_sub𝔪, toSubmodule_sub𝔮]
  exact D.isCompl_𝔪_sup

/-! ### Equivariance of the extensions by zero -/

/-- The extension by zero `ι𝔥 : 𝔥* → 𝔤*` is equivariant: it takes the dual of the adjoint
representation of `K` on `𝔥` to the coadjoint representation, `ι𝔥 (f ∘ Ad_{k⁻¹}) = Ad*_k (ι𝔥 f)`.
-/
theorem ι𝔥_adjoint𝔥_dual (k : K) (f : Module.Dual ℝ D.𝔥) :
    D.ι𝔥 (D.adjoint𝔥.dual k f) = coadjointRepresentation ℝ I G k (D.ι𝔥 f) := by
  rw [ι𝔥_def, adjoint𝔥_def]
  -- The lemma is stated with `D.sub𝔥.toSubmodule` and `(D.sub𝔪 ⊔ D.sub𝔮).toSubmodule`, which
  -- are `D.𝔥` and `D.𝔪 ⊔ D.𝔮` by definition.
  exact dualMap_projectionOnto_dual D.isCompl_sub𝔥_sup k f

/-- The extension by zero `𝔪* → 𝔤*` is equivariant: it takes the dual of the adjoint
representation of `K` on `𝔪` to the coadjoint representation. Here `𝔪*` is read in `A` through
`D.equivDual𝔪`. -/
theorem ι𝔪_symm_adjoint𝔪_dual (k : K) (f : Module.Dual ℝ D.𝔪) :
    D.ι𝔪 (D.equivDual𝔪.symm (D.adjoint𝔪.dual k f)) =
      coadjointRepresentation ℝ I G k (D.ι𝔪 (D.equivDual𝔪.symm f)) := by
  rw [ι𝔪_def, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, adjoint𝔪_def]
  -- The lemma is stated with `D.sub𝔪.toSubmodule` and `(D.sub𝔥 ⊔ D.sub𝔮).toSubmodule`, which
  -- are `D.𝔪` and `D.𝔥 ⊔ D.𝔮` by definition.
  exact dualMap_projectionOnto_dual D.isCompl_sub𝔪_sup k f

/-! ### The representation of `K` on `A ≃ 𝔪*` -/

/-- The representation of `K` on `A`: the dual of the adjoint representation of `K` on `𝔪`,
transported to `A` by the identification `D.equivDual𝔪 : A ≃ 𝔪*`. -/
def repA : Representation ℝ K A :=
  (D.equivDual𝔪.symm.conjAlgEquiv ℝ).toMonoidHom.comp D.adjoint𝔪.dual

theorem repA_apply (k : K) (η : A) :
    D.repA k η = D.equivDual𝔪.symm (D.adjoint𝔪.dual k (D.equivDual𝔪 η)) :=
  (rfl)

@[simp]
theorem equivDual𝔪_repA (k : K) (η : A) :
    D.equivDual𝔪 (D.repA k η) = D.adjoint𝔪.dual k (D.equivDual𝔪 η) := by
  rw [repA_apply, LinearEquiv.apply_symm_apply]

/-- The extension by zero `ι𝔪 : A → 𝔤*` intertwines the representation of `K` on `A ≃ 𝔪*` with
the coadjoint representation: `ι𝔪 (repA k η) = Ad*_k (ι𝔪 η)`. -/
theorem ι𝔪_repA (k : K) (η : A) :
    D.ι𝔪 (D.repA k η) = coadjointRepresentation ℝ I G k (D.ι𝔪 η) := by
  rw [repA_apply, ι𝔪_symm_adjoint𝔪_dual, LinearEquiv.symm_apply_apply]

/-- The orbit maps `k ↦ repA k η` of the representation of `K` on `A ≃ 𝔪*` are smooth. -/
theorem contMDiff_repA_apply (η : A) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, A) ∞ fun k : K ↦ D.repA k η := by
  have hK := K.contMDiff_subtypeVal_of_contMDiffSMul (I := I) (I' := 𝓘(ℝ, F)) (n := ∞)
  -- The functionals `η ↦ ι𝔪 η ξ` separate the points of `A`, and their values on `repA k η` are
  -- coadjoint matrix coefficients, by `ι𝔪_repA`.
  have hs : ∀ g ∈ Set.range fun ξ ↦ (Module.Dual.eval ℝ _ ξ).comp D.ι𝔪,
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ fun k : K ↦ g (D.repA k η) := by
    rintro _ ⟨ξ, rfl⟩
    simp only [LinearMap.comp_apply, Module.Dual.eval_apply, ι𝔪_repA]
    exact (contMDiff_coadjointRepresentation_apply (D.ι𝔪 η) ξ).comp hK
  refine (contMDiff_linearMap_comp_of_dual (contMDiff_dual_apply_of_separating
    (fun z hz ↦ ?_) hs) (LinearMap.id : A →ₗ[ℝ] A)).congr fun k ↦ (LinearMap.id_apply _).symm
  obtain ⟨ξ, hξ⟩ : ∃ ξ : D.𝔪, D.equivDual𝔪 z ξ ≠ 0 := by
    by_contra! h
    exact hz (D.equivDual𝔪.map_eq_zero_iff.1 (LinearMap.ext h))
  exact ⟨_, ⟨ξ, rfl⟩, by simpa [ι𝔪_apply_coe] using hξ⟩

/-- The representation of `K` on `A ≃ 𝔪*` is smooth: `(k, η) ↦ repA k η` is smooth on `K × A`. -/
theorem contMDiff_repA :
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, A)) 𝓘(ℝ, A) ∞ fun p : K × A ↦ D.repA p.1 p.2 := by
  have hL : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, A →L[ℝ] A) ∞
      fun k : K ↦ LinearMap.toContinuousLinearMap (D.repA k) :=
    fun k ↦ contMDiffAt_clm_apply.2 fun η ↦ (D.contMDiff_repA_apply η).contMDiffAt
  exact (hL.comp contMDiff_fst).clm_apply contMDiff_snd

/-! ### The action of `K` on the fibre `A × V ≃ 𝔪* × V` -/

/-- The linear action of `K` on the fibre `A × V ≃ 𝔪* × V` of the local model,
`k • (η, v) = (repA k η, rep k v)`. It depends on `D`, so it is not a global instance: use it with
`letI := D.fiberDistribMulAction`. -/
@[instance_reducible]
def fiberDistribMulAction : DistribMulAction K (A × V) :=
  DistribMulAction.compHom (A × V) (D.repA.prod D.repV)

/-- The action of `K` on `A × V`. Not a simp lemma: its left side is a scalar multiplication by
an action that is not an instance. -/
theorem fiberDistribMulAction_smul (k : K) (p : A × V) :
    letI := D.fiberDistribMulAction
    k • p = (D.repA k p.1, D.rep k p.2) :=
  -- The second component is `D.repV k p.2`, whose body is not exposed.
  Prod.ext (rfl) (D.repV_apply k p.2)

/-- The action of `K` on `A × V` commutes with multiplication by real scalars. -/
theorem smulCommClass_fiberDistribMulAction :
    letI := D.fiberDistribMulAction
    SMulCommClass K ℝ (A × V) :=
  letI := D.fiberDistribMulAction
  ⟨fun k c p ↦ by simp [D.fiberDistribMulAction_smul]⟩

/-- The action of `K` on the fibre `A × V` is smooth. With it, the balanced product
`TauCeti.BalancedProduct K (Subgroup.RightTranslation K) (A × V)`, the local model `G ×_K (A × V)`,
is a smooth manifold when the model `I` of `G` is boundaryless
(`TauCeti.BalancedProduct.isManifold_rightTranslation`). -/
theorem contMDiffSMul_fiberDistribMulAction :
    letI := D.fiberDistribMulAction
    ContMDiffSMul 𝓘(ℝ, F) 𝓘(ℝ, A × V) ∞ K (A × V) := by
  let := D.fiberDistribMulAction
  have hA : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, A × V)) (𝓘(ℝ, F).prod 𝓘(ℝ, A)) ∞
      fun p : K × (A × V) ↦ (p.1, p.2.1) :=
    contMDiff_fst.prodMk (contDiff_fst.contMDiff.comp contMDiff_snd)
  have hV : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, A × V)) (𝓘(ℝ, F).prod 𝓘(ℝ, V)) ∞
      fun p : K × (A × V) ↦ (p.1, p.2.2) :=
    contMDiff_fst.prodMk (contDiff_snd.contMDiff.comp contMDiff_snd)
  exact ⟨((D.contMDiff_repA.comp hA).prodMk_space (D.contMDiff_rep.comp hV)).congr
    fun p ↦ D.fiberDistribMulAction_smul p.1 p.2⟩

/-- The action of `k` on the fibre `A × V` is the continuous linear map
`(η, v) ↦ (repA k η, rep k v)`. -/
theorem fiberDistribMulAction_smul_eq_toContinuousLinearMap (k : K) :
    letI := D.fiberDistribMulAction
    (fun p : A × V ↦ k • p) = LinearMap.toContinuousLinearMap ((D.repA.prod D.repV) k) :=
  letI := D.fiberDistribMulAction
  funext fun p ↦ (D.fiberDistribMulAction_smul k p).trans (by simp [repV_apply])

/-- The differential of the action of `k` on the fibre `A × V`, at any point, is the action of
`k`, since the action is linear. -/
theorem mfderiv_fiberDistribMulAction_const_smul (k : K) (q p : A × V) :
    letI := D.fiberDistribMulAction
    mfderiv 𝓘(ℝ, A × V) 𝓘(ℝ, A × V) (fun y : A × V ↦ k • y) q p = k • p := by
  rw [fiberDistribMulAction_smul_eq_toContinuousLinearMap, ContinuousLinearMap.mfderiv_eq]
  exact congrFun (D.fiberDistribMulAction_smul_eq_toContinuousLinearMap k).symm p

/-! ### Equivariance of `ρ` and of `μ_V` -/

/-- The infinitesimal map `ρ : 𝔥 → sp(V, σ)` is equivariant:
`ρ (Ad_k ξ) v = rep k (ρ ξ (rep k⁻¹ v))` for `k ∈ K`, `ξ ∈ 𝔥` and `v ∈ V`. -/
theorem ρ_adjoint𝔥_apply (k : K) (ξ : D.𝔥) (v : V) :
    (D.ρ (D.adjoint𝔥 k ξ) : Module.End ℝ V) v =
      D.rep k ((D.ρ ξ : Module.End ℝ V) (D.rep k⁻¹ v)) := by
  obtain ⟨ζ, hζ⟩ := D.range_groupLieAlgebraMap_subtype.ge ξ.property
  obtain rfl : ξ = ⟨_, D.groupLieAlgebraMap_subtype_mem_𝔥 ζ⟩ := Subtype.ext hζ.symm
  have hAd : D.adjoint𝔥 k ⟨_, D.groupLieAlgebraMap_subtype_mem_𝔥 ζ⟩ =
      ⟨_, D.groupLieAlgebraMap_subtype_mem_𝔥 (adjointContinuousLinearMap (I := 𝓘(ℝ, F)) k ζ)⟩ :=
    Subtype.ext <| by
      simp only [coe_adjoint𝔥_apply, adjointRepresentation_apply,
        MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap, Subgroup.coe_subtype]
  rw [hAd, ← mfderiv_rep_apply, ← mfderiv_rep_apply]
  exact mfderiv_linearEquiv_apply_adjointContinuousLinearMap D.rep
    (D.contMDiff_rep.of_le (by simp)) k ζ v

/-- The infinitesimal map `ρ : 𝔥 → sp(V, σ)` is equivariant: `ρ (Ad_k ξ)` is the conjugate
`rep k ∘ ρ ξ ∘ rep k⁻¹` of `ρ ξ`. -/
theorem ρ_adjoint𝔥 (k : K) (ξ : D.𝔥) :
    (D.ρ (D.adjoint𝔥 k ξ) : Module.End ℝ V) =
      (D.rep k).toLinearMap ∘ₗ (D.ρ ξ : Module.End ℝ V) ∘ₗ (D.rep k⁻¹).toLinearMap :=
  LinearMap.ext (D.ρ_adjoint𝔥_apply k ξ)

/-- The moment map `μ_V : V → 𝔥*` is equivariant: `μ_V (rep k v)` is the dual of the adjoint
representation of `K` on `𝔥` applied to `μ_V v`. -/
theorem momentMap_rep (k : K) (v : V) :
    D.momentMap (D.rep k v) = D.adjoint𝔥.dual k (D.momentMap v) := by
  ext ξ
  rw [momentMap_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, momentMap_apply, ρ_adjoint𝔥_apply, inv_inv,
    ← (D.isSymplectomorphism_rep k).apply (D.rep k⁻¹ _) v, ← D.repV_apply k⁻¹,
    ← D.repV_apply k (D.repV k⁻¹ _), Representation.self_inv_apply]

/-- The moment map `μ_V`, extended by zero to `𝔤*`, is equivariant:
`ι𝔥 (μ_V (rep k v)) = Ad*_k (ι𝔥 (μ_V v))`. -/
theorem ι𝔥_momentMap_rep (k : K) (v : V) :
    D.ι𝔥 (D.momentMap (D.rep k v)) = coadjointRepresentation ℝ I G k (D.ι𝔥 (D.momentMap v)) := by
  rw [momentMap_rep, ι𝔥_adjoint𝔥_dual]

/-! ### Equivariance of the covectors and the infinitesimal action -/

/-- The covectors `ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` of the local model are equivariant:
`ν (k • p) = Ad*_k (ν p)` for the action of `K` on `A × V`. -/
theorem covector_smul (k : K) (p : A × V) :
    letI := D.fiberDistribMulAction
    D.covector (k • p) = coadjointRepresentation ℝ I G k (D.covector p) := by
  obtain ⟨η, v⟩ := p
  ext ξ
  have hτ : D.τ ξ = D.τ (adjointContinuousLinearMap (I := I) (k : G)⁻¹ ξ) := by
    rw [← coadjointRepresentation_apply, D.coadjointRepresentation_τ]
  rw [fiberDistribMulAction_smul, covector_apply, ι𝔪_repA, ι𝔥_momentMap_rep,
    coadjointRepresentation_apply, coadjointRepresentation_apply, coadjointRepresentation_apply,
    covector_apply, hτ]

/-- The two-form of the local model on `G × (A × V)` is invariant under the action
`(g, p) ↦ (g * k⁻¹, k • p)` of `k ∈ K`: the covectors `ν` are equivariant (`covector_smul`), and
each `rep k` preserves `σ`. -/
@[simp]
theorem mpullback_prodMap_mul_right_smul_form (k : K) :
    letI := D.fiberDistribMulAction
    SmoothForm.mpullback (Prod.map (· * (k : G)⁻¹) fun p : A × V ↦ k • p)
        (contMDiff_mul_right.prodMap (haveI := D.contMDiffSMul_fiberDistribMulAction
          ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) k)) D.form =
      D.form := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  have hk := ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, A × V)) (n := ∞)
    (M := A × V) k
  -- The term `pr_V^* σ` is invariant, as `pr_V (k • p) = rep k (pr_V p)` and `rep k` preserves `σ`.
  have hσ : SmoothForm.mpullback (fun p : A × V ↦ k • p) hk
      (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff D.σ.constSmooth) =
        SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff D.σ.constSmooth := by
    have he : SymplecticForm.IsSymplectomorphism D.σ D.σ
        (D.rep k).toContinuousLinearEquiv.toLinearEquiv := by
      rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
      exact D.isSymplectomorphism_rep k
    rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contDiff_snd.contMDiff
      (D.rep k).toContinuousLinearEquiv.toDiffeomorph.contMDiff
      (funext fun p ↦ congrArg Prod.snd (D.fiberDistribMulAction_smul k p)),
      he.mpullback_constSmooth]
  rw [form_def, localModelForm_def]
  exact mpullback_prodMap_mul_right_leftInvariantCovectorMapForm _ (k : G) hk
    (fun p ↦ by rw [← covector_def, ← covector_def]; exact D.covector_smul k p) hσ

/-- The infinitesimal representation of the Lie algebra of `K` on `A ≃ 𝔪*`: the derivative at `1`
of `k ↦ repA k η` in the direction `ξ`, read in `𝔪*` through `D.equivDual𝔪`, is
`ζ ↦ ι𝔪 η ⁅ζ, ξ'⁆`, where `ξ'` is the image of `ξ` in `𝔤`, which lies in `𝔥`. This is the sign of
`TauCeti.Lie.mvfderiv_coadjointRepresentation_apply_one`. -/
theorem equivDual𝔪_mfderiv_repA_apply (η : A) (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) (ζ : D.𝔪) :
    D.equivDual𝔪 (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, A) (fun k : K ↦ D.repA k η) 1 ξ) ζ =
      D.ι𝔪 η ⁅(ζ : GroupLieAlgebra I G), K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ⁆ := by
  -- The functional `a ↦ equivDual𝔪 a ζ` on `A`, through which `k ↦ repA k η` becomes the
  -- coadjoint matrix coefficient `k ↦ (Ad*_k (ι𝔪 η)) ζ`, by `ι𝔪_repA`.
  let ℓ : A →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((Module.Dual.eval ℝ _ ζ) ∘ₗ D.equivDual𝔪.toLinearMap)
  have hℓ (a : A) : ℓ a = D.equivDual𝔪 a ζ := by simp [ℓ]
  have hcomp : (ℓ ∘ fun k : K ↦ D.repA k η) =
      fun k : K ↦ coadjointRepresentation ℝ I G k (D.ι𝔪 η) ζ := by
    funext k
    rw [Function.comp_apply, hℓ, ← ι𝔪_apply_coe, ι𝔪_repA]
  refine (hℓ _).symm.trans ?_
  rw [← mvfderiv_apply_eq_mfderiv_apply,
    ← ℓ.mvfderiv_comp_apply ((D.contMDiff_repA_apply η).mdifferentiableAt (by simp)),
    hcomp, mvfderiv_coadjointRepresentation_subtype_apply_one]

/-- The infinitesimal representation of the Lie algebra of `K` on `A ≃ 𝔪*`: the derivative at `1`
of `k ↦ repA k η` in the direction `ξ` is the element of `A` that corresponds to the covector
`ζ ↦ ι𝔪 η ⁅ζ, ξ'⁆ = -ι𝔪 η ⁅ξ', ζ⁆` on `𝔪`, where `ξ'` is the image of `ξ` in `𝔤`, which lies
in `𝔥`. -/
theorem mfderiv_repA_apply (η : A) (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, A) (fun k : K ↦ D.repA k η) 1 ξ =
      D.equivDual𝔪.symm (-(D.ι𝔪 η ∘ₗ
        LieAlgebra.ad ℝ _ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) ∘ₗ D.𝔪.subtype)) := by
  refine D.equivDual𝔪.injective (LinearMap.ext fun ζ ↦ ?_)
  rw [equivDual𝔪_mfderiv_repA_apply, LinearEquiv.apply_symm_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, LieAlgebra.ad_apply,
    ← map_neg, ← lie_skew]

/-- The infinitesimal action of the Lie algebra of `K` on the fibre `A × V ≃ 𝔪* × V`: the
derivative at `1` of `k ↦ k • (η, v)` in the direction `ξ` is `(a, ρ ξ' v)`, where `ξ'` is the
image of `ξ` in `𝔤`, which lies in `𝔥`, and `a ∈ A` corresponds to the covector
`ζ ↦ ι𝔪 η ⁅ζ, ξ'⁆ = -ι𝔪 η ⁅ξ', ζ⁆` on `𝔪`. -/
theorem mfderiv_fiberDistribMulAction_smul_apply (p : A × V) (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) :
    letI := D.fiberDistribMulAction
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, A × V) (fun k : K ↦ k • p) 1 ξ =
      (D.equivDual𝔪.symm (-(D.ι𝔪 p.1 ∘ₗ
          LieAlgebra.ad ℝ _ (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ) ∘ₗ D.𝔪.subtype)),
        (D.ρ ⟨_, D.groupLieAlgebraMap_subtype_mem_𝔥 ξ⟩ : Module.End ℝ V) p.2) := by
  let := D.fiberDistribMulAction
  have hsmul : (fun k : K ↦ k • p) = fun k ↦ (D.repA k p.1, D.rep k p.2) :=
    funext fun k ↦ D.fiberDistribMulAction_smul k p
  rw [hsmul]
  refine (mvfderiv_apply_eq_mfderiv_apply (F := A × V) _ _ _).symm.trans ?_
  rw [((D.contMDiff_repA_apply p.1).mdifferentiableAt (by simp)).mvfderiv_prodMk_apply
      ((D.contMDiff_rep.curry_left).mdifferentiableAt (by simp)),
    mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, mfderiv_repA_apply,
    mfderiv_rep_apply]

end LocalModelData

end SymplecticGeometry

end
