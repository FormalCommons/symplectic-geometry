/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Adjoint.Splitting
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data

import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension

/-!
# The action of `K` on the splitting and on the fibre `𝔪* × V` of the local model

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (𝔪* × V)`, with its `Ad_K`-invariant splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and the
identification `A ≃ 𝔪*`. This file gives the action of `K` on the fibre `𝔪* × V` of the local
model. First its linear algebra: the sums `𝔪 ⊕ 𝔮` and `𝔥 ⊕ 𝔮` are invariant under `Ad_K`, so the
extensions by zero `ι𝔥 : 𝔥* → 𝔤*` and `ι𝔪 : 𝔪* → 𝔤*` intertwine the duals of the adjoint
representations of `K` on `𝔥` and `𝔪` with the coadjoint representation of `K` on `𝔤*`.
The representation of `K` on `A` is the dual of the adjoint representation on `𝔪`, transported
to `A` by `D.equivDual𝔪`.

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
docstring of Tau Ceti's `TauCeti/Geometry/Lie/Adjoint/Splitting.lean`.

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
* `SymplecticGeometry.LocalModelData.contMDiff_repA`: the representation on `A` is smooth.
* `SymplecticGeometry.LocalModelData.contMDiffSMul_fiberDistribMulAction`: the action of `K` on
  `A × V` is smooth.
* `SymplecticGeometry.LocalModelData.smulCommClass_fiberDistribMulAction`: the action of `K`
  on `A × V` commutes with real scalars.

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

/-- The representation of `K` on `A ≃ 𝔪*` is smooth: `(k, η) ↦ repA k η` is smooth on `K × A`. -/
theorem contMDiff_repA :
    ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, A)) 𝓘(ℝ, A) ∞ fun p : K × A ↦ D.repA p.1 p.2 := by
  have hK := K.contMDiff_subtypeVal_of_contMDiffSMul (I := I) (I' := 𝓘(ℝ, F)) (n := ∞)
  -- The functionals `η ↦ ι𝔪 η ξ` separate the points of `A`, and their values on `repA k η` are
  -- coadjoint matrix coefficients, by `ι𝔪_repA`.
  have hpt (η : A) : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, A) ∞ fun k : K ↦ D.repA k η := by
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
  have hL : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, A →L[ℝ] A) ∞
      fun k : K ↦ LinearMap.toContinuousLinearMap (D.repA k) :=
    fun k ↦ contMDiffAt_clm_apply.2 fun η ↦ (hpt η).contMDiffAt
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

end LocalModelData

end SymplecticGeometry

end
