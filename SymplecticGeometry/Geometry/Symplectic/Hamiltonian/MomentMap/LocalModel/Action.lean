/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Lie.Adjoint.Splitting
public import SymplecticGeometry.Geometry.Lie.FundamentalVectorField
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data

/-!
# The action of `K` on the splitting, on `𝔪*` and on `V` in the local model

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (𝔪* × V)`, with its `Ad_K`-invariant splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and the
identification `A ≃ 𝔪*`. This file gives the linear algebra of the action of `K` on the fibre
`𝔪* × V` of the local model: the sums `𝔪 ⊕ 𝔮` and `𝔥 ⊕ 𝔮` are invariant under `Ad_K`, so the
extensions by zero `ι𝔥 : 𝔥* → 𝔤*` and `ι𝔪 : 𝔪* → 𝔤*` intertwine the duals of the adjoint
representations of `K` on `𝔥` and `𝔪` with the coadjoint representation of `K` on `𝔤*`.
The representation of `K` on `A` is the dual of the adjoint representation on `𝔪`, transported
to `A` by `D.equivDual𝔪`. Finally, the infinitesimal map `ρ : 𝔥 → sp(V, σ)` and the moment map
`μ_V : V → 𝔥*` are equivariant for the representation `rep` of `K` on `V`.

The invariance of the sums is that of a sup of subrepresentations (Mathlib's lattice of
`Subrepresentation`). The equivariance of the extensions by zero is the case of the splitting of
`TauCeti.Lie.dualMap_projectionOnto_dual`, which follows the route described in the module
docstring of Tau Ceti's `TauCeti/Geometry/Lie/Adjoint/Splitting.lean`. The equivariance of `ρ`
is that of the orbit derivatives of the linear representation `rep` of `K` on `V`, the
library's `TauCeti.mfderiv_linearEquiv_apply_adjointContinuousLinearMap`, read through
`D.mfderiv_rep_apply` and the naturality `MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap`
of the adjoint action for the inclusion `K → G`. That of `μ_V` follows from it, since each
`rep k` preserves `σ`.

## Main definitions

* `SymplecticGeometry.LocalModelData.repA`: the representation of `K` on `A ≃ 𝔪*`, the dual of
  `SymplecticGeometry.LocalModelData.adjoint𝔪`.

## Main results

* `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔪_sup`,
  `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔥_sup`: `𝔪 ⊕ 𝔮` and `𝔥 ⊕ 𝔮` are
  invariant under the adjoint action of `K`.
* `SymplecticGeometry.LocalModelData.ι𝔥_adjoint𝔥_dual`,
  `SymplecticGeometry.LocalModelData.ι𝔪_symm_adjoint𝔪_dual`: `ι𝔥` and `ι𝔪` are equivariant.
* `SymplecticGeometry.LocalModelData.ι𝔪_repA`: `ι𝔪 (repA k η) = Ad*_k (ι𝔪 η)`.
* `SymplecticGeometry.LocalModelData.ρ_adjoint𝔥`: `ρ (Ad_k ξ) = rep k ∘ ρ ξ ∘ rep k⁻¹`.
* `SymplecticGeometry.LocalModelData.momentMap_rep`,
  `SymplecticGeometry.LocalModelData.ι𝔥_momentMap_rep`: `μ_V` is equivariant, and
  `ι𝔥 (μ_V (rep k v)) = Ad*_k (ι𝔥 (μ_V v))`.

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
  ((⟨D.𝔪, fun k _ h ↦ D.adjointRepresentation_mem_𝔪 k h⟩ :
      Subrepresentation ((adjointRepresentation ℝ I G).comp K.subtype)) ⊔
    ⟨D.𝔮, fun k _ h ↦ D.adjointRepresentation_mem_𝔮 k h⟩).apply_mem_toSubmodule k hξ

/-- The sum `𝔥 ⊕ 𝔮` is invariant under the adjoint action of `K`. -/
theorem adjointRepresentation_mem_𝔥_sup (k : K) {ξ : GroupLieAlgebra I G}
    (hξ : ξ ∈ D.𝔥 ⊔ D.𝔮) : adjointRepresentation ℝ I G k ξ ∈ D.𝔥 ⊔ D.𝔮 :=
  ((⟨D.𝔥, fun k _ h ↦ D.adjointRepresentation_mem_𝔥 k h⟩ :
      Subrepresentation ((adjointRepresentation ℝ I G).comp K.subtype)) ⊔
    ⟨D.𝔮, fun k _ h ↦ D.adjointRepresentation_mem_𝔮 k h⟩).apply_mem_toSubmodule k hξ

/-! ### Equivariance of the extensions by zero -/

/-- The extension by zero `ι𝔥 : 𝔥* → 𝔤*` is equivariant: it takes the dual of the adjoint
representation of `K` on `𝔥` to the coadjoint representation, `ι𝔥 (f ∘ Ad_{k⁻¹}) = Ad*_k (ι𝔥 f)`.
-/
theorem ι𝔥_adjoint𝔥_dual (k : K) (f : Module.Dual ℝ D.𝔥) :
    D.ι𝔥 (D.adjoint𝔥.dual k f) = coadjointRepresentation ℝ I G k (D.ι𝔥 f) := by
  have h := dualMap_projectionOnto_dual
    (S := ⟨D.𝔥, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔥 k hξ⟩)
    (T := ⟨D.𝔪 ⊔ D.𝔮, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔪_sup k hξ⟩)
    (Subrepresentation.isCompl_toSubmodule.1 D.isCompl_𝔥_sup) k f
  rw [← adjoint𝔥_def] at h
  rw [ι𝔥_def]
  -- `h` is about the subrepresentation with carrier `D.𝔥`, whose `toSubmodule` reduces to it.
  exact h

/-- The extension by zero `𝔪* → 𝔤*` is equivariant: it takes the dual of the adjoint
representation of `K` on `𝔪` to the coadjoint representation. Here `𝔪*` is read in `A` through
`D.equivDual𝔪`. -/
theorem ι𝔪_symm_adjoint𝔪_dual (k : K) (f : Module.Dual ℝ D.𝔪) :
    D.ι𝔪 (D.equivDual𝔪.symm (D.adjoint𝔪.dual k f)) =
      coadjointRepresentation ℝ I G k (D.ι𝔪 (D.equivDual𝔪.symm f)) := by
  have h := dualMap_projectionOnto_dual
    (S := ⟨D.𝔪, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔪 k hξ⟩)
    (T := ⟨D.𝔥 ⊔ D.𝔮, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔥_sup k hξ⟩)
    (Subrepresentation.isCompl_toSubmodule.1 D.isCompl_𝔪_sup) k f
  rw [← adjoint𝔪_def] at h
  rw [ι𝔪_def, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  -- `h` is about the subrepresentation with carrier `D.𝔪`, whose `toSubmodule` reduces to it.
  exact h

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

end LocalModelData

end SymplecticGeometry

end
