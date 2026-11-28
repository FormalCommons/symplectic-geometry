/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Basic

import SymplecticGeometry.Geometry.Manifold.ContMDiff.Dual

/-!
# The data of the Marle–Guillemin–Sternberg local model

Let `G` be a real Lie group with Lie algebra `𝔤` and `K` a compact closed subgroup of `G`, the
`H` of the local model `G ×_H (𝔪* × V)` of a Hamiltonian action near an orbit. The subgroup
carries a Lie group structure, modelled on a normed space `F`, for which it acts smoothly on `G`
by left multiplication: these are the instance arguments with which Tau Ceti's balanced product
`TauCeti.BalancedProduct K (Subgroup.RightTranslation K) Z` is a manifold, and the closed-subgroup
structure `TauCeti.Lie.EmbeddedLieSubgroupData.ofIsClosed` gives one.

`SymplecticGeometry.LocalModelData K V A` bundles the rest of the data:

* a covector `τ ∈ 𝔤*` fixed by the coadjoint action of `K`;
* the Lie algebra `𝔥` of `K`, as the image in `𝔤` of the differential at `1` of the inclusion;
* submodules `𝔪` and `𝔮` of `𝔤`, invariant under the adjoint action of `K`, with
  `𝔥 ⊕ 𝔪 = 𝔤_τ` and `𝔤_τ ⊕ 𝔮 = 𝔤`, where `𝔤_τ` is the coadjoint stabilizer
  `lieAnnihilator ℝ 𝔤 τ`, in the form of Tau Ceti's linear normal form;
* a finite-dimensional symplectic vector space `(V, σ)` with a smooth representation of `K` by
  linear symplectomorphisms, and its infinitesimal map `ρ : 𝔥 → sp(V, σ)`, which is the
  derivative at `1` of the orbit maps `k ↦ k • v`;
* a normed space `A` with a linear isomorphism `A ≃ 𝔪*`, which gives `𝔪*` a norm.

The splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` gives the extensions by zero `ι𝔥 : 𝔥* → 𝔤*` and
`ι𝔪 : 𝔪* → 𝔤*`, and with them the local model's moment map `μ_V : V → 𝔥*`, its covectors
`ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` and its two-form `-d⟨ν, θ⟩ + pr_V^* σ` on `G × (A × V)`, as
the case of the linear data of `SymplecticGeometry.localModelCovector` and
`SymplecticGeometry.localModelForm`.

## Main definitions

* `SymplecticGeometry.LocalModelData`: the data.
* `SymplecticGeometry.LocalModelData.ι𝔥`, `SymplecticGeometry.LocalModelData.ι𝔪`: the
  extensions by zero given by the splitting.
* `SymplecticGeometry.LocalModelData.momentMap`, `SymplecticGeometry.LocalModelData.covector`,
  `SymplecticGeometry.LocalModelData.form`: `μ_V`, `ν` and the two-form.
* `SymplecticGeometry.LocalModelData.sub𝔥`, `SymplecticGeometry.LocalModelData.sub𝔪`,
  `SymplecticGeometry.LocalModelData.sub𝔮`: `𝔥`, `𝔪` and `𝔮` as subrepresentations of the
  adjoint representation of `K` on `𝔤`.
* `SymplecticGeometry.LocalModelData.adjoint𝔥`, `SymplecticGeometry.LocalModelData.adjoint𝔪`,
  `SymplecticGeometry.LocalModelData.adjoint𝔮`, `SymplecticGeometry.LocalModelData.repV`: the
  representations of `K` on `𝔥`, `𝔪`, `𝔮` and `V`.
* `SymplecticGeometry.LocalModelData.ofBot`: the data for the trivial subgroup, with `𝔪 = 𝔤_τ`
  and the trivial representation.

## Main results

* `SymplecticGeometry.LocalModelData.mfderiv_rep_apply`: `ρ` is the derivative at `1` of the
  representation.
* `SymplecticGeometry.LocalModelData.isCompl_𝔥_sup`,
  `SymplecticGeometry.LocalModelData.isCompl_𝔪_sup`: `𝔤 = 𝔥 ⊕ (𝔪 ⊕ 𝔮)` and `𝔤 = 𝔪 ⊕ (𝔥 ⊕ 𝔮)`.
* `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔥`: `𝔥` is invariant under the
  adjoint action of `K`.
* `SymplecticGeometry.LocalModelData.contMDiff_covector_apply`: the components of `ν` are smooth.
* `SymplecticGeometry.LocalModelData.covectorCLM`,
  `SymplecticGeometry.LocalModelData.form_eq_inducedForm`: the covectors as continuous linear
  forms, and `D.form` as Tau Ceti's induced form of them.
* `SymplecticGeometry.LocalModelData.isClosed_form`,
  `SymplecticGeometry.LocalModelData.mpullback_mul_left_form`: the form is closed and invariant
  under `(g, η, v) ↦ (k * g, η, v)`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.Lie TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The data of the Marle–Guillemin–Sternberg local model `G ×_K (𝔪* × V)` for a compact closed
subgroup `K` of `G` with a Lie group structure on which it acts smoothly on `G`: a covector `τ`
fixed by `K`, the Lie algebra `𝔥` of `K` in `𝔤`, a `K`-invariant splitting
`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` with `𝔥 ⊕ 𝔪 = 𝔤_τ`, a smooth symplectic representation of `K` on `(V, σ)`
with its infinitesimal map `ρ : 𝔥 → sp(V, σ)`, and an isomorphism of `A` with `𝔪*`. -/
structure LocalModelData (K : Subgroup G) [IsClosed (K : Set G)] [CompactSpace K]
    [FiniteDimensional ℝ F] [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K]
    [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] where
  /-- The covector `τ ∈ 𝔤*` of the orbit. -/
  τ : Module.Dual ℝ (GroupLieAlgebra I G)
  /-- `τ` is fixed by the coadjoint action of `K`. -/
  coadjointRepresentation_τ : ∀ k : K, coadjointRepresentation ℝ I G k τ = τ
  /-- The Lie algebra `𝔥` of `K`, as a subspace of `𝔤`. -/
  𝔥 : Submodule ℝ (GroupLieAlgebra I G)
  /-- `𝔥` is the image of the differential at `1` of the inclusion `K → G`. -/
  range_groupLieAlgebraMap_subtype :
    LinearMap.range (K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I).toLinearMap = 𝔥
  /-- The complement `𝔪` of `𝔥` in `𝔤_τ`. -/
  𝔪 : Submodule ℝ (GroupLieAlgebra I G)
  /-- The complement `𝔮` of `𝔤_τ` in `𝔤`. -/
  𝔮 : Submodule ℝ (GroupLieAlgebra I G)
  disjoint_𝔥_𝔪 : Disjoint 𝔥 𝔪
  𝔥_sup_𝔪 : 𝔥 ⊔ 𝔪 = (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule
  isCompl_𝔮 : IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule 𝔮
  adjointRepresentation_mem_𝔪 : ∀ (k : K) {ξ}, ξ ∈ 𝔪 → adjointRepresentation ℝ I G k ξ ∈ 𝔪
  adjointRepresentation_mem_𝔮 : ∀ (k : K) {ξ}, ξ ∈ 𝔮 → adjointRepresentation ℝ I G k ξ ∈ 𝔮
  /-- The symplectic form `σ` on `V`. -/
  σ : SymplecticForm V
  /-- The representation of `K` on `V`. -/
  rep : K →* V ≃ₗ[ℝ] V
  isSymplectomorphism_rep : ∀ k, SymplecticForm.IsSymplectomorphism σ σ (rep k)
  contMDiff_rep : ContMDiff (𝓘(ℝ, F).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) ∞ fun p : K × V ↦ rep p.1 p.2
  /-- The infinitesimal map `𝔥 → sp(V, σ)` of the representation. -/
  ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm
  /-- `ρ` is the derivative at `1` of the orbit maps `k ↦ rep k v`. Use
  `LocalModelData.mfderiv_rep_apply`, which needs no proof of membership in `𝔥`. -/
  mfderiv_rep_apply_of_mem : ∀ (ξ : GroupLieAlgebra 𝓘(ℝ, F) K)
    (hξ : K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ ∈ 𝔥) (v : V),
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V) (fun k : K ↦ rep k v) 1 ξ =
      (ρ ⟨_, hξ⟩ : Module.End ℝ V) v
  /-- The identification of `A` with `𝔪*`. -/
  equivDual𝔪 : A ≃ₗ[ℝ] Module.Dual ℝ 𝔪

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- The differential at `1` of the inclusion `K → G` takes values in `𝔥`. -/
theorem groupLieAlgebraMap_subtype_mem_𝔥 (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) :
    K.subtype.groupLieAlgebraMap 𝓘(ℝ, F) I ξ ∈ D.𝔥 :=
  D.range_groupLieAlgebraMap_subtype ▸ LinearMap.mem_range_self _ ξ

/-- `ρ` is the derivative at `1` of the orbit maps `k ↦ rep k v`: the derivative in the
direction `ξ` is `ρ` of the image of `ξ` in `𝔥`, applied to `v`. -/
theorem mfderiv_rep_apply (ξ : GroupLieAlgebra 𝓘(ℝ, F) K) (v : V) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, V) (fun k : K ↦ D.rep k v) 1 ξ =
      (D.ρ ⟨_, D.groupLieAlgebraMap_subtype_mem_𝔥 ξ⟩ : Module.End ℝ V) v :=
  D.mfderiv_rep_apply_of_mem ξ _ v

theorem 𝔥_le_lieAnnihilator : D.𝔥 ≤ (lieAnnihilator ℝ (GroupLieAlgebra I G) D.τ).toSubmodule :=
  D.𝔥_sup_𝔪 ▸ le_sup_left

theorem 𝔪_le_lieAnnihilator : D.𝔪 ≤ (lieAnnihilator ℝ (GroupLieAlgebra I G) D.τ).toSubmodule :=
  D.𝔥_sup_𝔪 ▸ le_sup_right

/-- The splitting `𝔤 = 𝔥 ⊕ (𝔪 ⊕ 𝔮)`. -/
theorem isCompl_𝔥_sup : IsCompl D.𝔥 (D.𝔪 ⊔ D.𝔮) :=
  D.disjoint_𝔥_𝔪.isCompl_sup_right_of_isCompl_sup_left (D.𝔥_sup_𝔪 ▸ D.isCompl_𝔮)

/-- The splitting `𝔤 = 𝔪 ⊕ (𝔥 ⊕ 𝔮)`. -/
theorem isCompl_𝔪_sup : IsCompl D.𝔪 (D.𝔥 ⊔ D.𝔮) :=
  D.disjoint_𝔥_𝔪.symm.isCompl_sup_right_of_isCompl_sup_left
    (sup_comm D.𝔥 D.𝔪 ▸ D.𝔥_sup_𝔪 ▸ D.isCompl_𝔮)

/-! ### The action of `K` on the splitting -/

/-- The Lie algebra `𝔥` of `K` is invariant under the adjoint action of `K`. -/
theorem adjointRepresentation_mem_𝔥 (k : K) {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ D.𝔥) :
    adjointRepresentation ℝ I G k ξ ∈ D.𝔥 := by
  rw [← D.range_groupLieAlgebraMap_subtype] at hξ ⊢
  obtain ⟨ζ, rfl⟩ := hξ
  refine ⟨adjointContinuousLinearMap (I := 𝓘(ℝ, F)) k ζ, ?_⟩
  rw [ContinuousLinearMap.coe_coe, MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap,
    adjointRepresentation_apply, Subgroup.coe_subtype]

/-! ### The splitting as subrepresentations -/

-- The three definitions below are exposed so that other files see `D.sub𝔥.toSubmodule` as `D.𝔥`
-- by definition: the types of the API, such as `Module.Dual ℝ D.𝔥`, are stated with `D.𝔥`.

/-- The Lie algebra `𝔥` of `K`, as a subrepresentation of the adjoint representation of `K` on
`𝔤`. -/
@[expose]
def sub𝔥 : Subrepresentation ((adjointRepresentation ℝ I G).comp K.subtype) :=
  ⟨D.𝔥, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔥 k hξ⟩

/-- The complement `𝔪` of `𝔥` in `𝔤_τ`, as a subrepresentation of the adjoint representation of
`K` on `𝔤`. -/
@[expose]
def sub𝔪 : Subrepresentation ((adjointRepresentation ℝ I G).comp K.subtype) :=
  ⟨D.𝔪, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔪 k hξ⟩

/-- The complement `𝔮` of `𝔤_τ` in `𝔤`, as a subrepresentation of the adjoint representation of
`K` on `𝔤`. -/
@[expose]
def sub𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp K.subtype) :=
  ⟨D.𝔮, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔮 k hξ⟩

@[simp]
theorem toSubmodule_sub𝔥 : D.sub𝔥.toSubmodule = D.𝔥 :=
  (rfl)

@[simp]
theorem toSubmodule_sub𝔪 : D.sub𝔪.toSubmodule = D.𝔪 :=
  (rfl)

@[simp]
theorem toSubmodule_sub𝔮 : D.sub𝔮.toSubmodule = D.𝔮 :=
  (rfl)

@[simp]
theorem mem_sub𝔥 {ξ : GroupLieAlgebra I G} : ξ ∈ D.sub𝔥 ↔ ξ ∈ D.𝔥 :=
  Iff.rfl

@[simp]
theorem mem_sub𝔪 {ξ : GroupLieAlgebra I G} : ξ ∈ D.sub𝔪 ↔ ξ ∈ D.𝔪 :=
  Iff.rfl

@[simp]
theorem mem_sub𝔮 {ξ : GroupLieAlgebra I G} : ξ ∈ D.sub𝔮 ↔ ξ ∈ D.𝔮 :=
  Iff.rfl

/-- The adjoint representation of `K` on its Lie algebra `𝔥`. -/
def adjoint𝔥 : Representation ℝ K D.𝔥 :=
  D.sub𝔥.toRepresentation

theorem adjoint𝔥_def : D.adjoint𝔥 = D.sub𝔥.toRepresentation :=
  (rfl)

/-- The adjoint representation of `K` on `𝔪`. -/
def adjoint𝔪 : Representation ℝ K D.𝔪 :=
  D.sub𝔪.toRepresentation

theorem adjoint𝔪_def : D.adjoint𝔪 = D.sub𝔪.toRepresentation :=
  (rfl)

/-- The adjoint representation of `K` on `𝔮`. -/
def adjoint𝔮 : Representation ℝ K D.𝔮 :=
  D.sub𝔮.toRepresentation

theorem adjoint𝔮_def : D.adjoint𝔮 = D.sub𝔮.toRepresentation :=
  (rfl)

@[simp]
theorem coe_adjoint𝔥_apply (k : K) (h : D.𝔥) :
    (D.adjoint𝔥 k h : GroupLieAlgebra I G) = adjointRepresentation ℝ I G k h :=
  (rfl)

@[simp]
theorem coe_adjoint𝔪_apply (k : K) (m : D.𝔪) :
    (D.adjoint𝔪 k m : GroupLieAlgebra I G) = adjointRepresentation ℝ I G k m :=
  (rfl)

@[simp]
theorem coe_adjoint𝔮_apply (k : K) (q : D.𝔮) :
    (D.adjoint𝔮 k q : GroupLieAlgebra I G) = adjointRepresentation ℝ I G k q :=
  (rfl)

/-- The representation `rep` of `K` on `V`, as a `Representation`. -/
def repV : Representation ℝ K V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp D.rep

@[simp]
theorem repV_apply (k : K) (v : V) : D.repV k v = D.rep k v :=
  (rfl)

/-! ### The extensions by zero -/

/-- The extension by zero `𝔥* → 𝔤*` given by the splitting: `ι𝔥 f` is `f` on `𝔥` and vanishes on
`𝔪 ⊕ 𝔮`. -/
def ι𝔥 : Module.Dual ℝ D.𝔥 →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G) :=
  (Submodule.projectionOnto _ _ D.isCompl_𝔥_sup).dualMap

theorem ι𝔥_def :
    D.ι𝔥 = (Submodule.projectionOnto _ _ D.isCompl_𝔥_sup).dualMap :=
  (rfl)

@[simp]
theorem ι𝔥_apply_coe (f : Module.Dual ℝ D.𝔥) (ξ : D.𝔥) : D.ι𝔥 f ξ = f ξ := by
  rw [ι𝔥_def, LinearMap.dualMap_apply, Submodule.projectionOnto_apply_left]

theorem ι𝔥_apply_of_mem_sup (f : Module.Dual ℝ D.𝔥) {ξ} (hξ : ξ ∈ D.𝔪 ⊔ D.𝔮) :
    D.ι𝔥 f ξ = 0 := by
  rw [ι𝔥_def, LinearMap.dualMap_apply,
    Submodule.projectionOnto_apply_of_mem_right _ hξ, map_zero]

/-- The extension by zero `A ≃ 𝔪* → 𝔤*` given by the splitting: `ι𝔪 η` is the covector
`equivDual𝔪 η` on `𝔪` and vanishes on `𝔥 ⊕ 𝔮`. -/
def ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G) :=
  (Submodule.projectionOnto _ _ D.isCompl_𝔪_sup).dualMap ∘ₗ D.equivDual𝔪.toLinearMap

theorem ι𝔪_def :
    D.ι𝔪 = (Submodule.projectionOnto _ _ D.isCompl_𝔪_sup).dualMap ∘ₗ
      D.equivDual𝔪.toLinearMap :=
  (rfl)

/-- `ι𝔪 η` evaluates `equivDual𝔪 η` on the `𝔪`-component of a vector, taken along `𝔥 ⊕ 𝔮`. -/
theorem ι𝔪_apply (η : A) (ξ : GroupLieAlgebra I G) :
    D.ι𝔪 η ξ = D.equivDual𝔪 η (Submodule.projectionOnto _ _ D.isCompl_𝔪_sup ξ) := by
  rw [ι𝔪_def, LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe]

@[simp]
theorem ι𝔪_apply_coe (η : A) (ξ : D.𝔪) : D.ι𝔪 η ξ = D.equivDual𝔪 η ξ := by
  rw [ι𝔪_apply, Submodule.projectionOnto_apply_left]

theorem ι𝔪_apply_of_mem_sup (η : A) {ξ} (hξ : ξ ∈ D.𝔥 ⊔ D.𝔮) : D.ι𝔪 η ξ = 0 := by
  rw [ι𝔪_apply, Submodule.projectionOnto_apply_of_mem_right _ hξ, map_zero]

/-! ### The moment map, the covectors and the two-form -/

/-- The moment map `μ_V : V → 𝔥*` of the infinitesimal action `ρ` of `𝔥` on `(V, σ)`,
`μ_V v ξ = ½ σ (ρ ξ v, v)`. -/
def momentMap (v : V) : Module.Dual ℝ D.𝔥 :=
  D.σ.linearMomentMapComp D.ρ v

theorem momentMap_def (v : V) : D.momentMap v = D.σ.linearMomentMapComp D.ρ v :=
  (rfl)

@[simp]
theorem momentMap_apply (v : V) (ξ : D.𝔥) :
    D.momentMap v ξ = D.σ ((D.ρ ξ : Module.End ℝ V) v) v / 2 := by
  rw [momentMap_def, SymplecticForm.linearMomentMapComp_apply]

/-- The moment map `μ_V` vanishes at the origin of `V`. -/
@[simp]
theorem momentMap_zero : D.momentMap 0 = 0 := by
  rw [momentMap_def, SymplecticForm.linearMomentMapComp_zero]

/-- The covectors `ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` of the local model, on `A × V`. -/
def covector (p : A × V) : Module.Dual ℝ (GroupLieAlgebra I G) :=
  localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 p

theorem covector_def (p : A × V) :
    D.covector p = localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 p :=
  (rfl)

@[simp]
theorem covector_apply (η : A) (v : V) (ξ : GroupLieAlgebra I G) :
    D.covector (η, v) ξ = D.τ ξ + D.ι𝔪 η ξ + D.ι𝔥 (D.momentMap v) ξ := by
  rw [covector_def, localModelCovector_apply, momentMap_def]

/-- At the origin of `A × V`, the covector of the local model is `τ`. -/
@[simp]
theorem covector_zero : D.covector 0 = D.τ := by
  ext ξ
  rw [Prod.zero_eq_mk, covector_apply, map_zero, momentMap_zero, map_zero,
    LinearMap.zero_apply, add_zero, add_zero]

/-- The components `p ↦ ν p ξ` of the covectors of the local model are smooth on `A × V`. -/
theorem contMDiff_covector_apply (ξ : GroupLieAlgebra I G) :
    ContMDiff 𝓘(ℝ, A × V) 𝓘(ℝ) ∞ fun p : A × V ↦ D.covector p ξ :=
  contMDiff_localModelCovector_apply D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 ξ

/-- The two-form `-d⟨ν, θ⟩ + pr_V^* σ` of the local model on `G × (A × V)`, where `ν` are its
covectors and `θ` is the left-invariant Maurer–Cartan form of `G`. -/
def form : SmoothForm (I.prod 𝓘(ℝ, A × V)) (G × (A × V)) ℝ 2 :=
  localModelForm D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥

theorem form_def : D.form = localModelForm D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥 :=
  (rfl)

/-- The covectors `ν` of the local model, read as continuous linear forms on `𝔤`, the form in which
Tau Ceti's `TauCeti.CotangentBundle.inducedForm` takes them. -/
def covectorCLM (p : A × V) : E →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] E →L[ℝ] ℝ) (D.covector p)

theorem covectorCLM_def (p : A × V) :
    D.covectorCLM p =
      (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] E →L[ℝ] ℝ) (D.covector p) :=
  (rfl)

@[simp]
theorem covectorCLM_apply (p : A × V) (ξ : GroupLieAlgebra I G) :
    D.covectorCLM p ξ = D.covector p ξ :=
  (rfl)

@[simp]
theorem coe_covectorCLM (p : A × V) : (D.covectorCLM p : E →ₗ[ℝ] ℝ) = D.covector p :=
  (rfl)

/-- The covectors of the local model, read as continuous linear forms on `𝔤`, form a smooth map
on `A × V`. -/
theorem contMDiff_covectorCLM : ContMDiff 𝓘(ℝ, A × V) 𝓘(ℝ, E →L[ℝ] ℝ) ∞ D.covectorCLM :=
  contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) D.contMDiff_covector_apply

/-- The two-form of the local model is Tau Ceti's induced form
`TauCeti.CotangentBundle.inducedForm` of the covectors `ν`, read as continuous linear forms, and of
the pullback of `σ` along `pr_V : A × V → V`. -/
theorem form_eq_inducedForm :
    D.form = inducedForm I G (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff D.σ.constSmooth)
      D.contMDiff_covectorCLM := by
  rw [form_def, localModelForm_def]
  -- `D.covector` is `localModelCovector D.σ D.ρ D.τ D.ι𝔪 D.ι𝔥` by definition.
  rfl

/-- The two-form of the local model on `G × (A × V)` is closed. -/
theorem isClosed_form : D.form.IsClosed := by
  rw [form_def]
  exact isClosed_localModelForm _ _ _ _ _

/-- The two-form of the local model on `G × (A × V)` is invariant under left translation
`(g, η, v) ↦ (k * g, η, v)` of the factor `G`. -/
@[simp]
theorem mpullback_mul_left_form (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id) D.form =
      D.form := by
  rw [form_def, mpullback_mul_left_localModelForm]

/-- On the slice `G × {p}`, the two-form of the local model is the left-invariant Kirillov form
of the covector `ν p`. -/
@[simp]
theorem mpullback_prodMk_form (p : A × V) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const) D.form =
      (D.covector p).leftInvariantKirillovForm := by
  rw [form_def, mpullback_prodMk_localModelForm, covector_def]

end LocalModelData

/-! ### The data for the trivial subgroup -/

section Bot

variable [IsClosed ((⊥ : Subgroup G) : Set G)] [FiniteDimensional ℝ F]
  [ChartedSpace F (⊥ : Subgroup G)] [LieGroup 𝓘(ℝ, F) ∞ (⊥ : Subgroup G)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ (⊥ : Subgroup G) G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The data of the local model for the trivial subgroup `⊥` of `G`, any covector `τ` and any
symplectic vector space `(V, σ)`: `𝔥 = 0`, `𝔪 = 𝔤_τ`, `𝔮` a complement of `𝔤_τ`, the trivial
representation on `V`, and `A = ℝ^(dim 𝔪)`. -/
def LocalModelData.ofBot (τ : Module.Dual ℝ (GroupLieAlgebra I G)) (σ : SymplecticForm V) :
    LocalModelData (I := I) (⊥ : Subgroup G) (F := F) V
      (Fin (Module.finrank ℝ (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule) → ℝ) where
  τ := τ
  coadjointRepresentation_τ k := by
    rw [Subsingleton.elim k 1, OneMemClass.coe_one, map_one, one_apply_eq_self]
  𝔥 := ⊥
  range_groupLieAlgebraMap_subtype := by
    have h : ((⊥ : Subgroup G).subtype : (⊥ : Subgroup G) → G) = fun _ ↦ 1 :=
      funext fun k ↦ Subgroup.mem_bot.1 k.property
    rw [LinearMap.range_eq_bot]
    ext ξ
    rw [ContinuousLinearMap.coe_coe, MonoidHom.groupLieAlgebraMap_apply, h, mfderiv_const,
      zero_apply, LinearMap.zero_apply]
  𝔪 := (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule
  𝔮 := (Submodule.exists_isCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule).choose
  disjoint_𝔥_𝔪 := disjoint_bot_left
  𝔥_sup_𝔪 := bot_sup_eq _
  isCompl_𝔮 :=
    (Submodule.exists_isCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) τ).toSubmodule).choose_spec
  adjointRepresentation_mem_𝔪 k ξ hξ := by
    rwa [Subsingleton.elim k 1, OneMemClass.coe_one, map_one, one_apply_eq_self]
  adjointRepresentation_mem_𝔮 k ξ hξ := by
    rwa [Subsingleton.elim k 1, OneMemClass.coe_one, map_one, one_apply_eq_self]
  σ := σ
  rep := 1
  isSymplectomorphism_rep k := by
    rw [MonoidHom.one_apply, LinearEquiv.one_eq_refl]
    exact SymplecticForm.IsSymplectomorphism.refl σ
  contMDiff_rep := by
    simp only [MonoidHom.one_apply, one_apply_eq_self]
    exact contMDiff_snd
  ρ := 0
  mfderiv_rep_apply_of_mem ξ hξ v := by
    have h : (fun k : (⊥ : Subgroup G) ↦ (1 : (⊥ : Subgroup G) →* V ≃ₗ[ℝ] V) k v) =
        fun _ ↦ v :=
      funext fun _ ↦ by rw [MonoidHom.one_apply, one_apply_eq_self]
    rw [h, mfderiv_const]
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
    exact zero_apply (F := F →L[ℝ] V) ξ
  equivDual𝔪 := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq])

end Bot

end SymplecticGeometry
