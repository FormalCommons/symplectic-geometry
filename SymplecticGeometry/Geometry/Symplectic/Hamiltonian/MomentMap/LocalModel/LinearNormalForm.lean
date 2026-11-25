/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data

/-!
# The two-form of the local model at `(1, 0, 0)` and the linear normal form

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `G ×_K (𝔪* × V)`, with its splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` and the identification
`A ≃ 𝔪*`. This file computes the two-form `D.form` of the local model on `G × (A × V)` at the
point `(1, 0, 0)`, whose tangent space is `𝔤 × A × V`, and compares it with the linear normal form
model `(𝔪 × 𝔪*) × (𝔮 × V)` of Tau Ceti's `MomentMap/LinearNormalForm.lean`, whose form is

`Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + τ ⁅ζ, ζ'⁆ + σ(v, v')`,

the sum of `TauCeti.cotangentSymplecticForm`, the Kirillov form
`Module.Dual.kirillovSymplecticForm` of `τ` on `𝔮` and `σ`.

At `(1, 0, 0)` the covector of the local model is `τ`, and the derivative of `μ_V` vanishes, so
the form pairs `(ξᵢ, aᵢ, bᵢ)` to `τ ⁅ξ₁, ξ₂⁆ - ι𝔪 a₁ ξ₂ + ι𝔪 a₂ ξ₁ + σ (b₁, b₂)`. Since
`𝔥 ⊕ 𝔪 = 𝔤_τ`, only the components in `𝔪` and `𝔮` contribute, and with the same signs as the
model: no change of sign is needed.

## Main definitions

* `SymplecticGeometry.LocalModelData.linearModelMap`: the injective linear map
  `(𝔪 × 𝔪*) × (𝔮 × V) → 𝔤 × A × V`, `((m, f), (q, b)) ↦ (m + q, f, b)`, onto the complement
  `(𝔪 ⊕ 𝔮) × A × V` of `𝔥 × 0`.
* `SymplecticGeometry.LocalModelData.adjoint𝔪`, `SymplecticGeometry.LocalModelData.adjoint𝔮`,
  `SymplecticGeometry.LocalModelData.repV`: the representations of `K` on `𝔪`, `𝔮` and `V`, and
  `SymplecticGeometry.LocalModelData.linearModelRepresentation`, the representation of `K` on the
  model, by the adjoint action on `𝔪` and `𝔮`, its dual on `𝔪*` and `rep` on `V`.

## Main results

* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq`: the form
  at `(1, 0, 0)` on tangent vectors `(ξᵢ, aᵢ, bᵢ)`.
* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_linearModelMap`: through
  `linearModelMap`, the form at `(1, 0, 0)` is the form of the linear normal form model.
* `SymplecticGeometry.LocalModelData.isCompl_range_linearModelMap`: the range of
  `linearModelMap` is a complement of `𝔥 × 0`.
* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_eq_zero_iff`: the kernel of the form at
  `(1, 0, 0)` is the space `𝔥 × 0` of the directions `(ξ, 0, 0)` with `ξ ∈ 𝔥`.
* `SymplecticGeometry.LocalModelData.fst_linearModelMap_linearModelRepresentation`,
  `SymplecticGeometry.LocalModelData.ι𝔪_snd_fst_linearModelMap_linearModelRepresentation`,
  `SymplecticGeometry.LocalModelData.snd_snd_linearModelMap_linearModelRepresentation`:
  `linearModelMap` intertwines the action of `K` on the model with the action
  `(ξ, a, b) ↦ (Ad_k ξ, Ad*_k a, k • b)` of `K` on `𝔤 × A × V`, the coadjoint action on `A` being
  read in `𝔤*` through `ι𝔪`. This is the action of `K` on the tangent space at `(1, 0, 0)` by the
  differentials of `(g, η, v) ↦ (k g k⁻¹, Ad*_k η, k • v)`, which fix that point.
* `SymplecticGeometry.LocalModelData.adjointRepresentation_mem_𝔥`: `𝔥` is invariant under the
  adjoint action of `K`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open TauCeti TauCeti.Lie TauCeti.Manifold
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

/-! ### The form at `(1, 0, 0)` -/

/-- An element `ξ` of `𝔤` lies in the coadjoint stabilizer `𝔤_τ` exactly when `τ ⁅ξ, ζ⁆ = 0`
for every `ζ`. -/
theorem mem_lieAnnihilator_τ_iff {ξ : GroupLieAlgebra I G} :
    ξ ∈ (lieAnnihilator ℝ (GroupLieAlgebra I G) D.τ).toSubmodule ↔ ∀ ζ, D.τ ⁅ξ, ζ⁆ = 0 := by
  rw [← D.τ.ker_kirillovForm, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [Module.Dual.kirillovForm_apply, LinearMap.zero_apply]

/-- **The form of the local model at `(1, 0, 0)`.** It pairs the tangent vectors `(ξᵢ, aᵢ, bᵢ)` to
`τ ⁅ξ₁, ξ₂⁆ - ι𝔪 a₁ ξ₂ + ι𝔪 a₂ ξ₁ + σ (b₁, b₂)`. -/
theorem eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq
    {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))}
    {ξ₁ ξ₂ : GroupLieAlgebra I G} {a₁ a₂ : A} {b₁ b₂ : V}
    (hu₁ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₁ = (ξ₁, (a₁, b₁)))
    (hu₂ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₂ = (ξ₂, (a₂, b₂))) :
    D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u₁ u₂ =
      D.τ ⁅ξ₁, ξ₂⁆ - D.ι𝔪 a₁ ξ₂ + D.ι𝔪 a₂ ξ₁ + D.σ b₁ b₂ := by
  rw [form_def, eval₂_localModelForm_one_of_tangentSpaceProdEquiv_eq _ _ _ _ _ hu₁ hu₂,
    ← covector_def, covector_apply]
  simp [momentMap_def]

/-! ### The linear normal form model -/

/-- The linear map `(𝔪 × 𝔪*) × (𝔮 × V) → 𝔤 × A × V`, `((m, f), (q, b)) ↦ (m + q, f, b)`, from the
linear normal form model to the tangent space of `G × (A × V)` at `(1, 0, 0)`, where `f ∈ 𝔪*` is
read in `A` through `equivDual𝔪`. -/
def linearModelMap :
    (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V) →ₗ[ℝ] GroupLieAlgebra I G × (A × V) :=
  ((D.𝔪.subtype ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.fst ℝ _ _) +
      (D.𝔮.subtype ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _)).prod
    ((D.equivDual𝔪.symm.toLinearMap ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ LinearMap.fst ℝ _ _).prod
      (LinearMap.snd ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _))

@[simp]
theorem linearModelMap_apply (m : D.𝔪) (f : Module.Dual ℝ D.𝔪) (q : D.𝔮) (b : V) :
    D.linearModelMap ((m, f), (q, b)) = ((m : GroupLieAlgebra I G) + q, (D.equivDual𝔪.symm f, b)) :=
  (rfl)

/-- `linearModelMap` is injective, since `𝔪` and `𝔮` are independent. -/
theorem injective_linearModelMap : Function.Injective D.linearModelMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨⟨m, f⟩, q, b⟩ h
  simp only [LinearMap.mem_ker, linearModelMap_apply, Prod.mk_eq_zero,
    LinearEquiv.map_eq_zero_iff] at h
  obtain ⟨hmq, rfl, rfl⟩ := h
  have hq : (q : GroupLieAlgebra I G) = 0 := by
    refine Submodule.disjoint_def.1 (D.isCompl_𝔪_sup.disjoint.mono_right le_sup_right) _ ?_
      q.property
    rw [eq_neg_of_add_eq_zero_right hmq]
    exact neg_mem m.property
  have hm : (m : GroupLieAlgebra I G) = 0 := by rwa [hq, add_zero] at hmq
  simp [Submodule.coe_eq_zero.1 hm, Submodule.coe_eq_zero.1 hq]

/-- The range of `linearModelMap` is `(𝔪 ⊕ 𝔮) × A × V`. -/
theorem range_linearModelMap :
    LinearMap.range D.linearModelMap = (D.𝔪 ⊔ D.𝔮).prod ⊤ := by
  refine le_antisymm ?_ fun ⟨ξ, a, b⟩ ⟨hξ, _⟩ ↦ ?_
  · rintro _ ⟨⟨⟨m, f⟩, q, b⟩, rfl⟩
    exact ⟨Submodule.add_mem_sup m.property q.property, trivial⟩
  obtain ⟨m, hm, q, hq, rfl⟩ := Submodule.mem_sup.1 hξ
  exact ⟨((⟨m, hm⟩, D.equivDual𝔪 a), (⟨q, hq⟩, b)), by simp⟩

/-- The range of `linearModelMap` is a complement of the space `𝔥 × 0` of the directions
`(ξ, 0, 0)` with `ξ ∈ 𝔥`. -/
theorem isCompl_range_linearModelMap :
    IsCompl (LinearMap.range D.linearModelMap) (D.𝔥.prod ⊥) := by
  rw [range_linearModelMap]
  have h := D.isCompl_𝔥_sup.symm
  constructor
  · rw [Submodule.disjoint_def]
    rintro ⟨ξ, p⟩ ⟨hξ, -⟩ ⟨hξ', hp⟩
    exact Prod.ext (Submodule.disjoint_def.1 h.disjoint _ hξ hξ') hp
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨ξ, p⟩ -
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top (x := ξ))
    exact Submodule.mem_sup.2 ⟨(y, p), ⟨hy, trivial⟩, (z, 0), ⟨hz, rfl⟩, by simp⟩

/-- **The form of the local model at `(1, 0, 0)` is the linear normal form.** On tangent vectors
`linearModelMap xᵢ`, the form at `(1, 0, 0)` is the form of the linear normal form model
`(𝔪 × 𝔪*) × (𝔮 × V)`: the sum of the canonical form of `𝔪 × 𝔪*`, the Kirillov form of `τ` on
`𝔮` and `σ`. -/
theorem eval₂_form_one_zero_linearModelMap
    {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))}
    {x₁ x₂ : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)}
    (hu₁ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₁ = D.linearModelMap x₁)
    (hu₂ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₂ = D.linearModelMap x₂) :
    D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u₁ u₂ =
      (cotangentSymplecticForm.prod ((D.τ.kirillovSymplecticForm D.isCompl_𝔮).prod D.σ)) x₁ x₂ := by
  obtain ⟨⟨m₁, f₁⟩, q₁, b₁⟩ := x₁
  obtain ⟨⟨m₂, f₂⟩, q₂, b₂⟩ := x₂
  rw [linearModelMap_apply] at hu₁ hu₂
  rw [D.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq hu₁ hu₂]
  have h𝔮 (a : A) (q : D.𝔮) : D.ι𝔪 a q = 0 :=
    D.ι𝔪_apply_of_mem_sup a (Submodule.mem_sup_right q.property)
  have h₁ := D.mem_lieAnnihilator_τ_iff.1 (D.𝔪_le_lieAnnihilator m₁.property)
  have h₂ (ξ : GroupLieAlgebra I G) : D.τ ⁅ξ, (m₂ : GroupLieAlgebra I G)⁆ = 0 := by
    rw [← lie_skew, map_neg, D.mem_lieAnnihilator_τ_iff.1 (D.𝔪_le_lieAnnihilator m₂.property),
      neg_zero]
  simp only [lie_add, add_lie, map_add, h₁, h₂, ι𝔪_apply_coe, h𝔮, LinearEquiv.apply_symm_apply,
    SymplecticForm.prod_apply, cotangentSymplecticForm_apply,
    Module.Dual.kirillovSymplecticForm_apply]
  ring

/-- **The kernel of the form of the local model at `(1, 0, 0)`.** A tangent vector at `(1, 0, 0)`
pairs to zero with every tangent vector exactly when it is `(ξ, 0, 0)` for some `ξ ∈ 𝔥`. -/
theorem eval₂_form_one_zero_eq_zero_iff
    (u : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))) :
    (∀ u', D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u u' = 0) ↔
      tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u ∈ D.𝔥.prod ⊥ := by
  set e := tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))
  rcases hu : e u with ⟨ξ, a, b⟩
  have hval (u' : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))) :
      D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u u' =
        D.τ ⁅ξ, (e u').1⁆ - D.ι𝔪 a (e u').1 + D.ι𝔪 (e u').2.1 ξ + D.σ b (e u').2.2 :=
    D.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq hu rfl
  simp only [hval, Submodule.mem_prod]
  constructor
  · intro h
    have h' (ξ' : GroupLieAlgebra I G) (a' : A) (b' : V) :
        D.τ ⁅ξ, ξ'⁆ - D.ι𝔪 a ξ' + D.ι𝔪 a' ξ + D.σ b b' = 0 := by
      simpa using h (e.symm (ξ', (a', b')))
    -- `σ` is nondegenerate, so `b = 0`.
    have hb : b = 0 := D.σ.nondegenerate.1 b fun b' ↦ by
      have h0 := h' 0 0 b'
      have hl : ⁅ξ, (0 : GroupLieAlgebra I G)⁆ = 0 := lie_zero ξ
      rw [hl] at h0
      simpa using h0
    -- `ι𝔪 a' ξ = 0` for every `a'`, so the component of `ξ` in `𝔪` vanishes.
    obtain ⟨m, hm, r, hr, rfl⟩ :=
      Submodule.mem_sup.1 (D.isCompl_𝔪_sup.sup_eq_top ▸ Submodule.mem_top (x := ξ))
    have hm0 : m = 0 := by
      have := (Module.forall_dual_apply_eq_zero_iff ℝ (⟨m, hm⟩ : D.𝔪)).1 fun f ↦ by
        have h0 := h' 0 (D.equivDual𝔪.symm f) 0
        rw [map_add, D.ι𝔪_apply_of_mem_sup _ hr] at h0
        rw [← LinearEquiv.apply_symm_apply D.equivDual𝔪 f, ← ι𝔪_apply_coe]
        simpa using h0
      exact congrArg Subtype.val this
    subst hm0
    rw [zero_add] at h' ⊢
    -- `τ ⁅r, m'⁆ = 0` for `m' ∈ 𝔪`, so `ι𝔪 a` vanishes on `𝔪`, and `a = 0`.
    have ha : a = 0 := by
      refine D.equivDual𝔪.map_eq_zero_iff.1 (LinearMap.ext fun m' ↦ ?_)
      have h0 := h' m' 0 0
      have hτ : D.τ ⁅r, (m' : GroupLieAlgebra I G)⁆ = 0 := by
        rw [← lie_skew, map_neg,
          D.mem_lieAnnihilator_τ_iff.1 (D.𝔪_le_lieAnnihilator m'.property), neg_zero]
      simp only [hτ, map_zero, LinearMap.zero_apply, add_zero, zero_sub, neg_eq_zero,
        ι𝔪_apply_coe, hb] at h0
      simpa using h0
    subst ha
    -- `τ ⁅r, ·⁆ = 0`, so `r ∈ 𝔤_τ = 𝔥 ⊕ 𝔪`, and `r ∈ 𝔥 ⊕ 𝔮` gives `r ∈ 𝔥`.
    have hrτ : r ∈ D.𝔥 ⊔ D.𝔪 := D.𝔥_sup_𝔪 ▸ D.mem_lieAnnihilator_τ_iff.2 fun ξ' ↦ by
      simpa [hb] using h' ξ' 0 0
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hrτ
    have hz0 : z = 0 := Submodule.disjoint_def.1 D.isCompl_𝔪_sup.disjoint _ hz (by
      simpa using sub_mem hr (Submodule.mem_sup_left hy))
    exact ⟨by simpa [hz0] using hy, by rw [hb]; exact zero_mem _⟩
  · rintro ⟨hξ, hab⟩ u'
    obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 hab
    rw [D.mem_lieAnnihilator_τ_iff.1 (D.𝔥_le_lieAnnihilator hξ),
      D.ι𝔪_apply_of_mem_sup _ (Submodule.mem_sup_left hξ)]
    simp

/-! ### The action of `K` -/

/-- The Lie algebra `𝔥` of `K` is invariant under the adjoint action of `K`. -/
theorem adjointRepresentation_mem_𝔥 (k : K) {ξ : GroupLieAlgebra I G} (hξ : ξ ∈ D.𝔥) :
    adjointRepresentation ℝ I G k ξ ∈ D.𝔥 := by
  rw [← D.range_groupLieAlgebraMap_subtype] at hξ ⊢
  obtain ⟨ζ, rfl⟩ := hξ
  refine ⟨adjointContinuousLinearMap (I := 𝓘(ℝ, F)) k ζ, ?_⟩
  rw [ContinuousLinearMap.coe_coe, MonoidHom.groupLieAlgebraMap_adjointContinuousLinearMap,
    adjointRepresentation_apply, Subgroup.coe_subtype]

/-- The adjoint representation of `K` on `𝔪`. -/
def adjoint𝔪 : Representation ℝ K D.𝔪 :=
  Subrepresentation.toRepresentation (ρ := (adjointRepresentation ℝ I G).comp K.subtype)
    ⟨D.𝔪, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔪 k hξ⟩

/-- The adjoint representation of `K` on `𝔮`. -/
def adjoint𝔮 : Representation ℝ K D.𝔮 :=
  Subrepresentation.toRepresentation (ρ := (adjointRepresentation ℝ I G).comp K.subtype)
    ⟨D.𝔮, fun k _ hξ ↦ D.adjointRepresentation_mem_𝔮 k hξ⟩

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

/-- The representation of `K` on the linear normal form model `(𝔪 × 𝔪*) × (𝔮 × V)`: the adjoint
action on `𝔪` and `𝔮`, its dual on `𝔪*` and `rep` on `V`, as in Tau Ceti's equivariant linear normal
form `exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`. -/
def linearModelRepresentation :
    Representation ℝ K ((D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :=
  (D.adjoint𝔪.prod D.adjoint𝔪.dual).prod
    (D.adjoint𝔮.prod D.repV)

theorem linearModelRepresentation_def :
    D.linearModelRepresentation =
      (D.adjoint𝔪.prod D.adjoint𝔪.dual).prod
        (D.adjoint𝔮.prod D.repV) :=
  (rfl)

/-- The action of `k` on the model moves the `𝔤`-component of `linearModelMap` by `Ad_k`. -/
theorem fst_linearModelMap_linearModelRepresentation (k : K)
    (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    (D.linearModelMap (D.linearModelRepresentation k x)).1 =
      adjointRepresentation ℝ I G k (D.linearModelMap x).1 := by
  obtain ⟨⟨m, f⟩, q, b⟩ := x
  simp only [linearModelRepresentation_def, Representation.prod_apply_apply, linearModelMap_apply,
    coe_adjoint𝔪_apply, coe_adjoint𝔮_apply, map_add]

/-- The action of `k` on the model moves the `V`-component of `linearModelMap` by `rep k`. -/
theorem snd_snd_linearModelMap_linearModelRepresentation (k : K)
    (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    (D.linearModelMap (D.linearModelRepresentation k x)).2.2 =
      D.rep k (D.linearModelMap x).2.2 := by
  obtain ⟨⟨m, f⟩, q, b⟩ := x
  simp [linearModelRepresentation_def]

/-- The action of `k` on the model moves the `A`-component of `linearModelMap`, read in `𝔤*`
through `ι𝔪`, by the coadjoint action `Ad*_k`. -/
theorem ι𝔪_snd_fst_linearModelMap_linearModelRepresentation (k : K)
    (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    D.ι𝔪 (D.linearModelMap (D.linearModelRepresentation k x)).2.1 =
      coadjointRepresentation ℝ I G k (D.ι𝔪 (D.linearModelMap x).2.1) := by
  obtain ⟨⟨m, f⟩, q, b⟩ := x
  ext ζ
  obtain ⟨n, hn, r, hr, rfl⟩ :=
    Submodule.mem_sup.1 (D.isCompl_𝔪_sup.sup_eq_top ▸ Submodule.mem_top (x := ζ))
  have hr' : adjointRepresentation ℝ I G (k⁻¹ : K) r ∈ D.𝔥 ⊔ D.𝔮 := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hr
    rw [map_add]
    exact Submodule.add_mem_sup (D.adjointRepresentation_mem_𝔥 _ hy)
      (D.adjointRepresentation_mem_𝔮 _ hz)
  have hn' : adjointRepresentation ℝ I G (k⁻¹ : K) n = D.adjoint𝔪 k⁻¹ ⟨n, hn⟩ :=
    (D.coe_adjoint𝔪_apply k⁻¹ ⟨n, hn⟩).symm
  simp only [InvMemClass.coe_inv] at hr' hn'
  simp only [linearModelRepresentation_def, Representation.prod_apply_apply, linearModelMap_apply,
    map_add, D.ι𝔪_apply_of_mem_sup _ hr, coadjointRepresentation_apply, add_zero]
  rw [← adjointRepresentation_apply, ← adjointRepresentation_apply, D.ι𝔪_apply_of_mem_sup _ hr',
    add_zero, hn', ι𝔪_apply_coe, LinearEquiv.apply_symm_apply]
  have h := D.ι𝔪_apply_coe (D.equivDual𝔪.symm (D.adjoint𝔪.dual k f)) ⟨n, hn⟩
  rw [LinearEquiv.apply_symm_apply, Representation.dual_apply] at h
  exact h

end LocalModelData

end SymplecticGeometry

end
