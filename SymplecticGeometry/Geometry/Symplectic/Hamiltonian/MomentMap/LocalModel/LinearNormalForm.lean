/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.LinearAlgebra.Submodule.Compl
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Action
import SymplecticGeometry.Algebra.Lie.Coadjoint
import SymplecticGeometry.Geometry.Lie.Adjoint.Differential

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
* `SymplecticGeometry.LocalModelData.linearModelRepresentation`: the representation of `K` on the
  model, by the adjoint action on `𝔪` and `𝔮`, its dual on `𝔪*` and `rep` on `V`.

## Main results

* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq`: the form
  at `(1, 0, 0)` on tangent vectors `(ξᵢ, aᵢ, bᵢ)`.
* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq_add_of_mem_𝔥`:
  the form at `(1, 0, 0)` does not change when an element of `𝔥` is added to the `𝔤` component
  of its first argument.
* `SymplecticGeometry.LocalModelData.eval₂_form_one_zero_linearModelMap`: through
  `linearModelMap`, the form at `(1, 0, 0)` is the form of the linear normal form model.
* `SymplecticGeometry.LocalModelData.isCompl_range_linearModelMap`: the range of
  `linearModelMap` is a complement of `𝔥 × 0`.
* `SymplecticGeometry.LocalModelData.forall_eval₂_form_one_zero_eq_zero_iff`: the kernel of the
  form at `(1, 0, 0)` is the space `𝔥 × 0` of the directions `(ξ, 0, 0)` with `ξ ∈ 𝔥`. It is
  Tau Ceti's `Module.Dual.forall_kirillovForm_add_eq_zero_iff`, the radical of the
  Marle–Guillemin–Sternberg tensor, for the projection `𝔤 → 𝔪` along `𝔥 ⊕ 𝔮`, which maps
  `𝔤_τ = 𝔥 ⊕ 𝔪` onto `𝔪` with kernel meeting `𝔤_τ` in `𝔥`.
* `SymplecticGeometry.LocalModelData.tangentSpaceProdEquiv_mfderiv_conj_smul_one_zero`: for
  `k ∈ K`, the differential at `(1, 0, 0)` of `(g, p) ↦ (k g k⁻¹, k • p)` is
  `(ξ, a, b) ↦ (Ad_k ξ, repA k a, rep k b)`. Its `G` component is
  `TauCeti.Lie.mfderiv_conj_one_apply` (`Ad_k` is the differential at `1` of conjugation),
  and its fibre component is `mfderiv_fiberDistribMulAction_const_smul`, combined by
  `TauCeti.Manifold.mfderiv_prodMap_apply`.
* `SymplecticGeometry.LocalModelData.linearModelMap_linearModelRepresentation`: `linearModelMap`
  intertwines the action of `K` on the model with that differential, the action of `K` on the
  tangent space at `(1, 0, 0)`.

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

/-- The form of the local model at `(1, 0, 0)` does not see the `𝔥` component of its first
argument: for `h ∈ 𝔥`, it pairs `(h + ξ₁, a₁, b₁)` and `(ξ₂, a₂, b₂)` to
`τ ⁅ξ₁, ξ₂⁆ - ι𝔪 a₁ ξ₂ + ι𝔪 a₂ ξ₁ + σ (b₁, b₂)`, as it pairs `(ξ₁, a₁, b₁)` and `(ξ₂, a₂, b₂)`. -/
theorem eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq_add_of_mem_𝔥
    {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))}
    {h ξ₁ ξ₂ : GroupLieAlgebra I G} {a₁ a₂ : A} {b₁ b₂ : V} (hh : h ∈ D.𝔥)
    (hu₁ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₁ = (h + ξ₁, (a₁, b₁)))
    (hu₂ : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u₂ = (ξ₂, (a₂, b₂))) :
    D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u₁ u₂ =
      D.τ ⁅ξ₁, ξ₂⁆ - D.ι𝔪 a₁ ξ₂ + D.ι𝔪 a₂ ξ₁ + D.σ b₁ b₂ := by
  rw [D.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq hu₁ hu₂]
  simp [add_lie, D.τ.mem_lieAnnihilator_iff.1 (D.𝔥_le_lieAnnihilator hh),
    D.ι𝔪_apply_of_mem_sup _ (Submodule.mem_sup_left hh)]

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
  exact D.isCompl_𝔥_sup.symm.prod isCompl_top_bot

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
  have h₁ := D.τ.mem_lieAnnihilator_iff.1 (D.𝔪_le_lieAnnihilator m₁.property)
  have h₂ := D.τ.mem_lieAnnihilator_iff'.1 (D.𝔪_le_lieAnnihilator m₂.property)
  simp only [lie_add, add_lie, map_add, h₁, h₂, ι𝔪_apply_coe, h𝔮, LinearEquiv.apply_symm_apply,
    SymplecticForm.prod_apply, cotangentSymplecticForm_apply,
    Module.Dual.kirillovSymplecticForm_apply]
  ring

/-- **The kernel of the form of the local model at `(1, 0, 0)`.** A tangent vector at `(1, 0, 0)`
pairs to zero with every tangent vector exactly when it is `(ξ, 0, 0)` for some `ξ ∈ 𝔥`. -/
theorem forall_eval₂_form_one_zero_eq_zero_iff
    (u : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))) :
    (∀ u', D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u u' = 0) ↔
      tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u ∈ D.𝔥.prod ⊥ := by
  set e := tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))
  set π := Submodule.projectionOnto _ _ D.isCompl_𝔪_sup
  have hι (a : A) (ζ : GroupLieAlgebra I G) : D.ι𝔪 a ζ = D.equivDual𝔪 a (π ζ) := by
    rw [ι𝔪_def, LinearMap.comp_apply, LinearMap.dualMap_apply, LinearEquiv.coe_coe]
  -- `π` maps `𝔤_τ ⊇ 𝔪` onto `𝔪`, and `𝔤_τ ∩ ker π = (𝔥 ⊕ 𝔪) ∩ (𝔥 ⊕ 𝔮) = 𝔥`.
  have hπ : (lieAnnihilator ℝ (GroupLieAlgebra I G) D.τ).toSubmodule.map π = ⊤ :=
    eq_top_iff.2 fun m _ ↦
      ⟨m, D.𝔪_le_lieAnnihilator m.property, Submodule.projectionOnto_apply_left _ m⟩
  have h𝔥 : (lieAnnihilator ℝ (GroupLieAlgebra I G) D.τ).toSubmodule ⊓ LinearMap.ker π = D.𝔥 := by
    rw [Submodule.ker_projectionOnto, ← D.𝔥_sup_𝔪, sup_inf_assoc_of_le _ le_sup_left,
      D.isCompl_𝔪_sup.inf_eq_bot, sup_bot_eq]
  rcases hu : e u with ⟨ξ, a, b⟩
  -- The form pairs `u` with `e.symm (ζ, a', w)` as Tau Ceti's Marle–Guillemin–Sternberg tensor.
  have hpair (ζ : GroupLieAlgebra I G) (a' : A) (w : V) :
      D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u (e.symm (ζ, (a', w))) =
        D.equivDual𝔪 a' (π ξ) - D.equivDual𝔪 a (π ζ) + D.τ.kirillovForm ξ ζ +
          D.σ.toBilinForm b w := by
    -- `ring` also matches `D.σ b w` with `D.σ.toBilinForm b w`, the definition of the coercion.
    rw [D.eval₂_form_one_zero_of_tangentSpaceProdEquiv_eq hu (e.apply_symm_apply (ζ, (a', w))), hι,
      hι, Module.Dual.kirillovForm_apply]
    ring
  have key : (∀ u', D.form.eval₂ ((1 : G), ((0 : A), (0 : V))) u u' = 0) ↔
      ∀ (ζ : GroupLieAlgebra I G) (b' : Module.Dual ℝ D.𝔪) (w : V),
        b' (π ξ) - D.equivDual𝔪 a (π ζ) + D.τ.kirillovForm ξ ζ + D.σ.toBilinForm b w = 0 := by
    refine ⟨fun h ζ b' w ↦ ?_, fun h u' ↦ ?_⟩
    · have := h (e.symm (ζ, (D.equivDual𝔪.symm b', w)))
      rwa [hpair, LinearEquiv.apply_symm_apply] at this
    · obtain ⟨⟨ζ, a', w⟩, rfl⟩ := e.symm.surjective u'
      rw [hpair]
      exact h ζ (D.equivDual𝔪 a') w
  rw [key, D.τ.forall_kirillovForm_add_eq_zero_iff D.σ.nondegenerate.1 hπ, ← h𝔥]
  simp only [Submodule.mem_prod, Submodule.mem_inf, LieSubalgebra.mem_toSubmodule,
    LinearMap.mem_ker, LinearEquiv.map_eq_zero_iff, and_assoc]
  refine and_congr_right' (and_congr_right' ⟨?_, fun h ↦ ?_⟩)
  · rintro ⟨rfl, rfl⟩
    exact zero_mem _
  · exact Prod.mk_eq_zero.1 h

/-! ### The action of `K` -/

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

@[simp]
theorem linearModelRepresentation_apply (k : K) (m : D.𝔪) (f : Module.Dual ℝ D.𝔪) (q : D.𝔮)
    (b : V) :
    D.linearModelRepresentation k ((m, f), (q, b)) =
      ((D.adjoint𝔪 k m, D.adjoint𝔪.dual k f), (D.adjoint𝔮 k q, D.repV k b)) :=
  (rfl)

/-- **The differential of the action of `K` at `(1, 0, 0)`.** For `k ∈ K`, the differential at
`(1, 0, 0)` of the map `(g, p) ↦ (k g k⁻¹, k • p)` of `G × (A × V)` sends the tangent vector
`(ξ, a, b)` to `(Ad_k ξ, repA k a, rep k b)`. -/
theorem tangentSpaceProdEquiv_mfderiv_conj_smul_one_zero (k : K)
    {u : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))}
    {ξ : GroupLieAlgebra I G} {a : A} {b : V}
    (hu : tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V))) u = (ξ, (a, b))) :
    letI := D.fiberDistribMulAction
    tangentSpaceProdEquiv _
        (mfderiv (I.prod 𝓘(ℝ, A × V)) (I.prod 𝓘(ℝ, A × V))
          (fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2))
          ((1 : G), ((0 : A), (0 : V))) u) =
      (adjointRepresentation ℝ I G k ξ, (D.repA k a, D.rep k b)) := by
  let := D.fiberDistribMulAction
  -- The map is the product of conjugation by `k`, whose differential at `1` is `Ad_k`, and of
  -- the linear action of `k` on `A × V`.
  have hg : MDifferentiableAt 𝓘(ℝ, A × V) 𝓘(ℝ, A × V) (fun q : A × V ↦ k • q) 0 :=
    D.fiberDistribMulAction_smul_eq_toContinuousLinearMap k ▸
      ContinuousLinearMap.mdifferentiableAt _
  rw [← (tangentSpaceProdEquiv _).symm_apply_apply u, hu]
  refine (congrArg (tangentSpaceProdEquiv _)
    (mfderiv_prodMap_apply (p := ((1 : G), ((0 : A), (0 : V))))
      ((mdifferentiable_conj (k : G)).mdifferentiableAt) hg (ξ, (a, b)))).trans ?_
  -- The point of `tangentSpaceProdEquiv_symm_apply` is given, since the image of `(1, 0, 0)` is
  -- written in two ways that agree only up to unfolding.
  rw [tangentSpaceProdEquiv_apply,
    tangentSpaceProdEquiv_symm_apply (p := ((k : G) * 1 * (k : G)⁻¹, k • ((0 : A), (0 : V))))]
  exact Prod.ext (mfderiv_conj_one_apply (k : G) ξ)
    ((D.mfderiv_fiberDistribMulAction_const_smul k 0 (a, b)).trans
      (D.fiberDistribMulAction_smul k (a, b)))

/-- **`linearModelMap` is equivariant.** The action of `k ∈ K` on the linear normal form model is
taken by `linearModelMap` to the differential at `(1, 0, 0)` of the map
`(g, p) ↦ (k g k⁻¹, k • p)` of `G × (A × V)`. -/
theorem linearModelMap_linearModelRepresentation (k : K)
    (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    letI := D.fiberDistribMulAction
    D.linearModelMap (D.linearModelRepresentation k x) =
      tangentSpaceProdEquiv _
        (mfderiv (I.prod 𝓘(ℝ, A × V)) (I.prod 𝓘(ℝ, A × V))
          (fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2))
          ((1 : G), ((0 : A), (0 : V)))
          ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (D.linearModelMap x))) := by
  rw [D.tangentSpaceProdEquiv_mfderiv_conj_smul_one_zero k
    ((tangentSpaceProdEquiv _).apply_symm_apply _)]
  obtain ⟨⟨m, f⟩, q, b⟩ := x
  simp only [linearModelRepresentation_apply, linearModelMap_apply, coe_adjoint𝔪_apply,
    coe_adjoint𝔮_apply, map_add, repA_apply, LinearEquiv.apply_symm_apply,
    repV_apply]

end LocalModelData

end SymplecticGeometry

end
