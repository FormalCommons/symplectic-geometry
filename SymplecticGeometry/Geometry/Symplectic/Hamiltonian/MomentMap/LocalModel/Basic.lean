/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Cotangent.Bundle.Induced.Basic
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Linear
import SymplecticGeometry.Geometry.Symplectic.Manifold.TwoForm

/-!
# The two-form of the local model of a Hamiltonian action near an orbit

Let `G` be a real Lie group with Lie algebra `𝔤`. The Marle–Guillemin–Sternberg local model of a
Hamiltonian action near an orbit carries, on `G × (A × V)` with `A ≃ 𝔪*` and `(V, σ)` a
symplectic vector space, Tau Ceti's induced form (`TauCeti.CotangentBundle.inducedForm`)

`-d⟨ν, θ⟩ + pr_V^* σ`

of the covectors `ν (η, v) = τ + η + μ_V(v)`, with `θ` the left-invariant Maurer–Cartan form.
This file builds these covectors and this two-form from linear data, and computes the form on
left-trivialized tangent vectors.

## Main results

* `SymplecticGeometry.localModelCovector`: the covectors `ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` on
  `A × V`, given linear maps `ι𝔪 : A → 𝔤*` and `ι𝔥 : 𝔥* → 𝔤*` and the moment map
  `μ_V = σ.linearMomentMapComp ρ` of a linear map `ρ : 𝔥 → sp(V, σ)`, whose components are smooth
  (`SymplecticGeometry.contMDiff_localModelCovector_apply`).
* `SymplecticGeometry.localModelForm`: the form `-d⟨ν, θ⟩ + pr_V^* σ` on `G × (A × V)` of
  these covectors. It is closed (`SymplecticGeometry.isClosed_localModelForm`), invariant under
  `(g, η, v) ↦ (k * g, η, v)` (`SymplecticGeometry.mpullback_mul_left_localModelForm`), and on
  the slice `G × {p}` it is the left-invariant Kirillov form of `ν p`
  (`SymplecticGeometry.mpullback_prodMk_localModelForm`). The factor `A × V` carries the model
  `𝓘(ℝ, A × V)`.
* `SymplecticGeometry.fderiv_localModelCovector_apply`: the derivative of `p ↦ ν p ξ` at `(η, v)`
  sends `(a, b)` to `(ι𝔪 a + ι𝔥 (dμ_V(v) b)) ξ`, with `dμ_V(v) b` the covector `ζ ↦ σ (ρ ζ v, b)`
  (`TauCeti.SymplecticForm.linearMomentMapCompPolar`).
* `SymplecticGeometry.eval₂_localModelForm_of_tangentSpaceProdEquiv_eq`,
  `SymplecticGeometry.eval₂_localModelForm_one_of_tangentSpaceProdEquiv_eq`: at `(g, η, v)`, and
  at `(1, η, v)`, the form pairs `(d(L_g) ξᵢ, aᵢ, bᵢ)` to
  `ν ⁅ξ₁, ξ₂⁆ - (ι𝔪 a₁ + ι𝔥 (dμ_V(v) b₁)) ξ₂ + (ι𝔪 a₂ + ι𝔥 (dμ_V(v) b₂)) ξ₁ + σ (b₁, b₂)`.

The values of the form come from
`TauCeti.CotangentBundle.eval₂_inducedForm_of_tangentSpaceProdEquiv_eq`, with the value of
`pr_V^* σ` from `TauCeti.SymplecticForm.eval₂_mpullback_snd_constSmooth`. Its slices come from
`TauCeti.CotangentBundle.mpullback_prodMk_inducedForm`, its closedness from
`TauCeti.CotangentBundle.isClosed_inducedForm`, and its invariance under left translation from
`TauCeti.CotangentBundle.mpullback_prodMap_mul_left_inducedForm`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Bundle TauCeti TauCeti.Manifold TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

/-! ### The local model from linear data -/

section LinearData

variable {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

namespace SymplecticGeometry

section Covector

variable {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] (τ : Module.Dual ℝ 𝔤)
  (ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ 𝔤) (ι𝔥 : Module.Dual ℝ 𝔥 →ₗ[ℝ] Module.Dual ℝ 𝔤)

/-- The family of covectors `ν : A × V → 𝔤*` of the local model,
`ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)`, with `μ_V = σ.linearMomentMapComp ρ`. In the local model of a
Hamiltonian action near an orbit, `A` is `𝔪*`, and `ι𝔪 : 𝔪* → 𝔤*` and `ι𝔥 : 𝔥* → 𝔤*` are the
extensions by zero given by a splitting `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`. -/
def localModelCovector (p : A × V) : Module.Dual ℝ 𝔤 :=
  τ + ι𝔪 p.1 + ι𝔥 (σ.linearMomentMapComp ρ p.2)

theorem localModelCovector_def (p : A × V) :
    localModelCovector σ ρ τ ι𝔪 ι𝔥 p = τ + ι𝔪 p.1 + ι𝔥 (σ.linearMomentMapComp ρ p.2) :=
  (rfl)

@[simp]
theorem localModelCovector_apply (η : A) (v : V) (ξ : 𝔤) :
    localModelCovector σ ρ τ ι𝔪 ι𝔥 (η, v) ξ =
      τ ξ + ι𝔪 η ξ + ι𝔥 (σ.linearMomentMapComp ρ v) ξ :=
  (rfl)

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ V]

/-- Each component `p ↦ ν p ξ` of the covectors `ν = localModelCovector σ ρ τ ι𝔪 ι𝔥` of the local
model is smooth on `A × V`: it is affine in `η` and quadratic in `v`. -/
theorem contDiff_localModelCovector_apply (ξ : 𝔤) :
    ContDiff ℝ ∞ fun p : A × V ↦ localModelCovector σ ρ τ ι𝔪 ι𝔥 p ξ := by
  have hA : ContDiff ℝ ∞ fun η : A ↦ ι𝔪 η ξ :=
    (LinearMap.toContinuousLinearMap (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔪)).contDiff
  have hV := σ.contDiff_linearMomentMapComp ρ (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔥)
  simp only [LinearMap.comp_apply, Module.Dual.eval_apply] at hV
  simp only [localModelCovector_def, LinearMap.add_apply]
  exact (contDiff_const.add (hA.comp contDiff_fst)).add (hV.comp contDiff_snd)

/-- The components of `ν = localModelCovector σ ρ τ ι𝔪 ι𝔥` are smooth on the manifold `A × V`
with its model `𝓘(ℝ, A × V)`. -/
theorem contMDiff_localModelCovector_apply (ξ : 𝔤) :
    ContMDiff 𝓘(ℝ, A × V) 𝓘(ℝ) ∞ fun p : A × V ↦ localModelCovector σ ρ τ ι𝔪 ι𝔥 p ξ :=
  (contDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥 ξ).contMDiff

/-- The derivative of the component `p ↦ ν p ξ` of `ν = localModelCovector σ ρ τ ι𝔪 ι𝔥` at
`(η, v)` sends `(a, b)` to `(ι𝔪 a + ι𝔥 (dμ_V(v) b)) ξ`, where
`dμ_V(v) b = σ.linearMomentMapCompPolar ρ v b` is the covector `ζ ↦ σ (ρ ζ v, b)` on `𝔥`. -/
theorem fderiv_localModelCovector_apply (ξ : 𝔤) (η a : A) (v b : V) :
    fderiv ℝ (fun p : A × V ↦ localModelCovector σ ρ τ ι𝔪 ι𝔥 p ξ) (η, v) (a, b) =
      (ι𝔪 a + ι𝔥 (σ.linearMomentMapCompPolar ρ v b)) ξ := by
  have hV : DifferentiableAt ℝ
      (fun x ↦ (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔥) (σ.linearMomentMapComp ρ x)) v :=
    (σ.contDiff_linearMomentMapComp ρ _).differentiable (by simp) v
  have h := ((hasFDerivAt_const (τ ξ) (η, v)).add
    ((LinearMap.toContinuousLinearMap (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔪)).hasFDerivAt.comp (η, v)
      hasFDerivAt_fst)).add (hV.hasFDerivAt.comp (η, v) hasFDerivAt_snd)
  have hfun : (fun p : A × V ↦ localModelCovector σ ρ τ ι𝔪 ι𝔥 p ξ) = (fun _ ↦ τ ξ) +
      LinearMap.toContinuousLinearMap (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔪) ∘ Prod.fst +
      (fun x ↦ (Module.Dual.eval ℝ 𝔤 ξ ∘ₗ ι𝔥) (σ.linearMomentMapComp ρ x)) ∘ Prod.snd := by
    funext p
    simp [localModelCovector_def]
  rw [hfun, h.fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    σ.fderiv_apply_linearMomentMapComp ρ]
  simp

end Covector

section LieGroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ V]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  (τ : Module.Dual ℝ (GroupLieAlgebra I G)) (ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))
  (ι𝔥 : Module.Dual ℝ 𝔥 →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))

/-- The two-form of the local model on `G × (A × V)`: Tau Ceti's induced form
`-d⟨ν, θ⟩ + pr_V^* σ` (`TauCeti.CotangentBundle.inducedForm`) of the covectors
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥` and of the constant two-form `σ` on `V` pulled back along the
projection `pr_V : A × V → V`. -/
def localModelForm : SmoothForm (I.prod 𝓘(ℝ, A × V)) (G × (A × V)) ℝ 2 :=
  inducedForm I G (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff σ.constSmooth)
    (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E)
      (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥))

theorem localModelForm_def :
    localModelForm σ ρ τ ι𝔪 ι𝔥 =
      inducedForm I G (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff σ.constSmooth)
        (contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E)
          (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥)) :=
  (rfl)

/-- The two-form of the local model on `G × (A × V)` is closed. -/
theorem isClosed_localModelForm : (localModelForm (G := G) σ ρ τ ι𝔪 ι𝔥).IsClosed := by
  rw [localModelForm_def]
  exact isClosed_inducedForm _ ((SymplecticForm.isClosed_constSmooth σ).mpullback _ _)

/-- The two-form of the local model on `G × (A × V)` is invariant under left translation
`(g, η, v) ↦ (k * g, η, v)` of the factor `G`. -/
@[simp]
theorem mpullback_mul_left_localModelForm (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
        (localModelForm σ ρ τ ι𝔪 ι𝔥) =
      localModelForm σ ρ τ ι𝔪 ι𝔥 := by
  rw [localModelForm_def, mpullback_prodMap_mul_left_inducedForm]

/-- On the slice `G × {p}`, the two-form of the local model is the left-invariant Kirillov form
of the covector `localModelCovector σ ρ τ ι𝔪 ι𝔥 p`. -/
@[simp]
theorem mpullback_prodMk_localModelForm (p : A × V) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
        (localModelForm σ ρ τ ι𝔪 ι𝔥) =
      (localModelCovector σ ρ τ ι𝔪 ι𝔥 p).leftInvariantKirillovForm := by
  rw [localModelForm_def, mpullback_prodMk_inducedForm]
  exact congrArg _ (LinearMap.coe_toContinuousLinearMap _)

/-- **The two-form of the local model on left-trivialized tangent vectors.** At `(g, η, v)`, with
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥 (η, v)`, the form pairs the tangent vectors
`(d(L_g) ξᵢ, aᵢ, bᵢ)` to
`ν ⁅ξ₁, ξ₂⁆ - (ι𝔪 a₁ + ι𝔥 (dμ_V(v) b₁)) ξ₂ + (ι𝔪 a₂ + ι𝔥 (dμ_V(v) b₂)) ξ₁ + σ (b₁, b₂)`, where
`dμ_V(v) b = σ.linearMomentMapCompPolar ρ v b` is the covector `ζ ↦ σ (ρ ζ v, b)` on `𝔥`. -/
theorem eval₂_localModelForm_of_tangentSpaceProdEquiv_eq {g : G} {η : A} {v : V}
    {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, A × V)) (g, (η, v))} {ξ₁ ξ₂ : GroupLieAlgebra I G}
    {a₁ a₂ : A} {b₁ b₂ : V}
    (hu₁ : tangentSpaceProdEquiv (g, (η, v)) u₁ = (mulInvariantVectorField ξ₁ g, (a₁, b₁)))
    (hu₂ : tangentSpaceProdEquiv (g, (η, v)) u₂ = (mulInvariantVectorField ξ₂ g, (a₂, b₂))) :
    (localModelForm σ ρ τ ι𝔪 ι𝔥).eval₂ (g, (η, v)) u₁ u₂ =
      localModelCovector σ ρ τ ι𝔪 ι𝔥 (η, v) ⁅ξ₁, ξ₂⁆ -
        (ι𝔪 a₁ + ι𝔥 (σ.linearMomentMapCompPolar ρ v b₁)) ξ₂ +
        (ι𝔪 a₂ + ι𝔥 (σ.linearMomentMapCompPolar ρ v b₂)) ξ₁ + σ b₁ b₂ := by
  rw [localModelForm_def,
    eval₂_inducedForm_of_tangentSpaceProdEquiv_eq (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥)
      _ hu₁ hu₂,
    fderiv_localModelCovector_apply, fderiv_localModelCovector_apply,
    SymplecticForm.eval₂_mpullback_snd_constSmooth]

/-- The two-form of the local model at `(1, η, v)`: with
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥 (η, v)`, it pairs the tangent vectors `(ξᵢ, aᵢ, bᵢ)` to
`ν ⁅ξ₁, ξ₂⁆ - (ι𝔪 a₁ + ι𝔥 (dμ_V(v) b₁)) ξ₂ + (ι𝔪 a₂ + ι𝔥 (dμ_V(v) b₂)) ξ₁ + σ (b₁, b₂)`. -/
theorem eval₂_localModelForm_one_of_tangentSpaceProdEquiv_eq {η : A} {v : V}
    {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), (η, v))} {ξ₁ ξ₂ : GroupLieAlgebra I G}
    {a₁ a₂ : A} {b₁ b₂ : V}
    (hu₁ : tangentSpaceProdEquiv ((1 : G), (η, v)) u₁ = (ξ₁, (a₁, b₁)))
    (hu₂ : tangentSpaceProdEquiv ((1 : G), (η, v)) u₂ = (ξ₂, (a₂, b₂))) :
    (localModelForm σ ρ τ ι𝔪 ι𝔥).eval₂ ((1 : G), (η, v)) u₁ u₂ =
      localModelCovector σ ρ τ ι𝔪 ι𝔥 (η, v) ⁅ξ₁, ξ₂⁆ -
        (ι𝔪 a₁ + ι𝔥 (σ.linearMomentMapCompPolar ρ v b₁)) ξ₂ +
        (ι𝔪 a₂ + ι𝔥 (σ.linearMomentMapCompPolar ρ v b₂)) ξ₁ + σ b₁ b₂ :=
  eval₂_localModelForm_of_tangentSpaceProdEquiv_eq σ ρ τ ι𝔪 ι𝔥
    (hu₁.trans (by rw [mulInvariantVectorField_one]))
    (hu₂.trans (by rw [mulInvariantVectorField_one]))

end LieGroup

end SymplecticGeometry

end LinearData
