/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LeftTrivialization
public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Linear

/-!
# The two-form of the local model of a Hamiltonian action near an orbit

Let `G` be a real Lie group with Lie algebra `𝔤`, `N` a manifold and `ν : N → 𝔤*` a family of
covectors whose components `p ↦ ν p ξ` are smooth. Read through Tau Ceti's left trivialization
`Φ : G × 𝔤* ≃ T*G`, `(g, a) ↦ g • a` (`TauCeti.CotangentBundle.leftTrivialization`), the map
`Φ ∘ (id × ν) : G × N → T*G` sends `(g, p)` to the covector `ν p` moved from the identity to `g`
by the cotangent lift of left multiplication. For a two-form `β` on `N`, this file studies the
two-form

`(id × ν)^* Φ^* ω + pr_N^* β = -d⟨ν, θ⟩ + pr_N^* β`

on `G × N`, with `ω` the canonical symplectic form of `T*G` and `θ` the left-invariant
Maurer–Cartan form (`SymplecticGeometry.leftInvariantCovectorMapForm`).

The Marle–Guillemin–Sternberg local model of a Hamiltonian action near an orbit takes
`N = 𝔪* × V` and `ν (η, v) = τ + η + μ_V(v)`; the last part of the file builds its two-form from
linear data.

## Main results

* `SymplecticGeometry.contMDiff_toContinuousLinearMap_comp`: `ν`, read as a family of continuous
  functionals on the model space of `𝔤`, is smooth when its components are.
* `SymplecticGeometry.leftInvariantCovectorMapForm`: the two-form `-d⟨ν, θ⟩ + pr_N^* β` on
  `G × N`. It is closed when `β` is (`SymplecticGeometry.isClosed_leftInvariantCovectorMapForm`),
  invariant under `(g, p) ↦ (k * g, p)`
  (`SymplecticGeometry.mpullback_mul_left_leftInvariantCovectorMapForm`), and on the slice
  `G × {p}` it is the left-invariant Kirillov form of `ν p`
  (`SymplecticGeometry.mpullback_prodMk_leftInvariantCovectorMapForm`).
* `SymplecticGeometry.eval₂_leftInvariantCovectorMapForm`: at `(g, p)` the form pairs
  `(v₁, w₁)` and `(v₂, w₂)` to
  `(ν p).kirillovForm ξ₁ ξ₂ - d(ν · ξ₂)_p w₁ + d(ν · ξ₁)_p w₂ + β_p (w₁, w₂)`, where
  `ξᵢ = d(L_{g⁻¹})_g vᵢ`.
* `SymplecticGeometry.eval₂_leftInvariantCovectorMapForm_prodVectorField`: on product vector fields
  `(X_{ξᵢ}, Yᵢ)`, with `X_{ξᵢ}` left-invariant, the form at `(g, p)` is
  `ν p ⁅ξ₁, ξ₂⁆ - d(ν · ξ₂)_p (Y₁ p) + d(ν · ξ₁)_p (Y₂ p) + β_p (Y₁ p, Y₂ p)`.
* `SymplecticGeometry.eval₂_leftInvariantCovectorMapForm_of_tangentSpaceProdEquiv_eq`: for `N` a
  normed space, the same value with Fréchet derivatives on tangent vectors `(d(L_g) ξᵢ, wᵢ)`.
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

The values of the form come from Tau Ceti's
`TauCeti.CotangentBundle.eval₂_mpullback_prodMap_leftTrivialization_symplecticForm`, and the
invariance from `TauCeti.CotangentBundle.leftTrivialization_mul` and
`TauCeti.CotangentBundle.mpullback_smul_symplecticForm`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Bundle TauCeti TauCeti.Manifold TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {N : Type*} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

omit [LieGroup I ∞ G] in
/-- A family `ν : N → 𝔤*` of covectors with smooth components `p ↦ ν p ξ` is smooth as a family
of continuous functionals on the model space `E` of `𝔤`. -/
theorem contMDiff_toContinuousLinearMap_comp (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) :
    ContMDiff J 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      fun p ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p) :=
  -- `ν p`, read as a continuous functional, has the values of `ν p`. `ν p` is a functional on `𝔤`,
  -- which is only definitionally the model space `E`, so `LinearMap.coe_toContinuousLinearMap'`
  -- cannot rewrite here and the step is definitional.
  fun p ↦ TauCeti.contMDiffAt_clm_apply.2 fun v ↦ hν v p

variable [IsManifold J 1 N]

/-- The two-form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N`: the sum of the pullback of the canonical
symplectic form `ω` of `T*G` along `Φ ∘ (id × ν)`, with `Φ : G × 𝔤* ≃ T*G` the left
trivialization, and the pullback of a two-form `β` on `N` along the projection `pr_N = Prod.snd`.
The map `Φ ∘ (id × ν)` sends `(g, p)` to the covector `ν p ∘ d(L_{g⁻¹})_g` at `g`. -/
def leftInvariantCovectorMapForm (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ)
    (β : SmoothForm J N ℝ 2) : SmoothForm (I.prod J) (G × N) ℝ 2 :=
  SmoothForm.mpullback (Prod.map id _) (contMDiff_id.prodMap
      (contMDiff_toContinuousLinearMap_comp hν))
      (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
        (symplecticForm I G)) +
    SmoothForm.mpullback Prod.snd contMDiff_snd β

theorem leftInvariantCovectorMapForm_def (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ)
    (β : SmoothForm J N ℝ 2) :
    leftInvariantCovectorMapForm hν β =
      SmoothForm.mpullback (Prod.map id _) (contMDiff_id.prodMap
          (contMDiff_toContinuousLinearMap_comp hν))
          (SmoothForm.mpullback (leftTrivialization I G) (leftTrivialization I G).contMDiff
            (symplecticForm I G)) +
        SmoothForm.mpullback Prod.snd contMDiff_snd β :=
  (rfl)

/-- The form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N` is closed when `β` is. -/
theorem isClosed_leftInvariantCovectorMapForm [IsManifold J 2 N]
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) {β : SmoothForm J N ℝ 2} (hβ : β.IsClosed) :
    (leftInvariantCovectorMapForm hν β).IsClosed := by
  rw [leftInvariantCovectorMapForm_def]
  exact ((isSymplectic_symplecticForm.isClosed.mpullback _ _).mpullback _ _).add
    (hβ.mpullback _ contMDiff_snd)

/-- The form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N` is invariant under left translation
`(g, p) ↦ (k * g, p)` of the factor `G`. -/
@[simp]
theorem mpullback_mul_left_leftInvariantCovectorMapForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
        (leftInvariantCovectorMapForm hν β) =
      leftInvariantCovectorMapForm hν β := by
  have hf := contMDiff_toContinuousLinearMap_comp hν
  have hΦ := (leftTrivialization I G).contMDiff.comp (contMDiff_id.prodMap hf)
  -- Left translation of the factor `G` becomes the cotangent-lifted action of `k` on `T*G`.
  have h : (leftTrivialization I G ∘ Prod.map id
      fun p ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p)) ∘
        Prod.map (k * ·) id = (fun z : CotangentBundle I G ↦ k • z) ∘ (leftTrivialization I G ∘
          Prod.map id fun p ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p)) :=
    funext fun q ↦ leftTrivialization_mul k q.1 _
  rw [leftInvariantCovectorMapForm_def, map_add,
    SmoothForm.mpullback_prodMap_mpullback_snd contMDiff_mul_left contMDiff_id,
    SmoothForm.mpullback_id, LinearMap.id_apply]
  simp only [SmoothForm.mpullback_mpullback, h]
  rw [← SmoothForm.mpullback_mpullback _ _ hΦ (contMDiff_const_smul k),
    mpullback_smul_symplecticForm]

/-- On the slice `G × {p}`, the form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N` is the left-invariant
Kirillov form of `ν p`: the term `pr_N^* β` vanishes there, as `pr_N` is constant on the slice. -/
@[simp]
theorem mpullback_prodMk_leftInvariantCovectorMapForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (p : N) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
        (leftInvariantCovectorMapForm hν β) =
      (ν p).leftInvariantKirillovForm := by
  -- `Φ (g, ν p)` and the left-invariant covector field of `ν p` at `g` are covectors at `g` with
  -- the values `ν p (d(L_{g⁻¹})_g v)`.
  have h : (leftTrivialization I G ∘ Prod.map id
      fun p ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p)) ∘ (fun g : G ↦ (g, p)) =
      (ν p).leftInvariantCovector :=
    funext fun g ↦ CotangentBundle.ext (by simp) fun v ↦
      (leftTrivialization_snd_apply _ v).trans ((ν p).leftInvariantCovector_snd_apply g v).symm
  rw [leftInvariantCovectorMapForm_def, map_add, SmoothForm.mpullback_prodMk_left_mpullback_snd,
    add_zero, Module.Dual.leftInvariantKirillovForm_eq_mpullback_symplecticForm]
  simp only [SmoothForm.mpullback_mpullback, h]

/-! ### The form on tangent vectors -/

/-- **The form `-d⟨ν, θ⟩ + pr_N^* β` on tangent vectors.** At `(g, p)` it pairs the tangent
vectors `uᵢ = (vᵢ, wᵢ)` to
`(ν p).kirillovForm ξ₁ ξ₂ - d(ν · ξ₂)_p w₁ + d(ν · ξ₁)_p w₂ + β_p (w₁, w₂)`, where
`ξᵢ = d(L_{g⁻¹})_g vᵢ` and `(ν p).kirillovForm ξ₁ ξ₂ = ν p ⁅ξ₁, ξ₂⁆`. -/
theorem eval₂_leftInvariantCovectorMapForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (g : G) (p : N)
    (u₁ u₂ : TangentSpace (I.prod J) (g, p)) :
    (leftInvariantCovectorMapForm hν β).eval₂ (g, p) u₁ u₂ =
      (ν p).kirillovForm (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₁).1)
          (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₂).1) -
        mvfderiv J (fun y ↦ ν y (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₂).1)) p
          (tangentSpaceProdEquiv (g, p) u₁).2 +
        mvfderiv J (fun y ↦ ν y (mfderiv I I (g⁻¹ * ·) g (tangentSpaceProdEquiv (g, p) u₁).1)) p
          (tangentSpaceProdEquiv (g, p) u₂).2 +
        β.eval₂ p (tangentSpaceProdEquiv (g, p) u₁).2 (tangentSpaceProdEquiv (g, p) u₂).2 := by
  have hf := contMDiff_toContinuousLinearMap_comp hν
  have hd (ξ : GroupLieAlgebra I G) (w : TangentSpace J p) :
      mvfderiv J (fun y ↦ ν y ξ) p w =
        mvfderiv J (fun y ↦ LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν y)) p w ξ :=
    mvfderiv_clm_apply_const ((hf p).mdifferentiableAt (by simp)) ξ w
  have hk : Module.Dual.kirillovForm (L := GroupLieAlgebra I G)
      (LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν p) : E →ₗ[ℝ] ℝ) =
      (ν p).kirillovForm :=
    congrArg _ (LinearMap.coe_toContinuousLinearMap _)
  rw [leftInvariantCovectorMapForm_def, SmoothBundleForm.eval₂_add,
    eval₂_mpullback_prodMap_leftTrivialization_symplecticForm hf, SmoothForm.eval₂_mpullback_snd,
    tangentSpaceProdEquiv_apply, tangentSpaceProdEquiv_apply]
  linear_combination hd (mfderiv I I (g⁻¹ * ·) g u₂.1) u₁.2 -
    hd (mfderiv I I (g⁻¹ * ·) g u₁.1) u₂.2 +
    LinearMap.congr_fun (LinearMap.congr_fun hk (mfderiv I I (g⁻¹ * ·) g u₁.1))
      (mfderiv I I (g⁻¹ * ·) g u₂.1)

/-- The form `-d⟨ν, θ⟩ + pr_N^* β` on `G × N` on the product vector fields `(X_{ξᵢ}, Yᵢ)` of
left-invariant vector fields `X_{ξᵢ}` on `G` and vector fields `Yᵢ` on `N`: at `(g, p)` it is
`ν p ⁅ξ₁, ξ₂⁆ - d(ν · ξ₂)_p (Y₁ p) + d(ν · ξ₁)_p (Y₂ p) + β_p (Y₁ p, Y₂ p)`. -/
theorem eval₂_leftInvariantCovectorMapForm_prodVectorField
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (g : G) (p : N)
    (ξ₁ ξ₂ : GroupLieAlgebra I G) (Y₁ Y₂ : Π y : N, TangentSpace J y) :
    (leftInvariantCovectorMapForm hν β).eval₂ (g, p)
        (prodVectorField (mulInvariantVectorField ξ₁) Y₁ (g, p))
        (prodVectorField (mulInvariantVectorField ξ₂) Y₂ (g, p)) =
      ν p ⁅ξ₁, ξ₂⁆ - mvfderiv J (fun p ↦ ν p ξ₂) p (Y₁ p) +
        mvfderiv J (fun p ↦ ν p ξ₁) p (Y₂ p) + β.eval₂ p (Y₁ p) (Y₂ p) := by
  rw [eval₂_leftInvariantCovectorMapForm, tangentSpaceProdEquiv_prodVectorField,
    tangentSpaceProdEquiv_prodVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, Module.Dual.kirillovForm_apply]

/-- **The form `-d⟨ν, θ⟩ + pr_N^* β` on left-trivialized tangent vectors.** For `N` a normed space
`F`, at `(g, p)` the form pairs the tangent vectors `(d(L_g) ξᵢ, wᵢ)` to
`ν p ⁅ξ₁, ξ₂⁆ - d(ν · ξ₂)_p w₁ + d(ν · ξ₁)_p w₂ + β_p (w₁, w₂)`. -/
theorem eval₂_leftInvariantCovectorMapForm_of_tangentSpaceProdEquiv_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ν : F → Module.Dual ℝ (GroupLieAlgebra I G)}
    (hν : ∀ ξ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm 𝓘(ℝ, F) F ℝ 2)
    {g : G} {p : F} {u₁ u₂ : TangentSpace (I.prod 𝓘(ℝ, F)) (g, p)} {ξ₁ ξ₂ : GroupLieAlgebra I G}
    {w₁ w₂ : F} (hu₁ : tangentSpaceProdEquiv (g, p) u₁ = (mulInvariantVectorField ξ₁ g, w₁))
    (hu₂ : tangentSpaceProdEquiv (g, p) u₂ = (mulInvariantVectorField ξ₂ g, w₂)) :
    (leftInvariantCovectorMapForm hν β).eval₂ (g, p) u₁ u₂ =
      ν p ⁅ξ₁, ξ₂⁆ - fderiv ℝ (fun p ↦ ν p ξ₂) p w₁ + fderiv ℝ (fun p ↦ ν p ξ₁) p w₂ +
        β.eval₂ p w₁ w₂ := by
  rw [eval₂_leftInvariantCovectorMapForm, hu₁, hu₂, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, Module.Dual.kirillovForm_apply,
    mvfderiv_eq_fderiv_apply, mvfderiv_eq_fderiv_apply]

end SymplecticGeometry

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

end Covector

section LieGroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ V]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  (τ : Module.Dual ℝ (GroupLieAlgebra I G)) (ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))
  (ι𝔥 : Module.Dual ℝ 𝔥 →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))

/-- The two-form of the local model on `G × (A × V)`: the form
`Φ_ν^* ω + pr_V^* σ = -d⟨ν, θ⟩ + pr_V^* σ` of `SymplecticGeometry.leftInvariantCovectorMapForm`,
for the covectors `ν = localModelCovector σ ρ τ ι𝔪 ι𝔥` and the constant two-form `σ` on `V`
pulled back along the projection `pr_V : A × V → V`. -/
def localModelForm : SmoothForm (I.prod 𝓘(ℝ, A × V)) (G × (A × V)) ℝ 2 :=
  leftInvariantCovectorMapForm (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥)
    (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff σ.constSmooth)

theorem localModelForm_def :
    localModelForm σ ρ τ ι𝔪 ι𝔥 =
      leftInvariantCovectorMapForm (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥)
        (SmoothForm.mpullback Prod.snd contDiff_snd.contMDiff σ.constSmooth) :=
  (rfl)

/-- The two-form of the local model on `G × (A × V)` is closed. -/
theorem isClosed_localModelForm : (localModelForm (G := G) σ ρ τ ι𝔪 ι𝔥).IsClosed := by
  rw [localModelForm_def]
  exact isClosed_leftInvariantCovectorMapForm _
    ((SymplecticForm.isClosed_constSmooth σ).mpullback _ _)

/-- The two-form of the local model on `G × (A × V)` is invariant under left translation
`(g, η, v) ↦ (k * g, η, v)` of the factor `G`. -/
@[simp]
theorem mpullback_mul_left_localModelForm (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
        (localModelForm σ ρ τ ι𝔪 ι𝔥) =
      localModelForm σ ρ τ ι𝔪 ι𝔥 := by
  rw [localModelForm_def, mpullback_mul_left_leftInvariantCovectorMapForm]

/-- On the slice `G × {p}`, the two-form of the local model is the left-invariant Kirillov form
of the covector `localModelCovector σ ρ τ ι𝔪 ι𝔥 p`. -/
@[simp]
theorem mpullback_prodMk_localModelForm (p : A × V) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
        (localModelForm σ ρ τ ι𝔪 ι𝔥) =
      (localModelCovector σ ρ τ ι𝔪 ι𝔥 p).leftInvariantKirillovForm := by
  rw [localModelForm_def, mpullback_prodMk_leftInvariantCovectorMapForm]

end LieGroup

end SymplecticGeometry

end LinearData
