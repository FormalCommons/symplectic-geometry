/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint.LieGroup
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import SymplecticGeometry.Geometry.Symplectic.Coadjoint.LieGroup
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.Linear

/-!
# Covectors moved by left translation, and the two-form of the local model

Let `G` be a real Lie group with Lie algebra `𝔤`, `N` a manifold and `ν : N → 𝔤*` a family of
covectors whose components `p ↦ ν p ξ` are smooth. This file studies the map

`Φ_ν : G × N → T*G`, `Φ_ν (g, p) = g • ν p`,

which moves the covector `ν p` at the identity to the point `g` by the cotangent lift of left
multiplication (`SymplecticGeometry.leftInvariantCovectorMap`). For each `p`, the map
`g ↦ Φ_ν (g, p)` is Tau Ceti's left-invariant covector field `(ν p).leftInvariantCovector`.

The Marle–Guillemin–Sternberg local model of a Hamiltonian action near an orbit takes
`N = 𝔪* × V` and `ν (η, v) = τ + η + μ_V(v)`; the last part of the file builds its two-form from
linear data.

## Main results

* `SymplecticGeometry.proj_leftInvariantCovectorMap`,
  `SymplecticGeometry.leftInvariantCovectorMap_snd_apply`: `Φ_ν (g, p)` is the covector
  `ν p ∘ d(L_{g⁻¹})_g` at `g`.
* `SymplecticGeometry.leftInvariantCovectorMap_mul`: `Φ_ν (k * g, p) = k • Φ_ν (g, p)`.
* `SymplecticGeometry.contMDiff_leftInvariantCovectorMap`: `Φ_ν` is smooth.
* `SymplecticGeometry.isClosed_mpullback_leftInvariantCovectorMap_symplecticForm`: the pullback
  `Φ_ν^* ω` of the canonical symplectic form of `T*G` is closed.
* `SymplecticGeometry.mpullback_mul_left_mpullback_leftInvariantCovectorMap_symplecticForm`:
  `Φ_ν^* ω` is invariant under `(g, p) ↦ (k * g, p)`.
* `SymplecticGeometry.mpullback_prodMk_mpullback_leftInvariantCovectorMap_symplecticForm`:
  restricted to the slice `G × {p}`, `Φ_ν^* ω` is the left-invariant Kirillov form of `ν p`.
* `SymplecticGeometry.leftInvariantCovectorMapForm`: for a two-form `β` on `N`, the two-form
  `Φ_ν^* ω + pr_N^* β` on `G × N`, which is `-d⟨ν, θ⟩ + β` with `θ` the left-invariant
  Maurer–Cartan form. It is closed when `β` is
  (`SymplecticGeometry.isClosed_leftInvariantCovectorMapForm`), invariant under
  `(g, p) ↦ (k * g, p)` (`SymplecticGeometry.mpullback_mul_left_leftInvariantCovectorMapForm`),
  and on the slice `G × {p}` it is the left-invariant Kirillov form of `ν p`
  (`SymplecticGeometry.mpullback_prodMk_leftInvariantCovectorMapForm`).
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

The smoothness adapts the proof of Tau Ceti's `Module.Dual.contMDiff_leftInvariantCovector`, and
the invariance that of `Module.Dual.mpullback_mul_left_leftInvariantForm`, through the
equivariance of `Φ_ν` and `TauCeti.CotangentBundle.mpullback_smul_symplecticForm`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Bundle TauCeti
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {N : Type*} (ν : N → Module.Dual ℝ (GroupLieAlgebra I G))

/-- The map `G × N → T*G` of a family `ν : N → 𝔤*` of covectors: it sends `(g, p)` to the image
`g • ν p` of the covector `ν p` at the identity under the cotangent lift of left multiplication,
which is the covector `ν p ∘ d(L_{g⁻¹})_g` at `g`. -/
def leftInvariantCovectorMap (q : G × N) : CotangentBundle I G :=
  (ν q.2).leftInvariantCovector q.1

theorem leftInvariantCovectorMap_def (q : G × N) :
    leftInvariantCovectorMap ν q = (ν q.2).leftInvariantCovector q.1 :=
  (rfl)

@[simp]
theorem leftInvariantCovectorMap_apply (g : G) (p : N) :
    leftInvariantCovectorMap ν (g, p) = (ν p).leftInvariantCovector g :=
  (rfl)

/-- The covector `leftInvariantCovectorMap ν (g, p)` lies over `g`. -/
@[simp]
theorem proj_leftInvariantCovectorMap (q : G × N) : (leftInvariantCovectorMap ν q).proj = q.1 :=
  (ν q.2).proj_leftInvariantCovector q.1

/-- The value of `leftInvariantCovectorMap ν (g, p)` on a tangent vector `v` at `g` is
`ν p (d(L_{g⁻¹})_g v)`. -/
theorem leftInvariantCovectorMap_snd_apply (g : G) (p : N) (v : TangentSpace I g) :
    (leftInvariantCovectorMap ν (g, p)).snd v = ν p (mfderiv I I (g⁻¹ * ·) g v) :=
  (ν p).leftInvariantCovector_snd_apply g v

/-- The map `leftInvariantCovectorMap ν` is equivariant for left multiplication on the factor `G`
and the cotangent-lifted action on `T*G`. -/
theorem leftInvariantCovectorMap_mul (k g : G) (p : N) :
    leftInvariantCovectorMap ν (k * g, p) = k • leftInvariantCovectorMap ν (g, p) :=
  (ν p).leftInvariantCovector_mul k g

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {ν}

/-- The map `leftInvariantCovectorMap ν : G × N → T*G` is smooth when each component
`p ↦ ν p ξ` of `ν` is. -/
theorem contMDiff_leftInvariantCovectorMap (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) :
    ContMDiff (I.prod J) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (leftInvariantCovectorMap ν) := by
  have h : leftInvariantCovectorMap ν = fun q : G × N ↦
      q.1 • TotalSpace.mk' (E →L[ℝ] ℝ) (1 : G) (LinearMap.toContinuousLinearMap (ν q.2)) := by
    funext q
    rw [leftInvariantCovectorMap_def, ← Module.Dual.leftInvariantCovector_one,
      ← Module.Dual.leftInvariantCovector_mul, mul_one]
  -- `ν` is smooth as a family of continuous functionals on the model space `E` of `𝔤`, since its
  -- components are; `ν'` is `ν` with `𝔤` read as `E`, which carries the norm.
  let ν' : N → Module.Dual ℝ E := ν
  have hc : ContMDiff J 𝓘(ℝ, E →L[ℝ] ℝ) ∞ fun p ↦ LinearMap.toContinuousLinearMap (ν' p) :=
    fun p ↦ TauCeti.contMDiffAt_clm_apply.2 fun v ↦ by
      simp only [LinearMap.coe_toContinuousLinearMap']
      exact hν v p
  rw [h]
  exact contMDiff_fst.smul ((CotangentBundle.contMDiff_mk_comp (1 : G) hc).comp contMDiff_snd)

/-! ### The pullback of the canonical symplectic form -/

/-- The pullback `Φ_ν^* ω` of the canonical symplectic form of `T*G` along
`Φ_ν = leftInvariantCovectorMap ν` is closed. -/
theorem isClosed_mpullback_leftInvariantCovectorMap_symplecticForm [IsManifold J 2 N]
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) :
    (SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
      (CotangentBundle.symplecticForm I G)).IsClosed :=
  CotangentBundle.isSymplectic_symplecticForm.isClosed.mpullback _ _

variable [IsManifold J 1 N]

/-- The pullback `Φ_ν^* ω` of the canonical symplectic form of `T*G` along
`Φ_ν = leftInvariantCovectorMap ν` is invariant under left translation `(g, p) ↦ (k * g, p)` of
the factor `G`. -/
@[simp]
theorem mpullback_mul_left_mpullback_leftInvariantCovectorMap_symplecticForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
      (SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
        (CotangentBundle.symplecticForm I G)) =
      SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
        (CotangentBundle.symplecticForm I G) := by
  rw [SmoothForm.mpullback_mpullback_of_comp_eq (f := Prod.map (k * ·) id)
    (g := leftInvariantCovectorMap ν) _ _ (contMDiff_leftInvariantCovectorMap hν)
    (contMDiff_const_smul k) (funext fun q ↦ leftInvariantCovectorMap_mul ν k q.1 q.2),
    CotangentBundle.mpullback_smul_symplecticForm]

/-- On the slice `G × {p}`, the pullback `Φ_ν^* ω` of the canonical symplectic form of `T*G`
along `Φ_ν = leftInvariantCovectorMap ν` is the left-invariant Kirillov form of `ν p`. -/
@[simp]
theorem mpullback_prodMk_mpullback_leftInvariantCovectorMap_symplecticForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (p : N) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
      (SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
        (CotangentBundle.symplecticForm I G)) =
      (ν p).leftInvariantKirillovForm := by
  have h : leftInvariantCovectorMap ν ∘ (fun g : G ↦ (g, p)) = (ν p).leftInvariantCovector :=
    funext fun g ↦ leftInvariantCovectorMap_apply ν g p
  simp only [SmoothForm.mpullback_mpullback, h,
    Module.Dual.leftInvariantKirillovForm_eq_mpullback_symplecticForm]

/-! ### Adding the pullback of a two-form on `N` -/

/-- The two-form `Φ_ν^* ω + pr_N^* β` on `G × N`: the sum of the pullback of the canonical
symplectic form `ω` of `T*G` along `Φ_ν = leftInvariantCovectorMap ν` and the pullback of a
two-form `β` on `N` along the projection `pr_N = Prod.snd`. -/
def leftInvariantCovectorMapForm (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ)
    (β : SmoothForm J N ℝ 2) : SmoothForm (I.prod J) (G × N) ℝ 2 :=
  SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
      (CotangentBundle.symplecticForm I G) +
    SmoothForm.mpullback Prod.snd contMDiff_snd β

theorem leftInvariantCovectorMapForm_def (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ)
    (β : SmoothForm J N ℝ 2) :
    leftInvariantCovectorMapForm hν β =
      SmoothForm.mpullback (leftInvariantCovectorMap ν) (contMDiff_leftInvariantCovectorMap hν)
          (CotangentBundle.symplecticForm I G) +
        SmoothForm.mpullback Prod.snd contMDiff_snd β :=
  (rfl)

/-- The form `Φ_ν^* ω + pr_N^* β` on `G × N` is closed when `β` is. -/
theorem isClosed_leftInvariantCovectorMapForm [IsManifold J 2 N]
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) {β : SmoothForm J N ℝ 2} (hβ : β.IsClosed) :
    (leftInvariantCovectorMapForm hν β).IsClosed := by
  rw [leftInvariantCovectorMapForm_def]
  exact (isClosed_mpullback_leftInvariantCovectorMap_symplecticForm hν).add
    (hβ.mpullback _ contMDiff_snd)

/-- The form `Φ_ν^* ω + pr_N^* β` on `G × N` is invariant under left translation
`(g, p) ↦ (k * g, p)` of the factor `G`. -/
@[simp]
theorem mpullback_mul_left_leftInvariantCovectorMapForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (k : G) :
    SmoothForm.mpullback (Prod.map (k * ·) id) (contMDiff_mul_left.prodMap contMDiff_id)
        (leftInvariantCovectorMapForm hν β) =
      leftInvariantCovectorMapForm hν β := by
  rw [leftInvariantCovectorMapForm_def, map_add,
    mpullback_mul_left_mpullback_leftInvariantCovectorMap_symplecticForm hν,
    SmoothForm.mpullback_prodMap_mpullback_snd contMDiff_mul_left contMDiff_id,
    SmoothForm.mpullback_id, LinearMap.id_apply]

/-- On the slice `G × {p}`, the form `Φ_ν^* ω + pr_N^* β` on `G × N` is the left-invariant
Kirillov form of `ν p`: the term `pr_N^* β` vanishes there, as `pr_N` is constant on the slice. -/
@[simp]
theorem mpullback_prodMk_leftInvariantCovectorMapForm
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) (p : N) :
    SmoothForm.mpullback (fun g : G ↦ (g, p)) (contMDiff_id.prodMk contMDiff_const)
        (leftInvariantCovectorMapForm hν β) =
      (ν p).leftInvariantKirillovForm := by
  rw [leftInvariantCovectorMapForm_def, map_add,
    mpullback_prodMk_mpullback_leftInvariantCovectorMap_symplecticForm hν,
    SmoothForm.mpullback_prodMk_left_mpullback_snd, add_zero]

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
