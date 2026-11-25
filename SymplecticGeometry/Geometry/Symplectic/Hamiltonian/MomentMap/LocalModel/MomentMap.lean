/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Data
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.Manifold

/-!
# The moment map of the local model's form on `G × (A × V)`

Let `G` be a real Lie group with Lie algebra `𝔤`, `N` a manifold and `ν : N → 𝔤*` a family of
covectors with smooth components. The group `G` acts on `G × N` by left multiplication of the
first factor, `g • (h, p) = (g * h, p)` (`SymplecticGeometry.prodFstMulAction`). This file proves
that `μ (g, p) = Ad*_g (ν p)` is a coadjoint-equivariant moment map of this action for the
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
on `N` (`SymplecticGeometry.mfderiv_snd_fundamentalVectorField_prodFstMulAction`), with every
tangent vector to zero, so it does not change the moment map.

## Main definitions

* `SymplecticGeometry.prodFstMulAction`: the action `g • (h, p) = (g * h, p)` of `G` on `G × N`.

## Main results

* `SymplecticGeometry.contMDiffSMul_prodFstMulAction`: this action is smooth.
* `SymplecticGeometry.mfderiv_fst_fundamentalVectorField_prodFstMulAction`,
  `SymplecticGeometry.mfderiv_snd_fundamentalVectorField_prodFstMulAction`: its fundamental
  vector field of `ξ` has the components `(ξ_G, 0)`, with `ξ_G` the fundamental vector field of
  left multiplication.
* `SymplecticGeometry.isEquivariantMomentMap_leftInvariantCovectorMapForm`: `(g, p) ↦ Ad*_g (ν p)`
  is an equivariant moment map of `-d⟨ν, θ⟩ + pr_N^* β`.
* `SymplecticGeometry.isEquivariantMomentMap_localModelForm`,
  `SymplecticGeometry.LocalModelData.isEquivariantMomentMap_form`: the cases of the local model's
  form, from linear data and from `SymplecticGeometry.LocalModelData`.

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

/-! ### The action of `G` on `G × N` through the first factor -/

section Action

variable (G N : Type*) [Group G]

/-- The action of a group `G` on `G × N` by left multiplication of the first factor,
`g • (h, p) = (g * h, p)`. It is not a global instance, since `N` may carry an action of `G` of
its own: use it with `letI := prodFstMulAction G N`. -/
@[instance_reducible]
def prodFstMulAction : MulAction G (G × N) where
  smul g q := (g * q.1, q.2)
  one_smul q := Prod.ext (one_mul q.1) rfl
  mul_smul g h q := Prod.ext (mul_assoc g h q.1) rfl

variable {G N}

/-- The action of `G` on `G × N` through the first factor. Not a simp lemma: its left side is a
scalar multiplication by an action that is not an instance. -/
theorem prodFstMulAction_smul (g : G) (q : G × N) :
    letI := prodFstMulAction G N
    g • q = (g * q.1, q.2) :=
  (rfl)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace G] [ChartedSpace H G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- The action of `G` on `G × N` through the first factor is `Cⁿ` when multiplication on `G` is. -/
theorem contMDiffSMul_prodFstMulAction [ContMDiffMul I n G] :
    letI := prodFstMulAction G N
    ContMDiffSMul I (I.prod J) n G (G × N) :=
  letI := prodFstMulAction G N
  ⟨((contMDiff_fst.mul (contMDiff_fst.comp contMDiff_snd)).prodMk
    (contMDiff_snd.comp contMDiff_snd)).congr fun p ↦ prodFstMulAction_smul p.1 p.2⟩

variable [ContMDiffMul I 1 G]

/-- The first component of the fundamental vector field of `ξ` for the action of `G` on `G × N`
through the first factor is the fundamental vector field of `ξ` for left multiplication on `G`. -/
theorem mfderiv_fst_fundamentalVectorField_prodFstMulAction (ξ : GroupLieAlgebra I G)
    (q : G × N) :
    letI := prodFstMulAction G N
    mfderiv (I.prod J) I Prod.fst q (fundamentalVectorField (I.prod J) ξ q) =
      fundamentalVectorField I ξ q.1 :=
  letI := prodFstMulAction G N
  haveI := contMDiffSMul_prodFstMulAction (I := I) (J := J) (n := 1) (G := G) (N := N)
  mfderiv_fundamentalVectorField_of_map_smul mdifferentiableAt_fst
    ((ContMDiffSMul.contMDiff_smul_const (n := 1) q).mdifferentiableAt one_ne_zero)
    (fun g ↦ congrArg Prod.fst (prodFstMulAction_smul g q)) ξ

/-- The fundamental vector fields of the action of `G` on `G × N` through the first factor have
no component along `N`. -/
theorem mfderiv_snd_fundamentalVectorField_prodFstMulAction (ξ : GroupLieAlgebra I G)
    (q : G × N) :
    letI := prodFstMulAction G N
    mfderiv (I.prod J) J Prod.snd q (fundamentalVectorField (I.prod J) ξ q) = 0 := by
  let := prodFstMulAction G N
  have := contMDiffSMul_prodFstMulAction (I := I) (J := J) (n := 1) (G := G) (N := N)
  -- `Prod.snd` is constant along the orbit map `g ↦ g • q`.
  have hc : (Prod.snd ∘ fun g : G ↦ g • q) = fun _ ↦ q.2 :=
    funext fun g ↦ by rw [Function.comp_apply, prodFstMulAction_smul]
  rw [fundamentalVectorField_apply, ← mfderiv_comp_apply_of_eq (1 : G) mdifferentiableAt_snd
    ((ContMDiffSMul.contMDiff_smul_const (n := 1) q).mdifferentiableAt one_ne_zero)
    (one_smul G q), hc, mfderiv_const, zero_apply]

end Action

/-! ### The moment map of `-d⟨ν, θ⟩ + pr_N^* β` -/

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

section CovectorMap

variable {N : Type*} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] {ν : N → Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **The moment map of `-d⟨ν, θ⟩ + pr_N^* β`.** For the action of `G` on `G × N` by left
multiplication of the first factor, `(g, p) ↦ Ad*_g (ν p)` is a coadjoint-equivariant moment map of
the two-form `-d⟨ν, θ⟩ + pr_N^* β` of `SymplecticGeometry.leftInvariantCovectorMapForm`, for every
two-form `β` on `N`. -/
theorem isEquivariantMomentMap_leftInvariantCovectorMapForm [T2Space G] [I.Boundaryless]
    (hν : ∀ ξ, ContMDiff J 𝓘(ℝ) ∞ fun p ↦ ν p ξ) (β : SmoothForm J N ℝ 2) :
    letI := prodFstMulAction G N
    haveI := contMDiffSMul_prodFstMulAction (I := I) (J := J) (n := ∞) (G := G) (N := N)
    SmoothTwoForm.IsEquivariantMomentMap (leftInvariantCovectorMapForm hν β)
      fun q : G × N ↦ coadjointRepresentation ℝ I G q.1 (ν q.2) := by
  let := prodFstMulAction G N
  have := contMDiffSMul_prodFstMulAction (I := I) (J := J) (n := ∞) (G := G) (N := N)
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hf := contMDiff_toContinuousLinearMap_of_contMDiff_apply (E := E) hν
  have hφ := (leftTrivialization I G).contMDiff.comp (contMDiff_id.prodMap hf)
  -- The map `Φ ∘ (id × ν)` intertwines the action on `G × N` with the cotangent-lifted action, so
  -- the cotangent moment map pulls back along it.
  have h := (isEquivariantMomentMap_momentMap (IG := I) (G := G) (I := I) (M := G)).mpullback hφ
    fun g q ↦ (congrArg _ (Prod.ext (congrArg Prod.fst (prodFstMulAction_smul g q)) rfl)).trans
      (leftTrivialization_mul g q.1 _)
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
            mfderiv_snd_fundamentalVectorField_prodFstMulAction,
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

/-- **The moment map of the local model's form on `G × (A × V)`.** For the action of `G` by left
multiplication of the first factor, `(g, p) ↦ Ad*_g (ν p)`, with
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥`, is a coadjoint-equivariant moment map of the two-form
`localModelForm σ ρ τ ι𝔪 ι𝔥`. -/
theorem isEquivariantMomentMap_localModelForm [T2Space G] [I.Boundaryless] :
    letI := prodFstMulAction G (A × V)
    haveI := contMDiffSMul_prodFstMulAction (I := I) (J := 𝓘(ℝ, A × V)) (n := ∞) (G := G)
      (N := A × V)
    SmoothTwoForm.IsEquivariantMomentMap (localModelForm σ ρ τ ι𝔪 ι𝔥)
      fun q : G × (A × V) ↦
        coadjointRepresentation ℝ I G q.1 (localModelCovector σ ρ τ ι𝔪 ι𝔥 q.2) := by
  rw [localModelForm_def]
  exact isEquivariantMomentMap_leftInvariantCovectorMapForm _ _

end LinearData

namespace LocalModelData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The moment map of the local model's form on `G × (A × V)`.** For the action of `G` by left
multiplication of the first factor, `(g, p) ↦ Ad*_g (D.covector p)` is a coadjoint-equivariant
moment map of `D.form`. -/
theorem isEquivariantMomentMap_form [T2Space G] [I.Boundaryless] :
    letI := prodFstMulAction G (A × V)
    haveI := contMDiffSMul_prodFstMulAction (I := I) (J := 𝓘(ℝ, A × V)) (n := ∞) (G := G)
      (N := A × V)
    SmoothTwoForm.IsEquivariantMomentMap D.form
      fun q : G × (A × V) ↦ coadjointRepresentation ℝ I G q.1 (D.covector q.2) := by
  simp only [form_def, covector_def]
  exact isEquivariantMomentMap_localModelForm _ _ _ _ _

end LocalModelData

end SymplecticGeometry

end
