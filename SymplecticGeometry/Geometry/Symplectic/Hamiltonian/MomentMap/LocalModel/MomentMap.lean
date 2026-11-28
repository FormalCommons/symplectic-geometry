/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.MomentMap

/-!
# The moment map of the local model, on `G × (A × V)` and on `G ×_K (A × V)`

Let `G` be a real Lie group with Lie algebra `𝔤`, acting on `G × (A × V)` by left multiplication
of the first factor, `g • (h, p) = (g * h, p)`: the statements take any such action, together
with this equation, and `SymplecticGeometry.prodFstMulAction` is one. For the covectors
`ν (η, v) = τ + ι𝔪 η + ι𝔥 (μ_V v)` of the Marle–Guillemin–Sternberg local model, the map
`μ (g, p) = Ad*_g (ν p)` is a coadjoint-equivariant moment map of the local model's two-form on
`G × (A × V)`. This is the case of the local model of
`TauCeti.CotangentBundle.isEquivariantMomentMap_inducedForm`, in
`SymplecticGeometry/Geometry/Symplectic/Cotangent/Bundle/Induced.lean`.

The last part of the file states, for the local model, the values of Tau Ceti's moment map
`TauCeti.CotangentBundle.balancedProductInducedMomentMap`, `[g, p] ↦ Ad*_g (ν p)`, on the balanced
product `G ×_K (A × V)`. Tau Ceti's
`TauCeti.CotangentBundle.isEquivariantMomentMap_balancedProductInducedForm` makes it an
equivariant moment map of the descended form
`TauCeti.CotangentBundle.balancedProductInducedForm`.

## Main results

* `SymplecticGeometry.isEquivariantMomentMap_localModelForm`,
  `SymplecticGeometry.LocalModelData.isEquivariantMomentMap_form`: the cases of the local model's
  form, from linear data and from `SymplecticGeometry.LocalModelData`.
* `SymplecticGeometry.LocalModelData.balancedProductInducedMomentMap_mk`,
  `SymplecticGeometry.LocalModelData.balancedProductInducedMomentMap_smul`,
  `SymplecticGeometry.LocalModelData.balancedProductInducedMomentMap_mk_zero`: the moment map of
  the local model on `G ×_K (A × V)` at classes, its equivariance, and its values along the zero
  section.

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

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

/-! ### The local model -/

section LinearData

variable {𝔥 : Type*} [AddCommGroup 𝔥] [Module ℝ 𝔥]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (σ : SymplecticForm V) (ρ : 𝔥 →ₗ[ℝ] skewAdjointLieSubalgebra σ.toBilinForm)
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (τ : Module.Dual ℝ (GroupLieAlgebra I G)) (ι𝔪 : A →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))
  (ι𝔥 : Module.Dual ℝ 𝔥 →ₗ[ℝ] Module.Dual ℝ (GroupLieAlgebra I G))

/-- **The moment map of the local model's form on `G × (A × V)`.** For an action of `G` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map `(g, p) ↦ Ad*_g (ν p)`, with
`ν = localModelCovector σ ρ τ ι𝔪 ι𝔥`, is a coadjoint-equivariant moment map of the two-form
`localModelForm σ ρ τ ι𝔪 ι𝔥`. -/
theorem isEquivariantMomentMap_localModelForm [T2Space G] [I.Boundaryless]
    [MulAction G (G × (A × V))]
    [ContMDiffSMul I (I.prod 𝓘(ℝ, A × V)) ∞ G (G × (A × V))]
    (hsmul : ∀ (g : G) (q : G × (A × V)), g • q = (g * q.1, q.2)) :
    SmoothTwoForm.IsEquivariantMomentMap (localModelForm σ ρ τ ι𝔪 ι𝔥)
      fun q : G × (A × V) ↦
        coadjointRepresentation ℝ I G q.1 (localModelCovector σ ρ τ ι𝔪 ι𝔥 q.2) := by
  rw [localModelForm_def]
  exact isEquivariantMomentMap_inducedForm hsmul (contMDiff_localModelCovector_apply σ ρ τ ι𝔪 ι𝔥) _

end LinearData

namespace LocalModelData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The moment map of the local model's form on `G × (A × V)`.** For an action of `G` by left
multiplication of the first factor, `g • (h, p) = (g * h, p)`, the map
`(g, p) ↦ Ad*_g (D.covector p)` is a coadjoint-equivariant moment map of `D.form`. -/
theorem isEquivariantMomentMap_form [T2Space G] [I.Boundaryless]
    [MulAction G (G × (A × V))]
    [ContMDiffSMul I (I.prod 𝓘(ℝ, A × V)) ∞ G (G × (A × V))]
    (hsmul : ∀ (g : G) (q : G × (A × V)), g • q = (g * q.1, q.2)) :
    SmoothTwoForm.IsEquivariantMomentMap D.form
      fun q : G × (A × V) ↦ coadjointRepresentation ℝ I G q.1 (D.covector q.2) := by
  simp only [form_def, covector_def]
  exact isEquivariantMomentMap_localModelForm _ _ _ _ _ hsmul

/-! ### The moment map on `G ×_K (A × V)` -/

/-- The moment map `[g, p] ↦ Ad*_g (D.covector p)` of the local model on `G ×_K (A × V)`, Tau
Ceti's `TauCeti.CotangentBundle.balancedProductInducedMomentMap`, at `[g, p]`. -/
theorem balancedProductInducedMomentMap_mk (g : G) (p : A × V) :
    letI := D.fiberDistribMulAction
    balancedProductInducedMomentMap G D.covectorCLM_smul
        (BalancedProduct.mk K (K.toRightTranslation g) p) =
      coadjointRepresentation ℝ I G g (D.covector p) := by
  let := D.fiberDistribMulAction
  rw [TauCeti.CotangentBundle.balancedProductInducedMomentMap_mk, coe_covectorCLM]

/-- The moment map of the local model is equivariant for the action `k • [g, p] = [k g, p]`
of `G` on `G ×_K (A × V)` and the coadjoint action: `μ_Y (k • y) = Ad*_k (μ_Y y)`. Unlike
`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.apply_smul`, this needs no smooth structure. -/
theorem balancedProductInducedMomentMap_smul (k : G)
    (y : letI := D.fiberDistribMulAction; BalancedProduct K K.RightTranslation (A × V)) :
    letI := D.fiberDistribMulAction
    balancedProductInducedMomentMap G D.covectorCLM_smul (k • y) =
      coadjointRepresentation ℝ I G k
        (balancedProductInducedMomentMap G D.covectorCLM_smul y) := by
  let := D.fiberDistribMulAction
  induction y using BalancedProduct.induction_on_toRightTranslation with
  | h g p =>
    rw [BalancedProduct.smul_mk_toRightTranslation, balancedProductInducedMomentMap_mk,
      balancedProductInducedMomentMap_mk, map_mul, mul_apply_eq_comp]

/-- Along the zero section, the moment map of the local model is `[g, 0, 0] ↦ Ad*_g τ`. -/
theorem balancedProductInducedMomentMap_mk_zero (g : G) :
    letI := D.fiberDistribMulAction
    balancedProductInducedMomentMap G D.covectorCLM_smul
        (BalancedProduct.mk K (K.toRightTranslation g) ((0 : A), (0 : V))) =
      coadjointRepresentation ℝ I G g D.τ := by
  let := D.fiberDistribMulAction
  rw [balancedProductInducedMomentMap_mk, ← Prod.zero_eq_mk, covector_zero]

end LocalModelData

end SymplecticGeometry

end
