/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.LinearNormalForm
public import TauCeti.LinearAlgebra.LinearMap.Comp

/-!
# The tangent space of `G ×_K (A × V)` at `[1, 0]` and the linear normal form

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the local model, with descended
form `ω = D.descendedForm` on `Y = G ×_K (A × V)` and projection `π : G × (A × V) → Y`. This file
identifies the tangent space of `Y` at `[1, 0]`, with `ω` and the action of `K`, with the linear
normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` of Tau Ceti's `MomentMap/LinearNormalForm.lean`.

The identification is `dπ_(1, 0, 0) ∘ D.linearModelMap`, with the tangent space of `G × (A × V)` at
`(1, 0, 0)` read as `𝔤 × A × V`; the file defines this reading of `dπ_(1, 0, 0)` once, as the
linear map `SymplecticGeometry.LocalModelData.mkTangentMap`. Its kernel is `𝔥 × 0`
(`SymplecticGeometry.LocalModelData.mem_ker_mfderiv_mk_one_zero_iff`) and it is onto, since `π`
is a submersion. The range of `linearModelMap` is a complement of `𝔥 × 0`, so the composite is
bijective (Tau Ceti's `LinearMap.bijective_comp_iff`). The form `ω` at `[1, 0]` evaluates on images
under `dπ` as `D.form` at `(1, 0, 0)`, which on the range of `linearModelMap` is the model's form.
Finally, `k ∈ K` fixes `[1, 0]`, and `(k • ·) ∘ π = π ∘ c_k` with `c_k (g, p) = (k g k⁻¹, k • p)`,
whose differential at `(1, 0, 0)` `linearModelMap` intertwines with the representation of `K` on
the model.

The file also splits the tangent space at `[1, 0]` into the directions `dπ_(1, 0, 0) (ξ, 0)`,
`ξ ∈ 𝔤`, tangent to the orbit of `[1, 0]`, and the fibre directions `dπ_(1, 0, 0) (0, p)`,
`p ∈ A × V`. The two kinds of direction span complementary subspaces, and `p ↦ dπ_(1, 0, 0) (0, p)`
is injective; both facts again come from the kernel and the surjectivity of `mkTangentMap`, composed
with `LinearMap.inl` and `LinearMap.inr`. The fibre map is `K`-equivariant because `dc_k` sends
`(0, p)` to `(0, k • p)`.

## Main definitions

* `SymplecticGeometry.LocalModelData.mkTangentMap`: the linear map `y ↦ dπ_(1, 0, 0) y` from
  `𝔤 × (A × V)` to the tangent space of `G ×_K (A × V)` at `[1, 0]`.
* `SymplecticGeometry.LocalModelData.linearModelEquiv`: the linear equivalence from the linear
  normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` to the tangent space of `G ×_K (A × V)` at `[1, 0]`.
* `SymplecticGeometry.LocalModelData.fiberTangentMap`,
  `SymplecticGeometry.LocalModelData.orbitTangentMap`: the linear maps `p ↦ dπ_(1, 0, 0) (0, p)`
  and `ξ ↦ dπ_(1, 0, 0) (ξ, 0)` into the tangent space at `[1, 0]`.

## Main results

* `SymplecticGeometry.LocalModelData.ker_mkTangentMap`,
  `SymplecticGeometry.LocalModelData.surjective_mkTangentMap`: `mkTangentMap` has kernel `𝔥 × 0`
  and is onto.
* `SymplecticGeometry.LocalModelData.bijective_mkTangentMap_comp_linearModelMap`:
  `x ↦ dπ_(1, 0, 0) (linearModelMap x)` is bijective.
* `SymplecticGeometry.LocalModelData.linearModelEquiv_mk_zero_mk_zero`: `linearModelEquiv` sends
  `((m, 0), (q, 0))` to `dπ_(1, 0, 0) (ξ, 0)` whenever `ξ - (m + q) ∈ 𝔥`.
* `SymplecticGeometry.LocalModelData.eval₂_descendedForm_linearModelEquiv`: through
  `linearModelEquiv`, the descended form at `[1, 0]` is the form of the linear normal form model.
* `SymplecticGeometry.LocalModelData.linearModelEquiv_linearModelRepresentation`:
  `linearModelEquiv` takes the representation of `K` on the model to the differential at `[1, 0]`
  of the action of `K` on `G ×_K (A × V)`.
* `SymplecticGeometry.LocalModelData.fiberTangentMap_smul`,
  `SymplecticGeometry.LocalModelData.injective_fiberTangentMap`,
  `SymplecticGeometry.LocalModelData.isCompl_range_orbitTangentMap_range_fiberTangentMap`: the
  fibre directions are `K`-equivariant, injective, and complementary to the orbit directions.
* `SymplecticGeometry.LocalModelData.map_fiberTangentMap_smul`,
  `SymplecticGeometry.LocalModelData.isCompl_range_range_comp_fiberTangentMap`: the same after a
  linear map `T` to a module `W`: equivariance when `T` takes the action of `K` to given
  endomorphisms of `W`, and the complement when `T` is an isomorphism.

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
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)

/-- **The differential of the projection at `(1, 0, 0)`.** The linear map
`y ↦ dπ_(1, 0, 0) y` from `𝔤 × (A × V)`, read as the tangent space of `G × (A × V)` at
`(1, 0, 0)`, to the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`. -/
def mkTangentMap :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    (GroupLieAlgebra I G × (A × V)) →ₗ[ℝ]
      TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) :=
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
      ((1 : G), ((0 : A), (0 : V)))).toLinearMap ∘ₗ
    (tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm.toLinearMap

theorem mkTangentMap_apply (y : GroupLieAlgebra I G × (A × V)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.mkTangentMap y =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm y) :=
  (rfl)

/-- **The kernel of `dπ` at `(1, 0, 0)`.** The kernel of `mkTangentMap` is `𝔥 × 0`. -/
theorem ker_mkTangentMap : LinearMap.ker D.mkTangentMap = D.𝔥.prod ⊥ := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  ext y
  have hs : tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))
      ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm y) = y :=
    ContinuousLinearEquiv.apply_symm_apply _ y
  rw [LinearMap.mem_ker, mkTangentMap_apply, ← ContinuousLinearMap.coe_coe, ← LinearMap.mem_ker,
    D.mem_ker_mfderiv_mk_one_zero_iff, hs]
  -- `mem_ker_mfderiv_mk_one_zero_iff` states membership in `𝔥 × 0` read in the product of the
  -- tangent spaces of `G` and `A × V`, type synonyms of `𝔤` and `A × V`.
  exact Iff.rfl

/-- **`dπ` at `(1, 0, 0)` is onto.** `mkTangentMap` is surjective, since `π` is a
submersion. -/
theorem surjective_mkTangentMap : Function.Surjective D.mkTangentMap := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  exact ((BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)).surjective_mfderiv
    (x := ((1 : G), ((0 : A), (0 : V)))) (by simp)).comp
    (tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm.surjective

/-- **The linear normal form model spans the tangent space at `[1, 0]`.** The map
`x ↦ dπ_(1, 0, 0) (linearModelMap x)` from the linear normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` to
the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`, is bijective. -/
theorem bijective_mkTangentMap_comp_linearModelMap :
    Function.Bijective (D.mkTangentMap ∘ₗ D.linearModelMap) :=
  -- The range of `linearModelMap` is a complement of the kernel `𝔥 × 0` of the surjective map
  -- `mkTangentMap`.
  LinearMap.bijective_comp_iff.2 ⟨D.injective_linearModelMap,
    D.ker_mkTangentMap ▸ D.isCompl_range_linearModelMap, D.surjective_mkTangentMap⟩

/-- **The linear normal form model is the tangent space at `[1, 0]`.** The linear equivalence
`x ↦ dπ_(1, 0, 0) (linearModelMap x)` from the linear normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` to
the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`. -/
def linearModelEquiv :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    ((D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) ≃ₗ[ℝ]
      TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) :=
  LinearEquiv.ofBijective (D.mkTangentMap ∘ₗ D.linearModelMap)
    D.bijective_mkTangentMap_comp_linearModelMap

theorem linearModelEquiv_apply (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.linearModelEquiv x =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (D.linearModelMap x)) :=
  (rfl)

/-- **Directions of `𝔤` in the image of `linearModelEquiv`.** For `m ∈ 𝔪` and `q ∈ 𝔮`,
`linearModelEquiv ((m, 0), (q, 0))` is `dπ_(1, 0, 0) (ξ, 0)` for each `ξ ∈ 𝔤` with
`ξ - (m + q) ∈ 𝔥`, where `π (g, p) = [g, p]`. -/
theorem linearModelEquiv_mk_zero_mk_zero {ξ : GroupLieAlgebra I G} (m : D.𝔪) (q : D.𝔮)
    (hξ : ξ - (m + q) ∈ D.𝔥) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.linearModelEquiv ((m, 0), (q, 0)) =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (ξ, 0)) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  rw [linearModelEquiv_apply]
  -- The difference of the two directions is `(m + q - ξ, 0)`, in the kernel `𝔥 × 0` of `dπ`.
  refine (LinearMap.sub_mem_ker_iff (f := D.mkTangentMap)
    (x := D.linearModelMap ((m, 0), (q, 0))) (y := (ξ, 0))).1 ?_
  rw [ker_mkTangentMap, linearModelMap_apply, map_zero]
  exact ⟨(congrArg (· ∈ D.𝔥) (neg_sub ξ _)).mp (neg_mem hξ), sub_eq_zero.2 rfl⟩

/-- **The descended form at `[1, 0]` is the linear normal form.** Through `linearModelEquiv`, the
descended form `ω` of the local model at `[1, 0]` is the form of the linear normal form model
`(𝔪 × 𝔪*) × (𝔮 × V)`: the sum of the canonical form of `𝔪 × 𝔪*`, the Kirillov form of `τ` on
`𝔮` and `σ`. -/
theorem eval₂_descendedForm_linearModelEquiv (x₁ x₂ : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
      (IZ := 𝓘(ℝ, A × V)) (F := F)
    SmoothBundleForm.eval₂ D.descendedForm
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V)))
        (D.linearModelEquiv x₁) (D.linearModelEquiv x₂) =
      (cotangentSymplecticForm.prod ((D.τ.kirillovSymplecticForm D.isCompl_𝔮).prod D.σ)) x₁ x₂ := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  rw [linearModelEquiv_apply, linearModelEquiv_apply]
  exact (D.eval₂_descendedForm_mfderiv ((1 : G), ((0 : A), (0 : V))) _ _).trans
    (D.eval₂_form_one_zero_linearModelMap ((tangentSpaceProdEquiv _).apply_symm_apply _)
      ((tangentSpaceProdEquiv _).apply_symm_apply _))

/-- **The action of `K` at `[1, 0]`, read on `G × (A × V)`.** Each `k ∈ K` fixes `[1, 0]`, and
the differential at `[1, 0]` of `y ↦ k • y` sends `dπ_(1, 0, 0) u` to `dπ_(1, 0, 0) (dc_k u)`,
where `π (g, p) = [g, p]` and `dc_k` is the differential at `(1, 0, 0)` of
`c_k (g, p) = (k g k⁻¹, k • p)`. -/
theorem mfderiv_smul_mfderiv_mk_one_zero (k : K)
    (u : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V)))) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y)
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V)))
        (mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
          ((1 : G), ((0 : A), (0 : V))) u) =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        (mfderiv (I.prod 𝓘(ℝ, A × V)) (I.prod 𝓘(ℝ, A × V))
          (fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2))
          ((1 : G), ((0 : A), (0 : V))) u) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)
  have hπ := (BalancedProduct.isSubmersion_mk_toRightTranslation (K := K) (Z := A × V) (I := I)
    (IZ := 𝓘(ℝ, A × V)) (F := F)).contMDiff.mdifferentiable (by simp)
  have hk : MDifferentiable 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (n := ∞) (k : G)).mdifferentiable (by simp)
  have hc : MDifferentiable (I.prod 𝓘(ℝ, A × V)) (I.prod 𝓘(ℝ, A × V))
      fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2) :=
    ((contMDiff_mul_left.mul contMDiff_const).prodMap
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓘(ℝ, F)) (n := ∞) k)).mdifferentiable (by simp)
  -- `k • [g, p] = [k g k⁻¹, k • p]`, and the map `(g, p) ↦ (k g k⁻¹, k • p)` fixes `(1, 0, 0)`.
  have hcomp : (fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y) ∘
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) =
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2) ∘
        fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2) := by
    funext p
    simp only [Function.comp_apply, BalancedProduct.smul_mk_toRightTranslation]
    rw [← Subgroup.coe_inv, BalancedProduct.mk_toRightTranslation_mul, inv_smul_smul]
  have hfix : (fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2))
      ((1 : G), ((0 : A), (0 : V))) = ((1 : G), ((0 : A), (0 : V))) :=
    Prod.ext (by simp) (smul_zero (A := A × V) k)
  rw [← mfderiv_comp_apply_of_eq _ (hπ _) (hc _) hfix, ← hcomp, mfderiv_comp_apply _ (hk _) (hπ _)]

/-- **`linearModelEquiv` is equivariant.** Each `k ∈ K` fixes `[1, 0]`, and `linearModelEquiv`
takes the action of `k` on the linear normal form model to the differential at `[1, 0]` of the
map `y ↦ k • y` of `G ×_K (A × V)`. -/
theorem linearModelEquiv_linearModelRepresentation (k : K)
    (x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.linearModelEquiv (D.linearModelRepresentation k x) =
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y)
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V)))
        (D.linearModelEquiv x) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  -- By `linearModelMap_linearModelRepresentation`, `linearModelMap` takes the action of `k` to the
  -- differential of `(g, p) ↦ (k g k⁻¹, k • p)` at `(1, 0, 0)`.
  have h : (tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm
        (D.linearModelMap (D.linearModelRepresentation k x)) =
      mfderiv (I.prod 𝓘(ℝ, A × V)) (I.prod 𝓘(ℝ, A × V))
        (fun x : G × (A × V) ↦ ((k : G) * x.1 * (k : G)⁻¹, k • x.2))
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (D.linearModelMap x)) :=
    (tangentSpaceProdEquiv_symm_apply (I := I) (J := 𝓘(ℝ, A × V)) _ _).trans
      ((D.linearModelMap_linearModelRepresentation k x).trans (tangentSpaceProdEquiv_apply _ _))
  rw [linearModelEquiv_apply, linearModelEquiv_apply, h, mfderiv_smul_mfderiv_mk_one_zero]

/-! ### The fibre directions and the orbit directions at `[1, 0]` -/

/-- **The fibre directions at `[1, 0]`.** The linear map `p ↦ dπ_(1, 0, 0) (0, p)` from `A × V`
to the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`. -/
def fiberTangentMap :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    (A × V) →ₗ[ℝ] TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) :=
  D.mkTangentMap ∘ₗ LinearMap.inr ℝ (GroupLieAlgebra I G) (A × V)

theorem fiberTangentMap_def :
    D.fiberTangentMap = D.mkTangentMap ∘ₗ LinearMap.inr ℝ (GroupLieAlgebra I G) (A × V) :=
  (rfl)

theorem fiberTangentMap_apply (p : A × V) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.fiberTangentMap p =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (0, p)) :=
  (rfl)

/-- **The orbit directions at `[1, 0]`.** The linear map `ξ ↦ dπ_(1, 0, 0) (ξ, 0)` from `𝔤` to
the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`: the differential at
`1` of `g ↦ [g, 0] = g • [1, 0]`. -/
def orbitTangentMap :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    GroupLieAlgebra I G →ₗ[ℝ] TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) :=
  D.mkTangentMap ∘ₗ LinearMap.inl ℝ (GroupLieAlgebra I G) (A × V)

theorem orbitTangentMap_def :
    D.orbitTangentMap = D.mkTangentMap ∘ₗ LinearMap.inl ℝ (GroupLieAlgebra I G) (A × V) :=
  (rfl)

theorem orbitTangentMap_apply (ξ : GroupLieAlgebra I G) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.orbitTangentMap ξ =
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (ξ, 0)) :=
  (rfl)

/-- **The fibre directions are equivariant.** For `k ∈ K`, the differential at `[1, 0]` of
`y ↦ k • y` sends `dπ_(1, 0, 0) (0, p)` to `dπ_(1, 0, 0) (0, k • p)`. -/
theorem fiberTangentMap_smul (k : K) (p : A × V) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    D.fiberTangentMap (k • p) =
      mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y)
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V)))
        (D.fiberTangentMap p) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  rw [fiberTangentMap_apply, fiberTangentMap_apply, mfderiv_smul_mfderiv_mk_one_zero]
  congr 1
  -- The differential of `(g, p) ↦ (k g k⁻¹, k • p)` at `(1, 0, 0)` sends `(0, p)` to
  -- `(Ad_k 0, k • p) = (0, k • p)`.
  have h := D.tangentSpaceProdEquiv_mfderiv_conj_smul_one_zero k
    ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).apply_symm_apply (0, p))
  rw [map_zero, ← D.fiberDistribMulAction_smul] at h
  exact (tangentSpaceProdEquiv_symm_apply _ _).trans
    (h.symm.trans (tangentSpaceProdEquiv_apply _ _))

/-- **The fibre directions are independent.** `p ↦ dπ_(1, 0, 0) (0, p)` is injective, since the
kernel of `dπ` at `(1, 0, 0)` is `𝔥 × 0`. -/
theorem injective_fiberTangentMap : Function.Injective D.fiberTangentMap := by
  rw [← LinearMap.ker_eq_bot, fiberTangentMap_def, LinearMap.ker_comp, ker_mkTangentMap,
    eq_bot_iff]
  exact fun p hp ↦ (Submodule.mem_prod.1 (Submodule.mem_comap.1 hp)).2

/-- **The fibre directions are a complement of the orbit directions.** In the tangent space of
`G ×_K (A × V)` at `[1, 0]`, the directions `dπ_(1, 0, 0) (ξ, 0)`, `ξ ∈ 𝔤`, and the directions
`dπ_(1, 0, 0) (0, p)`, `p ∈ A × V`, span complementary subspaces. -/
theorem isCompl_range_orbitTangentMap_range_fiberTangentMap :
    IsCompl (LinearMap.range D.orbitTangentMap) (LinearMap.range D.fiberTangentMap) := by
  -- The kernel `𝔥 × 0` of the surjective map `mkTangentMap` lies in `𝔤 × 0`.
  have hker : LinearMap.ker D.mkTangentMap ≤
      LinearMap.range (LinearMap.inl ℝ (GroupLieAlgebra I G) (A × V)) := by
    rw [ker_mkTangentMap, LinearMap.range_inl]
    exact fun y hy ↦ (Submodule.mem_bot ℝ).1 (Submodule.mem_prod.1 hy).2
  have hc := LinearMap.isCompl_range_inl_inr (R := ℝ) (M := GroupLieAlgebra I G) (M₂ := A × V)
  rw [orbitTangentMap_def, fiberTangentMap_def, LinearMap.range_comp, LinearMap.range_comp]
  exact ⟨Submodule.disjoint_map_of_ker_le_left hc.disjoint hker,
    Submodule.codisjoint_map D.surjective_mkTangentMap hc.codisjoint⟩

/-- **Equivariance of the fibre directions, after a linear map.** Let `T` be a linear map from the
tangent space of `G ×_K (A × V)` at `[1, 0]` to a real module `W`, and for each `k ∈ K` let `R k`
be a linear endomorphism of `W`, such that `T` takes the differential at `[1, 0]` of `y ↦ k • y`
to `R k`. Then `T (dπ_(1, 0, 0) (0, k • p)) = R k (T (dπ_(1, 0, 0) (0, p)))`. -/
theorem map_fiberTangentMap_smul {W : Type*} [AddCommGroup W] [Module ℝ W] :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    ∀ (T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) →ₗ[ℝ] W)
      (R : K → W →ₗ[ℝ] W),
      (∀ (k : K) u,
        T (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun y : BalancedProduct K K.RightTranslation (A × V) ↦ (k : G) • y)
          (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) u) =
          R k (T u)) →
      ∀ (k : K) (p : A × V), T (D.fiberTangentMap (k • p)) = R k (T (D.fiberTangentMap p)) := by
  intro T R hT k p
  rw [fiberTangentMap_smul, hT]

/-- **The fibre directions are a complement of the orbit directions, after a linear
isomorphism.** Let `T` be a linear isomorphism from the tangent space of `G ×_K (A × V)` at
`[1, 0]` to a real module `W`, and let `f : 𝔤 →ₗ[ℝ] W` be the composite of
`ξ ↦ dπ_(1, 0, 0) (ξ, 0)` with `T`. Then the range of `f` and the range of
`p ↦ T (dπ_(1, 0, 0) (0, p))` are complements in `W`. -/
theorem isCompl_range_range_comp_fiberTangentMap {W : Type*} [AddCommGroup W] [Module ℝ W] :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    ∀ (T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk K (K.toRightTranslation (1 : G)) ((0 : A), (0 : V))) ≃ₗ[ℝ] W)
      (f : GroupLieAlgebra I G →ₗ[ℝ] W),
      T.toLinearMap ∘ₗ D.orbitTangentMap = f →
      IsCompl (LinearMap.range f) (LinearMap.range (T.toLinearMap ∘ₗ D.fiberTangentMap)) := by
  intro T f hT
  rw [← hT, LinearMap.range_comp, LinearMap.range_comp]
  exact Submodule.isCompl_map T D.isCompl_range_orbitTangentMap_range_fiberTangentMap

end LocalModelData

end SymplecticGeometry

end
