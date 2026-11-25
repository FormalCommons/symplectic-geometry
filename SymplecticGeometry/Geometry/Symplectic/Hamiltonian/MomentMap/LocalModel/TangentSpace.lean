/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Descent
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.LinearNormalForm

/-!
# The tangent space of `G ×_K (A × V)` at `[1, 0]` and the linear normal form

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the local model, with descended
form `ω = D.descendedForm` on `Y = G ×_K (A × V)` and projection `π : G × (A × V) → Y`. This file
identifies the tangent space of `Y` at `[1, 0]`, with `ω` and the action of `K`, with the linear
normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` of Tau Ceti's `MomentMap/LinearNormalForm.lean`.

The identification is `dπ_(1, 0, 0) ∘ D.linearModelMap`, with the tangent space of `G × (A × V)` at
`(1, 0, 0)` read as `𝔤 × A × V`. It is injective because the kernel of `dπ` at `(1, 0, 0)` is
`𝔥 × 0` (`SymplecticGeometry.LocalModelData.mem_ker_mfderiv_mk_one_zero_iff`), which meets the
range of `linearModelMap` only in `0`; it is surjective because `dπ` is, and that range is a
complement of `𝔥 × 0`. The form `ω` at `[1, 0]` evaluates on images under `dπ` as `D.form` at
`(1, 0, 0)`, which on the range of `linearModelMap` is the model's form. Finally,
`k ∈ K` fixes `[1, 0]`, and `(k • ·) ∘ π = π ∘ c_k` with `c_k (g, p) = (k g k⁻¹, k • p)`, whose
differential at `(1, 0, 0)` `linearModelMap` intertwines with the representation of `K` on the
model.

## Main definitions

* `SymplecticGeometry.LocalModelData.linearModelEquiv`: the linear equivalence from the linear
  normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` to the tangent space of `G ×_K (A × V)` at `[1, 0]`.

## Main results

* `SymplecticGeometry.LocalModelData.bijective_mfderiv_mk_linearModelMap`:
  `x ↦ dπ_(1, 0, 0) (linearModelMap x)` is bijective.
* `SymplecticGeometry.LocalModelData.eval₂_descendedForm_linearModelEquiv`: through
  `linearModelEquiv`, the descended form at `[1, 0]` is the form of the linear normal form model.
* `SymplecticGeometry.LocalModelData.linearModelEquiv_linearModelRepresentation`:
  `linearModelEquiv` takes the representation of `K` on the model to the differential at `[1, 0]`
  of the action of `K` on `G ×_K (A × V)`.

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

/-- **The linear normal form model spans the tangent space at `[1, 0]`.** The map
`x ↦ dπ_(1, 0, 0) (linearModelMap x)` from the linear normal form model `(𝔪 × 𝔪*) × (𝔮 × V)` to
the tangent space of `G ×_K (A × V)` at `[1, 0]`, where `π (g, p) = [g, p]`, is bijective. -/
theorem bijective_mfderiv_mk_linearModelMap :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    Function.Bijective fun x : (D.𝔪 × Module.Dual ℝ D.𝔪) × (D.𝔮 × V) ↦
      mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
        ((1 : G), ((0 : A), (0 : V)))
        ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm (D.linearModelMap x)) := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  let e : TangentSpace (I.prod 𝓘(ℝ, A × V)) ((1 : G), ((0 : A), (0 : V))) ≃L[ℝ]
      GroupLieAlgebra I G × (A × V) := tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))
  set dπ := mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
      ((1 : G), ((0 : A), (0 : V)))
  have hc := D.isCompl_range_linearModelMap (I := I)
  have hker (u) : dπ u = 0 ↔ e u ∈ D.𝔥.prod ⊥ := D.mem_ker_mfderiv_mk_one_zero_iff u
  have he (y : GroupLieAlgebra I G × (A × V)) :
      e ((tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm y) = y :=
    e.apply_symm_apply y
  refine ⟨fun x y hxy ↦ D.injective_linearModelMap ?_, fun w ↦ ?_⟩
  · -- `linearModelMap (x - y)` lies in the range of `linearModelMap` and in the kernel `𝔥 × 0`
    -- of `dπ`, so it vanishes.
    have hxy : dπ ((tangentSpaceProdEquiv _).symm (D.linearModelMap (x - y))) = 0 := by
      rw [map_sub]
      exact (congrArg _ (map_sub _ _ _)).trans ((map_sub _ _ _).trans (sub_eq_zero.2 hxy))
    rw [hker, he] at hxy
    exact sub_eq_zero.1 ((map_sub ..).symm.trans
      (Submodule.disjoint_def.1 hc.disjoint _ ⟨x - y, rfl⟩ hxy))
  · -- Write a preimage `u` of `w` as `linearModelMap x + h` with `h ∈ 𝔥 × 0`.
    obtain ⟨u, rfl⟩ := (BalancedProduct.isSubmersion_mk_toRightTranslation (K := K)
      (Z := A × V) (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)).surjective_mfderiv
      (x := ((1 : G), ((0 : A), (0 : V)))) (by simp) w
    obtain ⟨_, ⟨x, rfl⟩, h, hh, hu⟩ :=
      Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := e u))
    refine ⟨x, ?_⟩
    rw [← sub_eq_zero, ← map_sub, hker, map_sub, he, ← hu, sub_add_cancel_left]
    exact neg_mem hh

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
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
  LinearEquiv.ofBijective
    ((mfderiv (I.prod 𝓘(ℝ, A × V)) 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
      (fun p : G × (A × V) ↦ BalancedProduct.mk K (K.toRightTranslation p.1) p.2)
      ((1 : G), ((0 : A), (0 : V)))).toLinearMap ∘ₗ
      (tangentSpaceProdEquiv ((1 : G), ((0 : A), (0 : V)))).symm.toLinearMap ∘ₗ D.linearModelMap)
    D.bijective_mfderiv_mk_linearModelMap

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
  rw [linearModelEquiv_apply, linearModelEquiv_apply, h,
    ← mfderiv_comp_apply_of_eq _ (hπ _) (hc _) hfix, ← hcomp, mfderiv_comp_apply _ (hk _) (hπ _)]

end LocalModelData

end SymplecticGeometry

end
