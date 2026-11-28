/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.TangentSpace
import SymplecticGeometry.Geometry.Manifold.GroupAction.LinearTube

import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import SymplecticGeometry.Topology.Algebra.Module.Alternating.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# An equivariant local diffeomorphism from a local model at a point to `M`

Let `x` be a point of a `G`-manifold `M` whose stabilizer `H = G_x` is compact, let
`D : SymplecticGeometry.LocalModelData H V A` be data of a Marle–Guillemin–Sternberg local model
`Y = G ×_H (A × V)` over `H`, and let `T : T_{[1, 0]} Y ≃ T_x M` be a linear isomorphism that is
`H`-equivariant and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)`. This file builds from `T` a
`G`-equivariant map `Ψ : Y → M`, with `Ψ [g, 0] = g • x`, that is smooth and a local
diffeomorphism near the zero section and has differential `T` at `[1, 0]`. For the local model
`SymplecticGeometry.LocalModelData.ofPoint …` of a Hamiltonian `G`-manifold at `x`,
`SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint` gives such a `T`,
and the map is then the one that a Moser argument corrects into a local symplectomorphism.

The map is the tube map along a linear fibre of
`Geometry/Manifold/GroupAction/LinearTube.lean`,
`SymplecticGeometry.LinearizingChart.linearTubeMap`, for a linearizing chart at `x`
(`SymplecticGeometry.LinearizingChart.nonempty`) and the fibre directions
`L p = T (dπ_(1, 0, 0) (0, p))` read in `T_x M`
(`SymplecticGeometry.LocalModelData.fiberTangentMap`). The map `L` is `H`-equivariant by
`SymplecticGeometry.LocalModelData.fiberTangentMap_smul` and the equivariance of `T`, injective
since `T` and `fiberTangentMap` are, and its range is a complement of `𝔤 · x`
(`SymplecticGeometry.LocalModelData.isCompl_range_range_comp_fiberTangentMap`).
So `SymplecticGeometry.LinearizingChart.exists_isLocalDiffeomorphAt_linearTubeMap` gives the
neighbourhood `Z` of `0` on which the map is a local diffeomorphism. Its differential at `[1, 0]`
sends `dπ_(1, 0, 0) (ξ, p)` to `ξ_M(x) + L p`
(`SymplecticGeometry.LinearizingChart.mfderiv_linearTubeMap_mfderiv_quotientMk`), and so does
`T`; since `dπ_(1, 0, 0)` is onto (`SymplecticGeometry.LocalModelData.surjective_mkTangentMap`),
the two agree.

Let `σ` be a `G`-invariant two-form on `M`. An equivariant `Ψ₀` with `Ψ₀ [1, 0] = x`,
differentiable at `[1, 0]`, whose differential there takes `σ` at `x` to the descended form `ω`
at `[1, 0]` (as the differential `T` given by
`SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint` does), pulls `σ` back
to `ω` at every point `[g, 0]` of the zero section. At `[1, 0]` this is the hypothesis on the
differential; at `[g, 0] = g • [1, 0]` it follows from the invariance of `σ` and of `ω`
(`TauCeti.CotangentBundle.mpullback_smul_balancedProductInducedForm`) by
`TauCeti.mpullback_apply_smul_eq_of_apply_eq`. These are the forms that the equivariant relative
Moser theorem `TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_of_eq_along` compares
along the zero section.

## Main results

* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorphAt`: the equivariant map
  `Ψ : Y → M` with `Ψ [g, 0] = g • x`, smooth and a local diffeomorphism at the classes `[g, p]`
  with `p` in an open `H`-invariant neighbourhood of `0`, and with differential `T` at `[1, 0]`.
* `SymplecticGeometry.LocalModelData.mpullback_apply_mk_zero_eq_descendedForm`,
  `SymplecticGeometry.LocalModelData.eval₂_mfderiv_mk_zero_eq_eval₂_descendedForm`: such a
  `Ψ₀` pulls `σ` back to `ω` at every point `[g, 0]`, as forms and on pairs of tangent vectors.
* `SymplecticGeometry.LocalModelData.mpullback_subtypeVal_apply_mk_zero_eq`: the same for the
  restrictions to an open set of `Y` that contains the zero section and on which `Ψ₀` is smooth.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Function MulAction TauCeti TauCeti.Lie TauCeti.Manifold TauCeti.CotangentBundle
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [IsClosed (stabilizer G x : Set G)] [CompactSpace (stabilizer G x)]
  [ChartedSpace F (stabilizer G x)] [LieGroup 𝓘(ℝ, F) ∞ (stabilizer G x)]
  [ContMDiffSMul 𝓘(ℝ, F) I ∞ (stabilizer G x) G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) (stabilizer G x) (F := F) V A)

namespace LocalModelData

/-- **An equivariant local diffeomorphism from a local model at `x` to `M`.** Let `D` be data of
a local model `Y = G ×_H (A × V)` whose subgroup `H = G_x` is the stabilizer of `x`, and let
`T : T_{[1, 0]} Y ≃ T_x M` be a linear isomorphism that intertwines the differential at `[1, 0]` of
`y ↦ k • y` with `dk_x` for each `k ∈ H`, and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)` for each
`ξ ∈ 𝔤`. Then there are an open `H`-invariant neighbourhood `Z` of `0` in `A × V` and a
`G`-equivariant map `Ψ : Y → M` with `Ψ [g, 0] = g • x`, which is smooth and a local
diffeomorphism at every class `[g, p]` with `p ∈ Z`, and whose differential at `[1, 0]` is `T`. -/
theorem exists_isLocalDiffeomorphAt :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    ∀ T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) ≃ₗ[ℝ] TangentSpace I' x,
      (∀ (k : stabilizer G x) u,
        T (D.tangentRepresentationOneZero k u) =
          tangentRepresentation (fun (g : G) _ ↦
            ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x) k
            (T u)) →
      (∀ ξ : GroupLieAlgebra I G,
        T (D.orbitTangentMap ξ) = InfinitesimalAction.fundamental I G I' M ξ x) →
      ∃ (Z : Set (A × V))
        (Ψ : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) → M),
        IsOpen Z ∧ (0 : A × V) ∈ Z ∧ (∀ (k : stabilizer G x) {p : A × V}, p ∈ Z → k • p ∈ Z) ∧
        (∀ (g : G) {p : A × V}, p ∈ Z →
          ContMDiffAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ
            (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p)) ∧
        (∀ (g : G) y, Ψ (g • y) = g • Ψ y) ∧
        (∀ g : G, Ψ (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) 0) = g • x) ∧
        (∀ (g : G) {p : A × V}, p ∈ Z →
          IsLocalDiffeomorphAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞ Ψ
            (BalancedProduct.mk _ ((stabilizer G x).toRightTranslation g) p)) ∧
        ∀ u, mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u = T u := by
  intro T hTk hTξ
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  let e : LinearizingChart G I' x :=
    Classical.choice (LinearizingChart.nonempty I (isCompact_iff_compactSpace.2 ‹_›))
  -- The fibre directions, read in `T_x M` through `T`.
  let L : (A × V) →L[ℝ] E' :=
    LinearMap.toContinuousLinearMap (T.toLinearMap ∘ₗ D.fiberTangentMap : (A × V) →ₗ[ℝ] E')
  have hLapply (p : A × V) : L p = T (D.fiberTangentMap p) := rfl
  have hL (k : stabilizer G x) (p : A × V) :
      L (k • p) = mfderiv I' I' (fun y : M ↦ (k : G) • y) x (L p) := by
    rw [hLapply, hLapply, fiberTangentMap_smul, hTk]
    rw [tangentRepresentation_apply]
    -- The sides differ only in how the vector is typed: in `T_x M`, or in `E'`, of which `T_x M`
    -- is a type synonym.
    rfl
  have hLi : Injective L := T.injective.comp D.injective_fiberTangentMap
  have hV : IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)
      (L : (A × V) →ₗ[ℝ] E').range := by
    rw [InfinitesimalAction.orbitTangent_eq_range]
    exact D.isCompl_range_range_comp_fiberTangentMap T _
      (LinearMap.ext fun ξ ↦ (hTξ ξ).trans (InfinitesimalAction.eval_apply _ x ξ).symm)
  obtain ⟨Z, hZo, hZ0, hZk, -, hZd⟩ :=
    e.exists_isLocalDiffeomorphAt_linearTubeMap hL F hLi hV
  refine ⟨Z, e.linearTubeMap hL, hZo, hZ0, hZk, fun g p hp ↦ (hZd g hp).contMDiffAt,
    e.linearTubeMap_smul hL, e.linearTubeMap_mk_zero hL, hZd, fun u ↦ ?_⟩
  obtain ⟨⟨ξ, p⟩, rfl⟩ := D.surjective_mkTangentMap u
  have hsplit : D.mkTangentMap (ξ, p) = D.orbitTangentMap ξ + D.fiberTangentMap p := by
    rw [orbitTangentMap_def, fiberTangentMap_def, LinearMap.comp_apply, LinearMap.comp_apply,
      ← map_add]
    simp
  have hT : T (D.mkTangentMap (ξ, p)) =
      HAdd.hAdd (α := TangentSpace I' x) (β := TangentSpace I' x)
        (InfinitesimalAction.fundamental I G I' M ξ x) (L p) := by
    rw [hsplit, map_add, hTξ, hLapply]
  rw [hT, mkTangentMap_apply, InfinitesimalAction.fundamental_apply]
  -- That lemma differentiates along the projection of `H.RightTranslation × (A × V)`, which is
  -- `(g, p) ↦ [g, p]` on `G × (A × V)` with the same charts; what is left is the reading of
  -- `(ξ, p)` as a tangent vector of the product.
  refine Eq.trans ?_ (e.mfderiv_linearTubeMap_mfderiv_quotientMk hL F ξ p)
  congr 2
  exact tangentSpaceProdEquiv_symm_apply _ _

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M] in
/-- **The tube map pulls `σ` back to the descended form along the zero section**, as an equality
of the pulled-back form and the descended form `ω` at each point `[g, 0]`. Let `σ` be a two-form
on `M` invariant under the action of `G`, and let `Ψ₀ : Y → M` be a `G`-equivariant map with
`Ψ₀ [1, 0] = x`, differentiable at `[1, 0]`, whose differential `dΨ₀` at `[1, 0]` satisfies
`σ_x (dΨ₀ u, dΨ₀ v) = ω_{[1, 0]} (u, v)`. Then the pullback of `σ` along `Ψ₀` is `ω` at every
point `[g, 0]` of the zero section. -/
theorem mpullback_apply_mk_zero_eq_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
      ∀ {Ψ₀ : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) → M},
      (∀ (g : G) y, Ψ₀ (g • y) = g • Ψ₀ y) →
      Ψ₀ (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
        ((0 : A), (0 : V))) = x →
      MDifferentiableAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) →
      (∀ u v, SmoothBundleForm.eval₂ σ x
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) u)
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) v) =
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) →
      ∀ g : G, mpullback 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀ σ.val
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
            ((0 : A), (0 : V))) =
        (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
            D.mpullback_smul_mpullback_snd_constSmooth
            D.isMomentMap_mpullback_snd_constSmooth).val
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
            ((0 : A), (0 : V))) := by
  intro σ hσ Ψ₀ hΨ hΨ1 hdiff hT g
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  have := BalancedProduct.contMDiffSMul_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  set y₁ := BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
    ((0 : A), (0 : V))
  have hmk (g : G) : g • y₁ = BalancedProduct.mk (stabilizer G x)
      ((stabilizer G x).toRightTranslation g) ((0 : A), (0 : V)) := by
    rw [BalancedProduct.smul_mk_toRightTranslation, mul_one]
  -- At `[1, 0]` this is the hypothesis on the differential.
  have h₁ : mpullback _ I' Ψ₀ σ.val y₁ =
      (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
        D.mpullback_smul_mpullback_snd_constSmooth
        D.isMomentMap_mpullback_snd_constSmooth).val y₁ := by
    refine ContinuousAlternatingMap.ext_fin_two fun u v ↦ ?_
    rw [mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
      ← hT, hΨ1]
  -- At `[g, 0] = g • [1, 0]` it follows by the invariance of `σ` and of the descended form.
  have hω := (SmoothForm.mpullback_eq_iff _).1 (mpullback_smul_balancedProductInducedForm
    (hf := D.contMDiff_covectorCLM) (hfK := D.covectorCLM_smul)
    (hσK := D.mpullback_smul_mpullback_snd_constSmooth)
    (hμ := D.isMomentMap_mpullback_snd_constSmooth) g)
  have hσg := (SmoothForm.mpullback_eq_iff _).1 (hσ g)
  rw [← hmk]
  have := ContMDiffSMul.contMDiffConstSMul I (n := 1) (G := G)
    (I' := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))))
    (M := BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V))
  have := ContMDiffSMul.contMDiffConstSMul I (I' := I') (n := 1) (G := G) (M := M)
  exact mpullback_apply_smul_eq_of_apply_eq g (hΨ g) hσg hω hdiff h₁

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M] in
/-- **The tube map pulls `σ` back to the descended form along the zero section**, on pairs of
tangent vectors: in the setting of
`SymplecticGeometry.LocalModelData.mpullback_apply_mk_zero_eq_descendedForm`, for every `g ∈ G`
and all tangent vectors `u`, `v` of `Y` at `[g, 0]`,
`σ_{Ψ₀ [g, 0]} (dΨ₀ u, dΨ₀ v) = ω_{[g, 0]} (u, v)`. -/
theorem eval₂_mfderiv_mk_zero_eq_eval₂_descendedForm :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
      ∀ {Ψ₀ : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) → M},
      (∀ (g : G) y, Ψ₀ (g • y) = g • Ψ₀ y) →
      Ψ₀ (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
        ((0 : A), (0 : V))) = x →
      MDifferentiableAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) →
      (∀ u v, SmoothBundleForm.eval₂ σ x
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) u)
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) v) =
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) →
      ∀ (g : G) u v,
        SmoothBundleForm.eval₂ σ
            (Ψ₀ (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
              ((0 : A), (0 : V))))
            (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
              (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
                ((0 : A), (0 : V))) u)
            (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
              (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
                ((0 : A), (0 : V))) v) =
          SmoothBundleForm.eval₂
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth)
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
              ((0 : A), (0 : V))) u v := by
  intro σ hσ Ψ₀ hΨ hΨ1 hdiff hT g u v
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  rw [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, ← mpullback_apply_pair,
    D.mpullback_apply_mk_zero_eq_descendedForm hσ hΨ hΨ1 hdiff hT g]

omit [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M] in
/-- **The tube map pulls `σ` back to the descended form along the zero section**, on an open set:
in the setting of `SymplecticGeometry.LocalModelData.mpullback_apply_mk_zero_eq_descendedForm`,
let `U` be an open set of `Y` that contains the zero section and on which `Ψ₀` is smooth (this
replaces the differentiability of `Ψ₀` at `[1, 0]`). Then
the pullbacks of `σ` along `Ψ₀` restricted to `U`, and of `ω` along the inclusion of `U`, agree at
every point `[g, 0]`. This is the hypothesis `heq` of
`TauCeti.SmoothEmbedding.exists_equivariant_diffeomorph_opens_of_eq_along` for the zero section. -/
theorem mpullback_subtypeVal_apply_mk_zero_eq :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    haveI := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
      (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
    ∀ {σ : SmoothTwoForm I' M}, (∀ g : G, SmoothForm.mpullback (fun y : M ↦ g • y)
        (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) σ = σ) →
      ∀ {Ψ₀ : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) → M},
      (∀ (g : G) y, Ψ₀ (g • y) = g • Ψ₀ y) →
      Ψ₀ (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
        ((0 : A), (0 : V))) = x →
      (∀ u v, SmoothBundleForm.eval₂ σ x
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) u)
          (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
            (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
              ((0 : A), (0 : V))) v) =
        SmoothBundleForm.eval₂
            (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
              D.mpullback_smul_mpullback_snd_constSmooth
              D.isMomentMap_mpullback_snd_constSmooth)
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u v) →
      ∀ (U : TopologicalSpace.Opens
          (BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V)))
        (hU : ∀ g : G, BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation g)
          ((0 : A), (0 : V)) ∈ U)
        (hΨU : ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' ∞
          (Ψ₀ ∘ (Subtype.val : U → _))) (g : G),
        (SmoothForm.mpullback _ hΨU σ).val ⟨_, hU g⟩ =
          (SmoothForm.mpullback (Subtype.val : U → _) contMDiff_subtypeVal
              (balancedProductInducedForm I G _ D.contMDiff_covectorCLM D.covectorCLM_smul
                D.mpullback_smul_mpullback_snd_constSmooth
                D.isMomentMap_mpullback_snd_constSmooth)).val
            ⟨_, hU g⟩ := by
  intro σ hσ Ψ₀ hΨ hΨ1 hT U hU hΨU g
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  let := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I 𝓘(ℝ, A × V) F
  have := BalancedProduct.isManifold_rightTranslation (K := stabilizer G x) (Z := A × V)
    (I := I) (IZ := 𝓘(ℝ, A × V)) (F := F)
  have hdiff : MDifferentiableAt 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) I' Ψ₀
      (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
        ((0 : A), (0 : V))) :=
    (contMDiffAt_subtype_iff.1 (hΨU ⟨_, hU 1⟩)).mdifferentiableAt (by simp)
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  rw [SmoothForm.mpullback_comp_subtypeVal_apply, SmoothForm.coe_mpullback_subtype_val_apply]
  refine (mpullback_apply (I := 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))) Ψ₀ σ.val _
    w).symm.trans ?_
  exact DFunLike.congr_fun (D.mpullback_apply_mk_zero_eq_descendedForm hσ hΨ hΨ1 hdiff hT g) w

end LocalModelData

end SymplecticGeometry

end
