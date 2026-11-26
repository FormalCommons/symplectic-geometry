/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.GroupAction.LinearTube
public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.OfPoint

/-!
# An equivariant local diffeomorphism from the local model at a point to `M`

Let `D = SymplecticGeometry.LocalModelData.ofPoint …` be the data of the
Marle–Guillemin–Sternberg local model `Y = G ×_H (A × V)` at a point `x` of a Hamiltonian
`G`-manifold `M` with compact stabilizer `H = G_x`, and let `T : T_{[1, 0]} Y ≃ T_x M` be a linear
isomorphism that is `H`-equivariant and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)`, such as
`SymplecticGeometry.LocalModelData.exists_linearEquiv_tangentSpace_ofPoint` gives. This file
builds from `T` a `G`-equivariant map `Ψ : Y → M`, with `Ψ [g, 0] = g • x`, that is smooth and a
local diffeomorphism near the zero section and has differential `T` at `[1, 0]`. It is the map
that a Moser argument then corrects into a local symplectomorphism.

The map is the tube map along a linear fibre of
`Geometry/Manifold/GroupAction/LinearTube.lean`,
`SymplecticGeometry.LinearizingChart.linearTubeMap`, for a linearizing chart at `x`
(`SymplecticGeometry.LinearizingChart.nonempty`) and the fibre directions
`L p = T (dπ_(1, 0, 0) (0, p))` read in `T_x M`
(`SymplecticGeometry.LocalModelData.fiberTangentMap`). The map `L` is `H`-equivariant by
`SymplecticGeometry.LocalModelData.fiberTangentMap_smul` and the equivariance of `T`, injective
since `T` and `fiberTangentMap` are, and its range is a complement of `𝔤 · x`
(`SymplecticGeometry.LocalModelData.isCompl_orbitTangent_range_linearEquiv_comp_fiberTangentMap`).
So `SymplecticGeometry.LinearizingChart.exists_isLocalDiffeomorphAt_linearTubeMap` gives the
neighbourhood `Z` of `0` on which the map is a local diffeomorphism. Its differential at `[1, 0]`
sends `dπ_(1, 0, 0) (ξ, p)` to `ξ_M(x) + L p`
(`SymplecticGeometry.LinearizingChart.mfderiv_linearTubeMap_mfderiv_quotientMk`), and so does
`T`; since `dπ_(1, 0, 0)` is onto (`SymplecticGeometry.LocalModelData.surjective_mkTangentMap`),
the two agree.

## Main results

* `SymplecticGeometry.LocalModelData.exists_isLocalDiffeomorphAt_ofPoint`: the equivariant map
  `Ψ : Y → M` with `Ψ [g, 0] = g • x`, smooth and a local diffeomorphism at the classes `[g, p]`
  with `p` in an open `H`-invariant neighbourhood of `0`, and with differential `T` at `[1, 0]`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Function MulAction TauCeti TauCeti.Lie TauCeti.Manifold
open scoped Manifold ContDiff

noncomputable section

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)} {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
  (hμ : σ.IsEquivariantMomentMap μ)
  [IsClosed (stabilizer G x : Set G)] [CompactSpace (stabilizer G x)]
  (d : EmbeddedLieSubgroupData I (stabilizer G x) F)
  {𝔪 𝔮 : Subrepresentation ((adjointRepresentation ℝ I G).comp (stabilizer G x).subtype)}
  (h𝔪 : Disjoint ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
    𝔪.toSubmodule)
  (h𝔪' : ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ⊔ 𝔪.toSubmodule =
    (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule)
  (h𝔮 : IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule 𝔮.toSubmodule)
  (eV : V ≃ₗ[ℝ] hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)
  (eA : A ≃ₗ[ℝ] Module.Dual ℝ 𝔪.toSubmodule)

namespace LocalModelData

/-- **An equivariant local diffeomorphism from the local model at `x` to `M`.** Let `D` be the
data of the local model at `x`, `Y = G ×_H (A × V)` with `H = G_x`, and let
`T : T_{[1, 0]} Y ≃ T_x M` be a linear isomorphism that intertwines the differential at `[1, 0]` of
`y ↦ k • y` with `dk_x` for each `k ∈ H`, and sends `dπ_(1, 0, 0) (ξ, 0)` to `ξ_M(x)` for each
`ξ ∈ 𝔤`, as `exists_linearEquiv_tangentSpace_ofPoint` provides. Then there are an open
`H`-invariant neighbourhood `Z` of `0` in `A × V` and a `G`-equivariant map `Ψ : Y → M` with
`Ψ [g, 0] = g • x`, which is smooth and a local diffeomorphism at every class `[g, p]` with
`p ∈ Z`, and whose differential at `[1, 0]` is `T`. -/
theorem exists_isLocalDiffeomorphAt_ofPoint :
    let _ := d.chartedSpace
    let _ := d.lieGroup
    let _ := d.contMDiffSMul (I'' := I) (M := G)
    let D := ofPoint hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace (stabilizer G x) (A × V) I
      𝓘(ℝ, A × V) F
    ∀ T : TangentSpace 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
        (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
          ((0 : A), (0 : V))) ≃ₗ[ℝ] TangentSpace I' x,
      (∀ (k : stabilizer G x) u,
        T (mfderiv 𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V)))
          (fun y : BalancedProduct (stabilizer G x) (stabilizer G x).RightTranslation (A × V) ↦
            (k : G) • y)
          (BalancedProduct.mk (stabilizer G x) ((stabilizer G x).toRightTranslation (1 : G))
            ((0 : A), (0 : V))) u) =
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
  intro _ _ _ D T hTk hTξ
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
      (L : (A × V) →ₗ[ℝ] E').range :=
    isCompl_orbitTangent_range_linearEquiv_comp_fiberTangentMap hσ hσG hμ d h𝔪 h𝔪' h𝔮 eV eA T
      hTξ
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

end LocalModelData

end SymplecticGeometry

end
