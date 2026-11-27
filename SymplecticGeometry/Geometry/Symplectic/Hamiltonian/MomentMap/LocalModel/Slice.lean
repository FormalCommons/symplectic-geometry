/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Hamiltonian.MomentMap.LocalModel.Action
public import SymplecticGeometry.Geometry.Lie.GroupLieAlgebra.Normed
public import TauCeti.Geometry.Lie.Subgroup.BalancedProduct
import SymplecticGeometry.Geometry.Lie.Subgroup.BalancedProduct

/-!
# Exponential coordinates on the local model near `[1, 0]`

Let `D : SymplecticGeometry.LocalModelData K V A` be the data of the Marle–Guillemin–Sternberg
local model `Y = G ×_K (A × V)`, with the charts
`TauCeti.BalancedProduct.rightTranslationChartedSpace`. For an injective linear map
`j : C → 𝔤` whose image is a complement of `𝔥` in `𝔤`, such as the inclusion of `𝔪 ⊕ 𝔮`
(`SymplecticGeometry.LocalModelData.isCompl_𝔥_sup`), the map `(w, p) ↦ [exp (j w), p]` from
`C × (A × V)` to `Y` is a local diffeomorphism at `0`. These are coordinates on `Y` near `[1, 0]`
in which the fibre coordinate is `p` itself.

This is the case `Z = A × V`, `z = 0` of
`TauCeti.BalancedProduct.isLocalDiffeomorphAt_mk_mulInvariantExp`: the point `0` is fixed by the
linear action of `K`, and `𝔥` is the image of the Lie algebra of `K`.

## Main results

* `SymplecticGeometry.LocalModelData.isLocalDiffeomorphAt_mk_mulInvariantExp`: the map
  `(w, p) ↦ [exp (j w), p]` is a local diffeomorphism at `0`.
* `SymplecticGeometry.LocalModelData.isLocalDiffeomorphAt_mk_mulInvariantExp_submodule`: the
  same for a complement `𝔠` of `𝔥` in `𝔤`, with `j` the inclusion of `𝔠`.

## References

* [V. Guillemin and S. Sternberg][GuilleminSternberg1990]
* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985).
-/

public section

open Function TauCeti
open scoped Manifold ContDiff GroupLieAlgebra

namespace SymplecticGeometry

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace LocalModelData

variable {K : Subgroup G} [IsClosed (K : Set G)] [CompactSpace K] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  (D : LocalModelData (I := I) K (F := F) V A)
  {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- **Exponential coordinates on the local model near `[1, 0]`.** For an injective linear map
`j : C → 𝔤` whose image is a complement of `𝔥`, the map `(w, p) ↦ [exp (j w), p]` from
`C × (A × V)` to `G ×_K (A × V)` is a local diffeomorphism at `0`. -/
theorem isLocalDiffeomorphAt_mk_mulInvariantExp {j : C →L[ℝ] E} (hj : Injective j)
    (hcompl : IsCompl D.𝔥 (LinearMap.range j.toLinearMap)) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    IsLocalDiffeomorphAt 𝓘(ℝ, C × (A × V))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
      (fun p : C × (A × V) ↦ BalancedProduct.mk K
        (K.toRightTranslation (mulInvariantExp (I := I) (j p.1 : GroupLieAlgebra I G))) p.2)
      0 := by
  let := D.fiberDistribMulAction
  have := D.contMDiffSMul_fiberDistribMulAction
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact BalancedProduct.isLocalDiffeomorphAt_mk_mulInvariantExp F hj
    (D.range_groupLieAlgebraMap_subtype ▸ hcompl) (z := ((0 : A), (0 : V))) fun k ↦ smul_zero k

/-- **Exponential coordinates on the local model near `[1, 0]`, for a complement of `𝔥`.** For a
complement `𝔠` of `𝔥` in `𝔤`, such as `𝔪 ⊕ 𝔮` (`SymplecticGeometry.LocalModelData.isCompl_𝔥_sup`),
with the norm of `𝔤` (`GroupLieAlgebra.instNormedAddCommGroup`), the map
`(w, p) ↦ [exp w, p]` from `𝔠 × (A × V)` to `G ×_K (A × V)` is a local diffeomorphism at `0`. -/
theorem isLocalDiffeomorphAt_mk_mulInvariantExp_submodule
    {𝔠 : Submodule ℝ (GroupLieAlgebra I G)} (h𝔠 : IsCompl D.𝔥 𝔠) :
    letI := D.fiberDistribMulAction
    haveI := D.contMDiffSMul_fiberDistribMulAction
    letI := BalancedProduct.rightTranslationChartedSpace K (A × V) I 𝓘(ℝ, A × V) F
    IsLocalDiffeomorphAt 𝓘(ℝ, 𝔠 × (A × V))
      𝓘(ℝ, ProperSMul.QuotientModelSpace F (E × (A × V))) ∞
      (fun p : 𝔠 × (A × V) ↦ BalancedProduct.mk K
        (K.toRightTranslation (mulInvariantExp (I := I) (p.1 : GroupLieAlgebra I G))) p.2)
      0 :=
  D.isLocalDiffeomorphAt_mk_mulInvariantExp (j := 𝔠.subtypeL) Subtype.val_injective
    (by convert h𝔠 using 1; exact 𝔠.range_subtype)

end LocalModelData

end SymplecticGeometry

end
