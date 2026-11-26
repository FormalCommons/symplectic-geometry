/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.IdempotentRange
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# The rank of an idempotent endomorphism of a finite-rank core

For an endomorphism `P` of one of Tau Ceti's finite-rank cores `E` (`TauCeti.FiniteRankBundleCore`)
with `P ≫ P = P`, every fibre map `P.fiberMap x` is idempotent, and the rank of its range is a
locally constant function of the base point. Over a preconnected base it is therefore constant.
This constant rank is what one needs to make the range of `P` into a finite-rank core of its own,
since such a core has the same rank at every point. Over a disconnected base the rank of `P` may
differ from one component to another.

The proof applies Tau Ceti's `TauCeti.isLocallyConstant_finrank_range`, for a continuous family of
projections on a fixed space, to the chart operator of `P` in the chart of `E` at a point `x₀`. On
that chart's base set this operator is continuous and idempotent, and it is conjugate to the fibre
map of `P` by the transition maps of `E`, so it has the same rank. Tau Ceti's
`TauCeti.Topology.VectorBundle.ConstantRank` compares ranks through charts in the same way
(`ContinuousLinearMap.finrank_range_inCoordinates`).

## Main results

* `TauCeti.FiniteRankBundleCore.isIdempotentElem_fiberMap`: the fibre maps of an idempotent
  endomorphism are idempotent.
* `TauCeti.FiniteRankBundleCore.finrank_range_operator`: a chart operator of a morphism of
  finite-rank cores has the rank of the fibre map.
* `TauCeti.FiniteRankBundleCore.isLocallyConstant_finrank_range_fiberMap`: the rank of an
  idempotent endomorphism is locally constant on the base.
* `TauCeti.FiniteRankBundleCore.finrank_range_fiberMap_eq`: over a preconnected base it is
  constant.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

open CategoryTheory Topology Filter

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
  {E : FiniteRankBundleCore 𝕜 X} {P : E ⟶ E}

/-- The fibre maps of an idempotent endomorphism of a finite-rank core are idempotent. -/
theorem isIdempotentElem_fiberMap (hP : P ≫ P = P) (x : X) :
    IsIdempotentElem (P.fiberMap x) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ← fiberMap_comp, hP]

/-- At a point `y` of the source chart `i` and the target chart `j`, the chart operator of a
morphism of finite-rank cores has the rank of its fibre map at `y`. -/
theorem finrank_range_operator {A D : FiniteRankBundleCore 𝕜 X} (f : A ⟶ D) (i j : X)
    (y : ↥(A.core.baseSet i ∩ D.core.baseSet j)) :
    Module.finrank 𝕜 (f.operator i j y).range = Module.finrank 𝕜 (f.fiberMap y.val).range := by
  rw [VectorBundleCore.CoordinateHom.operator_eq, inChartCoordinates_core,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2
        (A.core.coordChange_bijective y.property.1 (A.mem_baseSet_self y.val)).2)]
  exact (Submodule.equivMapOfInjective _
    (D.core.coordChange_bijective (D.mem_baseSet_self y.val) y.property.2).1 _).finrank_eq.symm

variable [CompleteSpace 𝕜]

/-- The rank of an idempotent endomorphism `P` of a finite-rank core, that is the dimension of the
range of `P.fiberMap x`, is a locally constant function of `x`. -/
theorem isLocallyConstant_finrank_range_fiberMap (hP : P ≫ P = P) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 (P.fiberMap x).range := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  have hU : IsOpen (E.core.baseSet x₀ ∩ E.core.baseSet x₀) :=
    (E.core.isOpen_baseSet x₀).inter (E.core.isOpen_baseSet x₀)
  have hx₀ : x₀ ∈ E.core.baseSet x₀ ∩ E.core.baseSet x₀ :=
    ⟨E.mem_baseSet_self x₀, E.mem_baseSet_self x₀⟩
  have hidem (y) : IsIdempotentElem (P.operator x₀ x₀ y) := by
    rw [IsIdempotentElem, ContinuousLinearMap.mul_def, VectorBundleCore.CoordinateHom.operator_eq,
      ← E.core.inChartCoordinates_comp E.core E.core x₀ x₀ y.property.1,
      ← ContinuousLinearMap.mul_def, (isIdempotentElem_fiberMap hP y.val).eq]
  have h := (IsLocallyConstant.iff_eventually_eq _).1
    (isLocallyConstant_finrank_range (P.operator x₀ x₀).continuous hidem) ⟨x₀, hx₀⟩
  have hmap : Filter.map Subtype.val (𝓝 (⟨x₀, hx₀⟩ : ↥(E.core.baseSet x₀ ∩ E.core.baseSet x₀))) =
      𝓝 x₀ :=
    hU.isOpenEmbedding_subtypeVal.map_nhds_eq _
  rw [← hmap, eventually_map]
  filter_upwards [h] with y hy
  rw [← finrank_range_operator, hy, finrank_range_operator]

/-- Over a preconnected base, an idempotent endomorphism `P` of a finite-rank core has the same
rank at every point. Without preconnectedness this fails: over a disconnected base `P` can be the
identity over one component and zero over another. -/
theorem finrank_range_fiberMap_eq [PreconnectedSpace X] (hP : P ≫ P = P) (x y : X) :
    Module.finrank 𝕜 (P.fiberMap x).range = Module.finrank 𝕜 (P.fiberMap y).range :=
  (isLocallyConstant_finrank_range_fiberMap hP).apply_eq_of_preconnectedSpace x y

end TauCeti.FiniteRankBundleCore

end
