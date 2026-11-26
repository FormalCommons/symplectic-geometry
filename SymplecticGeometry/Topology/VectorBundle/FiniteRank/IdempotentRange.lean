/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.VectorBundle.Core.Basic
public import TauCeti.Analysis.Normed.Operator.IdempotentRange
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# The rank of an idempotent bundle endomorphism

For a coordinate endomorphism `P` of a vector-bundle core (`VectorBundleCore.CoordinateHom Z Z`)
whose fibre maps are idempotent, over a complete model fibre, the rank of the range of
`P.fiberMap x` is a locally constant function of the base point. We apply this to an endomorphism
`P` of one of Tau Ceti's finite-rank cores (`TauCeti.FiniteRankBundleCore`) with `P ≫ P = P`:
its rank is locally constant, and constant over a preconnected base. This constant rank is what
one needs to make the range of `P` into a finite-rank core of its own, since such a core has the
same rank at every point. Over a disconnected base the rank of `P` may differ from one component
to another.

The proof applies Tau Ceti's `TauCeti.isLocallyConstant_finrank_range`, for a continuous family of
projections on a fixed space, to the chart operator of `P` in the chart of `Z` at a point `x₀`.
On that chart's base set this operator is continuous and idempotent, and it is conjugate to the
fibre map of `P` by transition maps, so it has the same rank
(`VectorBundleCore.finrank_range_inChartCoordinates`). Tau Ceti's
`TauCeti.Topology.VectorBundle.ConstantRank` compares ranks through charts in the same way
(`ContinuousLinearMap.finrank_range_inCoordinates`).

## Main results

* `VectorBundleCore.CoordinateHom.finrank_range_operator`: a chart operator of a coordinate
  morphism has the rank of the fibre map.
* `VectorBundleCore.CoordinateHom.isLocallyConstant_finrank_range_fiberMap`: the rank of a
  coordinate endomorphism with idempotent fibre maps is locally constant on the base.
* `TauCeti.FiniteRankBundleCore.isIdempotentElem_fiberMap`: the fibre maps of an idempotent
  endomorphism of a finite-rank core are idempotent.
* `TauCeti.FiniteRankBundleCore.isLocallyConstant_finrank_range_fiberMap`: the rank of an
  idempotent endomorphism of a finite-rank core is locally constant on the base.
* `TauCeti.FiniteRankBundleCore.finrank_range_fiberMap_eq`: over a preconnected base it is
  constant.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6.
-/

public section

open CategoryTheory Topology Filter

namespace VectorBundleCore.CoordinateHom

variable {𝕜 B F G ι κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {Z : VectorBundleCore 𝕜 B F ι} {W : VectorBundleCore 𝕜 B G κ}

/-- At a point `y` of the source chart `i` and the target chart `j`, the chart operator of a
coordinate morphism has the rank of its fibre map at `y`. -/
theorem finrank_range_operator (f : CoordinateHom Z W) (i : ι) (j : κ)
    (y : ↥(Z.baseSet i ∩ W.baseSet j)) :
    Module.finrank 𝕜 (f.operator i j y).range = Module.finrank 𝕜 (f.fiberMap y.val).range := by
  rw [operator_eq, Z.finrank_range_inChartCoordinates y.property.1 y.property.2]

/-- Over a complete model fibre, the rank of a coordinate endomorphism `P` whose fibre maps are
idempotent, that is the dimension of the range of `P.fiberMap x`, is a locally constant function
of `x`. -/
theorem isLocallyConstant_finrank_range_fiberMap [CompleteSpace F] (P : CoordinateHom Z Z)
    (hP : ∀ x, IsIdempotentElem (P.fiberMap x)) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 (P.fiberMap x).range := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  have hU : IsOpen (Z.baseSet (Z.indexAt x₀) ∩ Z.baseSet (Z.indexAt x₀)) :=
    (Z.isOpen_baseSet _).inter (Z.isOpen_baseSet _)
  have hx₀ : x₀ ∈ Z.baseSet (Z.indexAt x₀) ∩ Z.baseSet (Z.indexAt x₀) :=
    ⟨Z.mem_baseSet_at x₀, Z.mem_baseSet_at x₀⟩
  have hPP : P.comp P = P := fiberMap_injective <| funext fun x ↦ by
    rw [fiberMap_comp, ← ContinuousLinearMap.mul_def, (hP x).eq]
  have hidem (y) : IsIdempotentElem (P.operator (Z.indexAt x₀) (Z.indexAt x₀) y) :=
    (operator_comp P P _ _ _ y.property.1 y.property.1 y.property.2).symm.trans
      (congrArg (fun f ↦ f.operator (Z.indexAt x₀) (Z.indexAt x₀) y) hPP)
  have h := (IsLocallyConstant.iff_eventually_eq _).1
    (TauCeti.isLocallyConstant_finrank_range (P.operator _ _).continuous hidem) ⟨x₀, hx₀⟩
  rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x₀, hx₀⟩, eventually_map]
  filter_upwards [h] with y hy
  rw [← finrank_range_operator, hy, finrank_range_operator]

end VectorBundleCore.CoordinateHom

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [TopologicalSpace X]
  {E : FiniteRankBundleCore 𝕜 X} {P : E ⟶ E}

/-- The fibre maps of an idempotent endomorphism of a finite-rank core are idempotent. -/
theorem isIdempotentElem_fiberMap (hP : P ≫ P = P) (x : X) :
    IsIdempotentElem (P.fiberMap x) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, ← fiberMap_comp, hP]

variable [CompleteSpace 𝕜]

/-- The rank of an idempotent endomorphism `P` of a finite-rank core, that is the dimension of the
range of `P.fiberMap x`, is a locally constant function of `x`. -/
theorem isLocallyConstant_finrank_range_fiberMap (hP : P ≫ P = P) :
    IsLocallyConstant fun x ↦ Module.finrank 𝕜 (P.fiberMap x).range :=
  VectorBundleCore.CoordinateHom.isLocallyConstant_finrank_range_fiberMap P
    (isIdempotentElem_fiberMap hP)

/-- Over a preconnected base, an idempotent endomorphism `P` of a finite-rank core has the same
rank at every point. Without preconnectedness this fails: over a disconnected base `P` can be the
identity over one component and zero over another. -/
theorem finrank_range_fiberMap_eq [PreconnectedSpace X] (hP : P ≫ P = P) (x y : X) :
    Module.finrank 𝕜 (P.fiberMap x).range = Module.finrank 𝕜 (P.fiberMap y).range :=
  (isLocallyConstant_finrank_range_fiberMap hP).apply_eq_of_preconnectedSpace x y

end TauCeti.FiniteRankBundleCore

end
