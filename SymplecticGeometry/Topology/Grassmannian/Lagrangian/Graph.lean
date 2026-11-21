/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import SymplecticGeometry.LinearAlgebra.Matrix.Rank
public import SymplecticGeometry.LinearAlgebra.Matrix.Symmetric
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Transverse
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Quotient
public import SymplecticGeometry.Topology.Instances.Matrix
public import TauCeti.Topology.Instances.Matrix

/-!
# The graph charts of the Lagrangian Grassmannian

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, with
the topology of orthogonal projections. A Lagrangian transverse to the horizontal subspace
`{y = 0}` is the graph `{(S y, y)}` of a unique symmetric matrix `S`, and one transverse to the
vertical subspace `{x = 0}` is the graph `{(x, S x)}` of a unique symmetric matrix. This file shows
that both descriptions are charts: partial homeomorphisms from `ℒ ι` onto the space
`selfAdjoint (Matrix ι ι ℝ)` of real symmetric matrices, defined on open sets.

For a unitary matrix `U = X + i Y`, the Lagrangian `unitaryFrame U` is transverse to `{y = 0}`
exactly when `Y` is invertible, and then its chart value is `X Y⁻¹`. Since `unitaryFrame` is an
open quotient map, this formula gives the openness and continuity that the charts need.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian.continuous_graphY`: the chart point `{(S y, y)}`
  depends continuously on `S`.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryFrame_eq_graphY_iff`: `unitaryFrame U` is
  `graphY S` iff `Im U` is invertible and `S = Re U (Im U)⁻¹`.
* `SymplecticGeometry.LagrangianGrassmannian.isOpenEmbedding_graphY`: `graphY` is an open
  embedding.
* `SymplecticGeometry.LagrangianGrassmannian.isOpen_setOf_isCompl`: the Lagrangians transverse to
  a given one form an open set.
* `SymplecticGeometry.LagrangianGrassmannian.graphYChart`: the chart on the Lagrangians
  transverse to `{y = 0}`, with inverse `graphY`; `unitaryFrame_mem_graphYChart_source_iff` says
  when a unitary frame lies in its source, and `coe_graphYChart_unitaryFrame` gives its value
  there.
* `SymplecticGeometry.LagrangianGrassmannian.graphChart`: the chart on the Lagrangians transverse
  to `{x = 0}`, with inverse `graph`.

The construction follows Tau Ceti's graph charts on finite Grassmannians,
`TauCeti.finiteGrassmannian.graphChart` (`TauCeti/Topology/Grassmannian/Graph.lean`), there
with frames in place of unitary frames.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set Topology

variable {ι : Type*} [Fintype ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Continuity of the chart points -/

/-- The chart point `{(S y, y)}` depends continuously on the symmetric matrix `S`. -/
@[fun_prop]
theorem continuous_graphY : Continuous (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) := by
  classical
  have h (S : selfAdjoint (Matrix ι ι ℝ)) :=
    isLagrangian_range_fromRows_one (isHermitian_iff_isSymm.1 S.property)
  have he : (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) = fun S ↦ ⟨_, h S⟩ :=
    funext fun S ↦ toSubmodule_injective (by
      rw [coe_graphY]
      exact (StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY (S : Matrix ι ι ℝ)).symm)
  rw [he]
  exact continuous_mk_range_fromRows continuous_subtypeVal continuous_const h

/-! ### Unitary frames transverse to the horizontal subspace -/

section DecidableEq

variable [DecidableEq ι]

/-- The frame `fromRows (Re U) (Im U)` of a unitary matrix spans a Lagrangian. -/
private theorem isLagrangian_range_fromRows_re_im (U : unitaryGroup ι ℂ) :
    (stdForm ι).IsLagrangian (LinearMap.range (toEuclideanLin
      (fromRows ((U : Matrix ι ι ℂ).map Complex.re) ((U : Matrix ι ι ℂ).map Complex.im)))) :=
  coe_unitaryFrame U ▸ (unitaryFrame U).isLagrangian

/-- The chart value `Re U (Im U)⁻¹` of a unitary matrix, which is symmetric since the frame
`fromRows (Re U) (Im U)` is Lagrangian. -/
private noncomputable def chartValue (U : unitaryGroup ι ℂ) : selfAdjoint (Matrix ι ι ℝ) :=
  ⟨(U : Matrix ι ι ℂ).map Complex.re * ((U : Matrix ι ι ℂ).map Complex.im)⁻¹,
    isHermitian_iff_isSymm.2 (isSymm_mul_nonsing_inv_of_transpose_mul_eq
      ((isLagrangian_range_fromRows_iff _ _).1 (isLagrangian_range_fromRows_re_im U)).2)⟩

/-- The Lagrangian framed by a unitary matrix `U` is the chart point `{(S y, y)}` exactly when
`Im U` is invertible and `S = Re U (Im U)⁻¹`. -/
theorem unitaryFrame_eq_graphY_iff {U : unitaryGroup ι ℂ} {S : selfAdjoint (Matrix ι ι ℝ)} :
    unitaryFrame U = graphY S ↔ IsUnit ((U : Matrix ι ι ℂ).map Complex.im) ∧
      (U : Matrix ι ι ℂ).map Complex.re * ((U : Matrix ι ι ℂ).map Complex.im)⁻¹ = S := by
  set X := (U : Matrix ι ι ℂ).map Complex.re
  set Y := (U : Matrix ι ι ℂ).map Complex.im
  constructor
  · intro h
    have hXS : X = (S : Matrix ι ι ℝ) * Y := by
      refine mulVec_injective (funext fun u ↦ ?_)
      have hu : toEuclideanLin (fromRows X Y) (WithLp.toLp 2 u) ∈ graphY S := by
        rw [← h, ← mem_toSubmodule, coe_unitaryFrame]
        exact LinearMap.mem_range_self _ _
      rw [mem_graphY_iff, StdSpace.x_toEuclideanLin_fromRows,
        StdSpace.y_toEuclideanLin_fromRows] at hu
      simpa [mulVec_mulVec] using hu
    have hrank := ((isLagrangian_range_fromRows_iff _ _).1
      (isLagrangian_range_fromRows_re_im U)).1
    have hY : IsUnit Y := by
      refine mulVec_surjective_iff_isUnit.1 (mulVec_surjective_iff_rank_eq_card.2 ?_)
      refine le_antisymm (rank_le_card_width Y) ?_
      calc Fintype.card ι = (fromRows X Y).rank := hrank.symm
        _ = (fromRows (S : Matrix ι ι ℝ) 1 * Y).rank := by
          rw [fromRows_mul, Matrix.one_mul, ← hXS]
        _ ≤ Y.rank := rank_mul_le_right _ _
    refine ⟨hY, ?_⟩
    rw [hXS, mul_nonsing_inv_cancel_right (A := Y) _ ((isUnit_iff_isUnit_det Y).1 hY)]
  · rintro ⟨hY, hS⟩
    have hXS : X = (S : Matrix ι ι ℝ) * Y := by
      rw [← hS, nonsing_inv_mul_cancel_right (A := Y) _ ((isUnit_iff_isUnit_det Y).1 hY)]
    refine toSubmodule_injective ?_
    rw [coe_unitaryFrame, coe_graphY, ← StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY,
      ← range_toLpLin_mul_of_isUnit 2 (fromRows (S : Matrix ι ι ℝ) 1) hY, fromRows_mul,
      Matrix.one_mul, ← hXS]

private theorem continuousOn_chartValue :
    ContinuousOn chartValue
      {U : unitaryGroup ι ℂ | IsUnit ((U : Matrix ι ι ℂ).map Complex.im)} := by
  refine IsInducing.subtypeVal.continuousOn_iff.2 fun U hU ↦ ?_
  have hX : Continuous fun U : unitaryGroup ι ℂ ↦ (U : Matrix ι ι ℂ).map Complex.re :=
    continuous_subtypeVal.matrix_map Complex.continuous_re
  have hY : Continuous fun U : unitaryGroup ι ℂ ↦ (U : Matrix ι ι ℂ).map Complex.im :=
    continuous_subtypeVal.matrix_map Complex.continuous_im
  exact (hX.continuousAt.mul (hY.continuousAt.matrix_inv
    (isUnit_iff_ne_zero.1 ((isUnit_iff_isUnit_det _).1 hU)))).continuousWithinAt

end DecidableEq

/-- **The basic chart.** The map `S ↦ {(S y, y)}` is an open embedding of the space of real
symmetric matrices into the Lagrangian Grassmannian. -/
theorem isOpenEmbedding_graphY : IsOpenEmbedding (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) := by
  classical
  refine .of_continuous_injective_isOpenMap continuous_graphY graphY_injective fun s hs ↦ ?_
  rw [← (isQuotientMap_unitaryFrame (ι := ι)).isOpen_preimage]
  have he : unitaryFrame ⁻¹' (graphY '' s) =
      {U : unitaryGroup ι ℂ | IsUnit ((U : Matrix ι ι ℂ).map Complex.im)} ∩
        chartValue ⁻¹' s := by
    ext U
    simp only [mem_preimage, mem_image, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨S, hS, h⟩
      obtain ⟨hY, hXY⟩ := unitaryFrame_eq_graphY_iff.1 h.symm
      exact ⟨hY, by rwa [show chartValue U = S from Subtype.ext hXY]⟩
    · rintro ⟨hY, hs⟩
      exact ⟨_, hs, (unitaryFrame_eq_graphY_iff.2 ⟨hY, rfl⟩).symm⟩
  have hopen : IsOpen {U : unitaryGroup ι ℂ | IsUnit ((U : Matrix ι ι ℂ).map Complex.im)} := by
    simp_rw [isUnit_iff_isUnit_det]
    exact (continuous_subtypeVal.matrix_map Complex.continuous_im).isOpen_setOf_isUnit_det
  rw [he]
  exact continuousOn_chartValue.isOpen_inter_preimage hopen hs

/-- The Lagrangians transverse to a given Lagrangian `Λ₀` form an open subset of `ℒ ι`. -/
theorem isOpen_setOf_isCompl (Λ₀ : ℒ ι) :
    IsOpen {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι)) Λ₀} := by
  classical
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GLSymplectic ι ℝ) (horizontal ι) Λ₀
  have h : {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι))
        ((g • horizontal ι : ℒ ι) : Submodule ℝ (StdSpace ι))} =
      (g⁻¹ • ·) ⁻¹' Set.range (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) := by
    ext Λ
    rw [range_graphY, mem_preimage, mem_ofPred_eq, mem_ofPred_eq, ← isCompl_smul_iff g⁻¹,
      inv_smul_smul]
  rw [h]
  exact (isOpenEmbedding_graphY (ι := ι)).isOpen_range.preimage (continuous_const_smul _)

/-! ### The chart transverse to the horizontal subspace -/

/-- The chart of `ℒ ι` on the Lagrangians transverse to the horizontal subspace `{y = 0}`: it
sends the graph `{(S y, y)}` to the symmetric matrix `S`. -/
noncomputable def graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ)) :=
  ((isOpenEmbedding_graphY (ι := ι)).toOpenPartialHomeomorph graphY).symm

theorem graphYChart_def :
    (graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))) =
      ((isOpenEmbedding_graphY (ι := ι)).toOpenPartialHomeomorph graphY).symm :=
  (rfl)

@[simp]
theorem graphYChart_source :
    (graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))).source =
      {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι)) (horizontal ι)} := by
  simp [graphYChart_def, range_graphY]

@[simp]
theorem graphYChart_target :
    (graphYChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))).target = univ := by
  simp [graphYChart_def]

@[simp]
theorem graphYChart_symm_apply (S : selfAdjoint (Matrix ι ι ℝ)) :
    (graphYChart : OpenPartialHomeomorph (ℒ ι) _).symm S = graphY S := by
  simp [graphYChart_def]

@[simp]
theorem graphYChart_graphY (S : selfAdjoint (Matrix ι ι ℝ)) :
    graphYChart (graphY S : ℒ ι) = S := by
  rw [graphYChart_def]
  exact (isOpenEmbedding_graphY (ι := ι)).toOpenPartialHomeomorph_left_inv graphY

/-- The Lagrangian framed by a unitary matrix `U = X + i Y` lies in the source of the basic chart,
that is, is transverse to `{y = 0}`, exactly when `Y` is invertible. -/
theorem unitaryFrame_mem_graphYChart_source_iff [DecidableEq ι] {U : unitaryGroup ι ℂ} :
    unitaryFrame U ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source ↔
      IsUnit ((U : Matrix ι ι ℂ).map Complex.im) := by
  rw [graphYChart_source, ← range_graphY]
  constructor
  · rintro ⟨S, hS⟩
    exact (unitaryFrame_eq_graphY_iff.1 hS.symm).1
  · intro hU
    exact ⟨chartValue U, (unitaryFrame_eq_graphY_iff.2 ⟨hU, rfl⟩).symm⟩

/-- For a unitary matrix `U = X + i Y` with `Y` invertible, the basic chart sends the Lagrangian
framed by `U` to `X Y⁻¹`. -/
theorem coe_graphYChart_unitaryFrame [DecidableEq ι] {U : unitaryGroup ι ℂ}
    (hU : IsUnit ((U : Matrix ι ι ℂ).map Complex.im)) :
    (graphYChart (unitaryFrame U) : Matrix ι ι ℝ) =
      (U : Matrix ι ι ℂ).map Complex.re * ((U : Matrix ι ι ℂ).map Complex.im)⁻¹ := by
  rw [← unitaryFrame_mem_graphYChart_source_iff, graphYChart_source, ← range_graphY] at hU
  obtain ⟨S, hS⟩ := hU
  rw [← hS, graphYChart_graphY]
  exact (unitaryFrame_eq_graphY_iff.1 hS.symm).2.symm

/-! ### The chart transverse to the vertical subspace -/

section DecidableEq

variable [DecidableEq ι]

/-- The chart of `ℒ ι` on the Lagrangians transverse to the vertical subspace `{x = 0}`: it
sends the graph `{(x, S x)}` to the symmetric matrix `S`. It is the action of the matrix `J` of
`TauCeti.GLSymplectic.symJ`, then `graphYChart`, then `S ↦ -S`. -/
noncomputable def graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ)) :=
  ((Homeomorph.smul (α := ℒ ι) (GLSymplectic.symJ ι ℝ)).toOpenPartialHomeomorph.trans
    graphYChart).trans
    (Homeomorph.neg _).toOpenPartialHomeomorph

theorem graphChart_def :
    (graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))) =
      ((Homeomorph.smul (α := ℒ ι) (GLSymplectic.symJ ι ℝ)).toOpenPartialHomeomorph.trans
        graphYChart).trans (Homeomorph.neg _).toOpenPartialHomeomorph :=
  (rfl)

theorem graphChart_apply (Λ : ℒ ι) :
    graphChart Λ = -graphYChart (GLSymplectic.symJ ι ℝ • Λ) :=
  (rfl)

@[simp]
theorem graphChart_source :
    (graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))).source =
      {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι)) (vertical ι)} := by
  rw [← range_graph, graphChart_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_source, graphYChart_source, ← range_graphY]
  ext Λ
  simp only [Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, univ_inter, inter_univ,
    mem_preimage, mem_range, Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.smul_apply]
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨-T, smul_left_cancel (GLSymplectic.symJ ι ℝ) ?_⟩
    rw [symJ_smul_graph, neg_neg, hT]
  · rintro ⟨T, rfl⟩
    exact ⟨-T, (symJ_smul_graph T).symm⟩

@[simp]
theorem graphChart_target :
    (graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))).target = univ := by
  simp [graphChart_def]

@[simp]
theorem graphChart_graph (S : selfAdjoint (Matrix ι ι ℝ)) : graphChart (graph S : ℒ ι) = S := by
  rw [graphChart_apply, symJ_smul_graph, graphYChart_graphY, neg_neg]

@[simp]
theorem graphChart_symm_apply (S : selfAdjoint (Matrix ι ι ℝ)) :
    (graphChart : OpenPartialHomeomorph (ℒ ι) _).symm S = graph S := by
  simp [graphChart_def, ← symJ_smul_graph]

end DecidableEq

end LagrangianGrassmannian

end SymplecticGeometry

end
