/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
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
* `SymplecticGeometry.LagrangianGrassmannian.isOpen_setOfPred_isCompl`: the Lagrangians transverse
  to a given one form an open set.
* `SymplecticGeometry.LagrangianGrassmannian.graphYChart`: the chart on the Lagrangians
  transverse to `{y = 0}`, with inverse `graphY`. For a Lagrangian spanned by a frame
  `fromRows X Y`, `mem_graphYChart_source_iff_isUnit` says it lies in the source iff `Y` is
  invertible, and `coe_graphYChart_eq_mul_inv` gives its value `X Y⁻¹`;
  `unitaryFrame_mem_graphYChart_source_iff` says
  when a unitary frame lies in its source, and `coe_graphYChart_unitaryFrame` gives its value
  there.
* `SymplecticGeometry.LagrangianGrassmannian.graphChart`: the chart on the Lagrangians transverse
  to `{x = 0}`, with inverse `graph`. For a Lagrangian spanned by `fromRows X Y`,
  `mem_graphChart_source_iff_isUnit` says it lies in the source iff `X` is invertible, and
  `coe_graphChart_eq_mul_inv` gives its value `Y X⁻¹`.
* `SymplecticGeometry.LagrangianGrassmannian.continuous_of_coe_eq_graph`: a continuous family of
  Lagrangians that are graphs `{(x, A t x)}` has continuous `A`.

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
  rw [funext graphY_eq_ofFrame]
  exact continuous_ofFrame continuous_subtypeVal continuous_const _

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
      (U : Matrix ι ι ℂ).map Complex.re * ((U : Matrix ι ι ℂ).map Complex.im)⁻¹ = S :=
  eq_graphY_iff_of_coe_eq (coe_unitaryFrame U)

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
  rw [he]
  refine continuousOn_chartValue.isOpen_inter_preimage ?_ hs
  simp_rw [isUnit_iff_isUnit_det]
  exact Matrix.isOpen_setOfPred_isUnit_det_map_im.preimage continuous_subtypeVal

/-- The Lagrangians transverse to a given Lagrangian `Λ₀` form an open subset of `ℒ ι`. -/
theorem isOpen_setOfPred_isCompl (Λ₀ : ℒ ι) :
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

/-- A Lagrangian spanned by the frame `fromRows X Y` lies in the source of the basic chart, that
is, is transverse to `{y = 0}`, exactly when `Y` is invertible. -/
theorem mem_graphYChart_source_iff_isUnit [DecidableEq ι] {Λ : ℒ ι} {X Y : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin (fromRows X Y))) :
    Λ ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source ↔ IsUnit Y := by
  rw [graphYChart_source, mem_ofPred_eq, isCompl_iff_disjoint, hΛ, coe_horizontal]
  exact StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian
    (hΛ ▸ Λ.isLagrangian)

/-- If a Lagrangian is spanned by the frame `fromRows X Y` with `Y` invertible, the basic chart
sends it to `X Y⁻¹`. -/
theorem coe_graphYChart_eq_mul_inv [DecidableEq ι] {Λ : ℒ ι} {X Y : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin (fromRows X Y)))
    (hY : IsUnit Y) :
    (graphYChart Λ : Matrix ι ι ℝ) = X * Y⁻¹ := by
  obtain ⟨T, rfl⟩ : Λ ∈ range graphY := by
    rw [range_graphY, ← graphYChart_source]
    exact (mem_graphYChart_source_iff_isUnit hΛ).2 hY
  rw [graphYChart_graphY]
  apply StdSpace.graphY_injective
  rw [← coe_graphY, hΛ, StdSpace.range_toEuclideanLin_fromRows_eq_graphY hY]

/-- The Lagrangian framed by a unitary matrix `U = X + i Y` lies in the source of the basic chart,
that is, is transverse to `{y = 0}`, exactly when `Y` is invertible. -/
theorem unitaryFrame_mem_graphYChart_source_iff [DecidableEq ι] {U : unitaryGroup ι ℂ} :
    unitaryFrame U ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source ↔
      IsUnit ((U : Matrix ι ι ℂ).map Complex.im) :=
  mem_graphYChart_source_iff_isUnit (coe_unitaryFrame U)

/-- For a unitary matrix `U = X + i Y` with `Y` invertible, the basic chart sends the Lagrangian
framed by `U` to `X Y⁻¹`. -/
theorem coe_graphYChart_unitaryFrame [DecidableEq ι] {U : unitaryGroup ι ℂ}
    (hU : IsUnit ((U : Matrix ι ι ℂ).map Complex.im)) :
    (graphYChart (unitaryFrame U) : Matrix ι ι ℝ) =
      (U : Matrix ι ι ℂ).map Complex.re * ((U : Matrix ι ι ℂ).map Complex.im)⁻¹ :=
  coe_graphYChart_eq_mul_inv (coe_unitaryFrame U) hU

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

/-- A Lagrangian spanned by the frame `fromRows X Y` lies in the source of the chart transverse
to `{x = 0}`, that is, meets `{x = 0}` only in `0`, iff `X` is invertible. -/
theorem mem_graphChart_source_iff_isUnit {Λ : ℒ ι} {X Y : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin (fromRows X Y))) :
    Λ ∈ (graphChart : OpenPartialHomeomorph (ℒ ι) _).source ↔ IsUnit X := by
  rw [graphChart_source, mem_ofPred_eq, isCompl_iff_disjoint, hΛ, coe_vertical]
  exact StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_x_iff_of_isLagrangian
    (hΛ ▸ Λ.isLagrangian)

/-- If a Lagrangian is spanned by the frame `fromRows X Y` with `X` invertible, the chart
transverse to `{x = 0}` sends it to `Y X⁻¹`. -/
theorem coe_graphChart_eq_mul_inv {Λ : ℒ ι} {X Y : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin (fromRows X Y)))
    (hX : IsUnit X) :
    (graphChart Λ : Matrix ι ι ℝ) = Y * X⁻¹ := by
  obtain ⟨T, rfl⟩ : Λ ∈ range graph := by
    rw [range_graph, ← graphChart_source]
    exact (mem_graphChart_source_iff_isUnit hΛ).2 hX
  rw [graphChart_graph]
  apply StdSpace.graph_injective
  rw [← coe_graph, hΛ, StdSpace.range_toEuclideanLin_fromRows_eq_graph hX]

end DecidableEq

/-- A continuous family of Lagrangians that are graphs `{(x, A t x)}` has continuous `A`: the
matrix `A t` is the value of `γ t` in the chart `graphChart`. -/
theorem continuous_of_coe_eq_graph {X : Type*} [TopologicalSpace X] {γ : X → ℒ ι}
    (hγc : Continuous γ) {A : X → Matrix ι ι ℝ}
    (hγ : ∀ t, (γ t : Submodule ℝ (StdSpace ι)) = StdSpace.graph (A t)) : Continuous A := by
  classical
  have hg (t : X) : γ t = graph ⟨A t, isHermitian_of_coe_eq_graph (hγ t)⟩ :=
    toSubmodule_injective (by rw [coe_graph]; exact hγ t)
  have hs (t : X) :
      γ t ∈ (graphChart : OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ))).source := by
    rw [hg t, ← graphChart_symm_apply]
    exact graphChart.map_target (by rw [graphChart_target]; exact mem_univ _)
  have hA (t : X) : A t = (graphChart (γ t) : Matrix ι ι ℝ) := by
    rw [hg t, graphChart_graph]
  rw [show A = _ from funext hA]
  exact continuous_subtypeVal.comp ((graphChart (ι := ι)).continuousOn.comp_continuous hγc hs)

end LagrangianGrassmannian

end SymplecticGeometry

end
