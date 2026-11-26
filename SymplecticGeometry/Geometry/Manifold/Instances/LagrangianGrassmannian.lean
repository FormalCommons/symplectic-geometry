/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Graph
public import TauCeti.Analysis.Calculus.ContDiff.Star
import SymplecticGeometry.LinearAlgebra.Matrix.SelfAdjoint
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# The Lagrangian Grassmannian as a smooth manifold

Write `ℒ ι` for the space of Lagrangian subspaces of the standard model `(StdSpace ι, ω₀)`, with
the topology of orthogonal projections. This file makes `ℒ ι` a smooth manifold modelled on the
real symmetric matrices `selfAdjoint (Matrix ι ι ℝ)`, and collects the facts of McDuff–Salamon
§2.3 about Lagrangian frames and the Lagrangian Grassmannian in one theorem.

The charts are the basic chart `graphYChart`, which sends the graph `{(S y, y)}` to `S`,
translated by unitary matrices: the chart `unitaryChart U` sends `Λ` to
`graphYChart (U⁻¹ • Λ)`. Two such charts differ by the action of a symplectic matrix with blocks
`A, B, C, D`, which sends `{(S y, y)}` to `{(T y, y)}` with `T = (A S + B)(C S + D)⁻¹` wherever
`C S + D` is invertible. This rational map is smooth, so the atlas is smooth.

The model space carries the ℓ² operator norm of `Matrix.Norms.L2Operator`. The smooth structure
does not depend on that choice, but the statements need one: to use them,
`open scoped Matrix.Norms.L2Operator`. This use of `selfAdjoint (Matrix ι ι ℝ)` with the ℓ²
operator norm as a model space follows Tau Ceti's
`TauCeti/Geometry/Manifold/Instances/PositiveDefiniteMatrix.lean`.

## Main definitions and results

* `SymplecticGeometry.LagrangianGrassmannian.contDiffOn_graphYChart_smul_graphY`: the transition
  maps `S ↦ (A S + B)(C S + D)⁻¹` are smooth where they are defined.
* `SymplecticGeometry.LagrangianGrassmannian.unitaryChart U`: the basic chart translated by a
  unitary matrix `U`.
* The `ChartedSpace (selfAdjoint (Matrix ι ι ℝ)) (ℒ ι)` instance, whose chart at `Λ` is
  `unitaryChart (chartUnitary Λ)` for a unitary `chartUnitary Λ` with
  `chartUnitary Λ • {x = 0} = Λ` (`chartAt_symm_apply`, `chartAt_self`), and the
  `IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι)` instance.
* `SymplecticGeometry.lagrangianGrassmannian_properties`: the frame criterion, the graph
  criterion, the action of `Sp(2n)` and the transitivity of `U(n)`, `ℒ ι ≃ U(n)/O(n)`, the
  manifold structure, its dimension `n (n + 1) / 2`, and the graph charts.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3,
  Lemmas 2.3.1 and 2.3.2.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Smoothness of the transition maps -/

section Blocks

variable (g : GLSymplectic ι ℝ)

local notation "M" => ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)

/-- The transition maps are smooth: `S ↦ graphYChart (g • graphY S)` is smooth on the open set
of symmetric matrices `S` where it is defined. -/
theorem contDiffOn_graphYChart_smul_graphY :
    ContDiffOn ℝ ∞ (fun S : selfAdjoint (Matrix ι ι ℝ) ↦ graphYChart (g • graphY S : ℒ ι))
      {S | g • graphY S ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source} := by
  have hs : {S | g • graphY S ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source} =
      {S : selfAdjoint (Matrix ι ι ℝ) |
        IsUnit (toBlocks₂₁ M * (S : Matrix ι ι ℝ) + toBlocks₂₂ M)} :=
    Set.ext fun S ↦ mem_graphYChart_source_iff_isUnit (coe_smul_graphY g S)
  have hv := selfAdjoint.contDiff_subtype_val ℝ (A := Matrix ι ι ℝ) (k := ∞)
  have h₁ : ContDiff ℝ ∞ fun S : selfAdjoint (Matrix ι ι ℝ) ↦
      toBlocks₁₁ M * (S : Matrix ι ι ℝ) + toBlocks₁₂ M :=
    (contDiff_const.mul hv).add contDiff_const
  have h₂ : ContDiff ℝ ∞ fun S : selfAdjoint (Matrix ι ι ℝ) ↦
      toBlocks₂₁ M * (S : Matrix ι ι ℝ) + toBlocks₂₂ M :=
    (contDiff_const.mul hv).add contDiff_const
  have hF : ContDiffOn ℝ ∞ (fun S : selfAdjoint (Matrix ι ι ℝ) ↦
      selfAdjointPartL ℝ (Matrix ι ι ℝ) ((toBlocks₁₁ M * (S : Matrix ι ι ℝ) + toBlocks₁₂ M) *
        Ring.inverse (toBlocks₂₁ M * (S : Matrix ι ι ℝ) + toBlocks₂₂ M)))
      {S | IsUnit (toBlocks₂₁ M * (S : Matrix ι ι ℝ) + toBlocks₂₂ M)} := by
    refine (selfAdjointPartL ℝ (Matrix ι ι ℝ)).contDiff.comp_contDiffOn fun S hS ↦ ?_
    exact (h₁.contDiffAt.mul (h₂.contDiffAt.inverse hS)).contDiffWithinAt
  rw [hs]
  refine hF.congr fun S hS ↦ ?_
  -- Mathlib generates only `selfAdjointPartL_apply_coe` for `selfAdjointPartL`, so there is no
  -- `selfAdjointPartL_apply` to rewrite with: unfold it to `selfAdjointPart` by `change`.
  change _ = selfAdjointPart ℝ _
  rw [← nonsing_inv_eq_ringInverse, ← coe_graphYChart_eq_mul_inv (coe_smul_graphY g S) hS]
  exact ((graphYChart (g • graphY S : ℒ ι)).property.selfAdjointPart_apply ℝ).symm

end Blocks

/-! ### The translated charts -/

/-- The basic chart translated by a unitary matrix `U`: `Λ ↦ graphYChart (U⁻¹ • Λ)`, defined on
the Lagrangians transverse to `U • {y = 0}`, with inverse `S ↦ U • graphY S`. -/
noncomputable def unitaryChart (U : unitaryGroup ι ℂ) :
    OpenPartialHomeomorph (ℒ ι) (selfAdjoint (Matrix ι ι ℝ)) :=
  (Homeomorph.smul (α := ℒ ι) U⁻¹).toOpenPartialHomeomorph.trans graphYChart

theorem unitaryChart_def (U : unitaryGroup ι ℂ) :
    unitaryChart U =
      (Homeomorph.smul (α := ℒ ι) U⁻¹).toOpenPartialHomeomorph.trans graphYChart :=
  (rfl)

@[simp]
theorem unitaryChart_apply (U : unitaryGroup ι ℂ) (Λ : ℒ ι) :
    unitaryChart U Λ = graphYChart (U⁻¹ • Λ) :=
  (rfl)

@[simp]
theorem unitaryChart_symm_apply (U : unitaryGroup ι ℂ) (S : selfAdjoint (Matrix ι ι ℝ)) :
    (unitaryChart U).symm S = U • graphY S := by
  simp [unitaryChart_def]

theorem mem_unitaryChart_source_iff {U : unitaryGroup ι ℂ} {Λ : ℒ ι} :
    Λ ∈ (unitaryChart U).source ↔
      U⁻¹ • Λ ∈ (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source := by
  simp [unitaryChart_def]

@[simp]
theorem unitaryChart_target (U : unitaryGroup ι ℂ) : (unitaryChart U).target = univ := by
  simp [unitaryChart_def]

/-- The transition map from the chart translated by `U` to the chart translated by `U'` is
`S ↦ graphYChart (g • graphY S)` for the symplectic matrix `g` of `U'⁻¹ U`. -/
theorem unitaryChart_symm_trans_apply (U U' : unitaryGroup ι ℂ)
    (S : selfAdjoint (Matrix ι ι ℝ)) :
    ((unitaryChart U).symm.trans (unitaryChart U')) S =
      graphYChart (GLSymplectic.ofUnitary (U'⁻¹ * U) • graphY S : ℒ ι) := by
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, unitaryChart_symm_apply,
    unitaryChart_apply, smul_smul, unitary_smul_def]

theorem unitaryChart_symm_trans_source (U U' : unitaryGroup ι ℂ) :
    ((unitaryChart U).symm.trans (unitaryChart U')).source =
      {S | GLSymplectic.ofUnitary (U'⁻¹ * U) • graphY S ∈
        (graphYChart : OpenPartialHomeomorph (ℒ ι) _).source} := by
  ext S
  -- The statement keeps the symplectic matrix `ofUnitary (U'⁻¹ * U)`, so unfold the unitary
  -- action into that form instead of the simp normal form `U • Λ`.
  simp [mem_unitaryChart_source_iff, smul_smul, unitary_smul_def, -ofUnitary_smul]

/-- A unitary matrix `U` with `U • {x = 0} = Λ`, chosen once and for all. The chart of `ℒ ι` at
`Λ` is the basic chart translated by `U`, so that it is centred at `Λ`. -/
noncomputable def chartUnitary (Λ : ℒ ι) : unitaryGroup ι ℂ :=
  (MulAction.exists_smul_eq (unitaryGroup ι ℂ) (vertical ι) Λ).choose

@[simp]
theorem chartUnitary_smul_vertical (Λ : ℒ ι) : chartUnitary Λ • vertical ι = Λ :=
  (MulAction.exists_smul_eq (unitaryGroup ι ℂ) (vertical ι) Λ).choose_spec

/-! ### The manifold structure -/

/-- The Lagrangian Grassmannian is a topological manifold modelled on the real symmetric
matrices. Its atlas consists of the basic chart `graphYChart` translated by the unitary
matrices, and the chart at `Λ` sends `Λ` to `0`. -/
noncomputable instance : ChartedSpace (selfAdjoint (Matrix ι ι ℝ)) (ℒ ι) where
  atlas := range unitaryChart
  chartAt Λ := unitaryChart (chartUnitary Λ)
  mem_chart_source Λ := by
    rw [mem_unitaryChart_source_iff, inv_smul_eq_iff.2 (chartUnitary_smul_vertical Λ).symm,
      graphYChart_source]
    exact isCompl_horizontal_vertical.symm
  chart_mem_atlas Λ := mem_range_self _

theorem atlas_eq :
    atlas (selfAdjoint (Matrix ι ι ℝ)) (ℒ ι) = range unitaryChart :=
  (rfl)

theorem chartAt_eq (Λ : ℒ ι) :
    chartAt (selfAdjoint (Matrix ι ι ℝ)) Λ = unitaryChart (chartUnitary Λ) :=
  (rfl)

/-- The inverse of the chart at `Λ` sends `S` to the chart point `{(S y, y)}` translated by the
unitary matrix `chartUnitary Λ`. -/
@[simp]
theorem chartAt_symm_apply (Λ : ℒ ι) (S : selfAdjoint (Matrix ι ι ℝ)) :
    (chartAt (selfAdjoint (Matrix ι ι ℝ)) Λ).symm S = chartUnitary Λ • graphY S :=
  unitaryChart_symm_apply _ _

/-- The chart at `Λ` sends `Λ` to the zero matrix. -/
@[simp]
theorem chartAt_self (Λ : ℒ ι) : chartAt (selfAdjoint (Matrix ι ι ℝ)) Λ Λ = 0 := by
  rw [chartAt_eq, unitaryChart_apply, inv_smul_eq_iff.2 (chartUnitary_smul_vertical Λ).symm,
    ← graphY_zero, graphYChart_graphY]

/-- **The Lagrangian Grassmannian is a smooth manifold**, modelled on the real symmetric matrices:
its transition maps `S ↦ (A S + B)(C S + D)⁻¹` are smooth. -/
instance : IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨U, rfl⟩ ⟨U', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
  rw [unitaryChart_symm_trans_source]
  exact (contDiffOn_graphYChart_smul_graphY _).congr fun S _ ↦
    unitaryChart_symm_trans_apply U U' S

end LagrangianGrassmannian

/-! ### The milestone -/

/-- **Lagrangian frames and the Lagrangian Grassmannian.** In the standard model
`(StdSpace ι, ω₀)` of dimension `2n`, `n = Fintype.card ι`:
1. the columns of a real `2n × n` matrix `fromRows X Y` span a Lagrangian subspace iff it has
   rank `n` and `Xᵀ Y = Yᵀ X`; in particular the graph `{(x, A x)}` of a real `n × n` matrix `A`
   is Lagrangian iff `A` is symmetric;
2. the symplectic group `Sp(2n)` maps Lagrangian subspaces to Lagrangian subspaces, and already
   `U(n) ⊆ Sp(2n)` acts transitively on them;
3. the space `ℒ ι` of Lagrangian subspaces is homeomorphic to `U(n)/O(n)`, through
   `U ↦ U • {y = 0}`; it is a smooth manifold modelled on the real symmetric matrices, which
   have dimension `n (n + 1) / 2`, and each chart is inverse to a translate by a unitary matrix
   of `S ↦ {(S y, y)}`, the graph of a symmetric matrix.

Milestone: *Lagrangian frames and the Lagrangian Grassmannian*. -/
theorem lagrangianGrassmannian_properties :
    (∀ X Y : Matrix ι ι ℝ,
      (stdForm ι).IsLagrangian
          (LinearMap.range (Matrix.toEuclideanLin (Matrix.fromRows X Y))) ↔
        (Matrix.fromRows X Y).rank = Fintype.card ι ∧ Xᵀ * Y = Yᵀ * X) ∧
    (∀ A : Matrix ι ι ℝ, (stdForm ι).IsLagrangian (StdSpace.graph A) ↔ A.IsSymm) ∧
    (∀ A ∈ Matrix.symplecticGroup ι ℝ, ∀ L : Submodule ℝ (StdSpace ι),
      (stdForm ι).IsLagrangian L →
        (stdForm ι).IsLagrangian (L.map (Matrix.toEuclideanLin A))) ∧
    (∀ Λ : ℒ ι, ∃ U : unitaryGroup ι ℂ,
      TauCeti.GLSymplectic.ofUnitary U • LagrangianGrassmannian.horizontal ι = Λ) ∧
    (∃ e : unitaryGroup ι ℂ ⧸ Matrix.UnitaryGroup.realSubgroup ι ≃ₜ ℒ ι,
      ∀ U, e (QuotientGroup.mk U) =
        TauCeti.GLSymplectic.ofUnitary U • LagrangianGrassmannian.horizontal ι) ∧
    IsManifold 𝓘(ℝ, selfAdjoint (Matrix ι ι ℝ)) ∞ (ℒ ι) ∧
    Module.finrank ℝ (selfAdjoint (Matrix ι ι ℝ)) =
      Fintype.card ι * (Fintype.card ι + 1) / 2 ∧
    ∀ Λ : ℒ ι, ∃ U : unitaryGroup ι ℂ, ∀ S,
      (chartAt (selfAdjoint (Matrix ι ι ℝ)) Λ).symm S =
        TauCeti.GLSymplectic.ofUnitary U • LagrangianGrassmannian.graphY S :=
  ⟨isLagrangian_range_fromRows_iff, isLagrangian_graph_iff,
    fun _ hA _ hL ↦ isLagrangian_map_toEuclideanLin hA hL,
    fun Λ ↦ (LagrangianGrassmannian.unitaryFrame_surjective Λ).imp fun U h ↦ by
      rwa [LagrangianGrassmannian.unitaryFrame_def, LagrangianGrassmannian.unitary_smul_def] at h,
    ⟨LagrangianGrassmannian.quotientHomeomorph ι, fun U ↦
      (LagrangianGrassmannian.quotientHomeomorph_mk U).trans (by
        rw [LagrangianGrassmannian.unitaryFrame_def, LagrangianGrassmannian.unitary_smul_def])⟩,
    inferInstance, Matrix.finrank_selfAdjoint,
    fun Λ ↦ ⟨LagrangianGrassmannian.chartUnitary Λ, fun S ↦
      LagrangianGrassmannian.chartAt_symm_apply Λ S⟩⟩

end SymplecticGeometry

end
