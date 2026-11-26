/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Action
public import TauCeti.LinearAlgebra.SymplecticGroup
import SymplecticGeometry.LinearAlgebra.Matrix.OfReal

/-!
# Chart points and transverse pairs of Lagrangians

Write `ℒ ι` for the Lagrangian Grassmannian of the standard model `(StdSpace ι, ω₀)`, and
`horizontal ι = {y = 0}`, `vertical ι = {x = 0}` for its coordinate Lagrangians.

## Main definitions

* `SymplecticGeometry.LagrangianGrassmannian.graphY S`: for a real symmetric matrix `S`, the
  Lagrangian `{(S y, y)}`, which is Tau Ceti's `Matrix.lagrangianChart S` read in `StdSpace ι`.
* `SymplecticGeometry.LagrangianGrassmannian.graph S`: the Lagrangian `{(x, S x)}`.

## Main results

* `SymplecticGeometry.LagrangianGrassmannian.isCompl_horizontal_iff`, `isCompl_vertical_iff`,
  `range_graphY`, `range_graph`: the Lagrangians transverse to `{y = 0}` (resp. `{x = 0}`) are
  exactly the graphs `{(S y, y)}` (resp. `{(x, S x)}`) of symmetric matrices.
* `SymplecticGeometry.LagrangianGrassmannian.isHermitian_of_coe_eq_graph`: a real matrix whose
  graph `{(x, A x)}` is a Lagrangian of `ℒ ι` is symmetric.
* `SymplecticGeometry.LagrangianGrassmannian.graphY_eq_ofFrame`: `graphY S` is spanned by the
  Lagrangian frame `fromRows S 1`; `eq_graphY_iff_of_coe_eq`: a Lagrangian spanned by the frame
  `fromRows X Y` is `graphY S` iff `Y` is invertible and `S = X Y⁻¹`.
* `SymplecticGeometry.LagrangianGrassmannian.coe_smul_graphY`: a symplectic matrix with blocks
  `A, B, C, D` maps `graphY S` to the span of the frame `fromRows (A S + B) (C S + D)`.
* `SymplecticGeometry.LagrangianGrassmannian.graphY_eq_unitaryFrame`: a unitary frame of
  `graphY S`, the unitary frame `unitaryOfFrame` of the Lagrangian frame `fromRows S 1`
  (`SymplecticGeometry.isLagrangian_range_fromRows_one`), that is, the real
  orthonormalization of `S + i`.
* `SymplecticGeometry.LagrangianGrassmannian.exists_isCompl_isCompl`: any two Lagrangians have a
  common transverse Lagrangian.
* `SymplecticGeometry.LagrangianGrassmannian.exists_smul_eq_horizontal_vertical`: the symplectic
  group acts transitively on pairs of transverse Lagrangians; `isCompl_smul_iff`, it preserves
  complementarity.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

open Matrix TauCeti

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-! ### Transporting complementarity by the symplectic group -/

/-- The symplectic group preserves complementarity of Lagrangians. -/
theorem isCompl_smul_iff [DecidableEq ι] (g : GLSymplectic ι ℝ) {Λ Λ' : ℒ ι} :
    IsCompl ((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι))
        ((g • Λ' : ℒ ι) : Submodule ℝ (StdSpace ι)) ↔
      IsCompl (Λ : Submodule ℝ (StdSpace ι)) Λ' := by
  rw [coe_smul_eq_map_toEuclideanCLE, coe_smul_eq_map_toEuclideanCLE]
  exact (Submodule.orderIsoMapComap _).isCompl_iff.symm

/-- A symplectic matrix does not change the dimension of the intersection of two Lagrangians. -/
theorem finrank_smul_inf_smul [DecidableEq ι] (g : GLSymplectic ι ℝ) (Λ Λ' : ℒ ι) :
    Module.finrank ℝ ↥(((g • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓
        ((g • Λ' : ℒ ι) : Submodule ℝ (StdSpace ι))) =
      Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ (Λ' : Submodule ℝ (StdSpace ι))) := by
  rw [coe_smul_eq_map_toEuclideanCLE, coe_smul_eq_map_toEuclideanCLE,
    ← Submodule.map_inf _ (LinearEquiv.injective _), LinearEquiv.finrank_map_eq]

/-- A unitary matrix does not change the dimension of the intersection of two Lagrangians. -/
theorem finrank_unitary_smul_inf_smul [DecidableEq ι] (U : unitaryGroup ι ℂ) (Λ Λ' : ℒ ι) :
    Module.finrank ℝ ↥(((U • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓
        ((U • Λ' : ℒ ι) : Submodule ℝ (StdSpace ι))) =
      Module.finrank ℝ ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ (Λ' : Submodule ℝ (StdSpace ι))) := by
  rw [unitary_smul_def, unitary_smul_def, finrank_smul_inf_smul]

/-- The intersection of a Lagrangian `Λ` with the Lagrangian framed by a unitary matrix `U` has
the dimension of the intersection of `U⁻¹ • Λ` with `{y = 0}`. -/
theorem finrank_inf_unitaryFrame [DecidableEq ι] (Λ : ℒ ι) (U : unitaryGroup ι ℂ) :
    Module.finrank ℝ
        ↥((Λ : Submodule ℝ (StdSpace ι)) ⊓ (unitaryFrame U : Submodule ℝ (StdSpace ι))) =
      Module.finrank ℝ ↥(((U⁻¹ • Λ : ℒ ι) : Submodule ℝ (StdSpace ι)) ⊓ horizontal ι) := by
  rw [← finrank_unitary_smul_inf_smul U⁻¹, unitaryFrame_def, inv_smul_smul]

/-! ### The points of the basic chart -/

/-- The Lagrangian `{(S y, y)}` of a real symmetric matrix `S`: Tau Ceti's chart subspace
`Matrix.lagrangianChart S` read in `StdSpace ι`. -/
noncomputable def graphY (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι :=
  ⟨StdSpace.graphY S, (isLagrangian_graphY_iff _).2 (isHermitian_iff_isSymm.1 S.property)⟩

@[simp]
theorem coe_graphY (S : selfAdjoint (Matrix ι ι ℝ)) :
    (graphY S : Submodule ℝ (StdSpace ι)) = StdSpace.graphY S :=
  (rfl)

@[simp]
theorem mem_graphY_iff {S : selfAdjoint (Matrix ι ι ℝ)} {z : StdSpace ι} :
    z ∈ graphY S ↔ z.x = (S : Matrix ι ι ℝ) *ᵥ z.y :=
  StdSpace.mem_graphY_iff

/-- The Lagrangian `graphY S` is Tau Ceti's chart subspace `{S y + i y}` of `ℂⁿ`, carried to
`StdSpace ι`. -/
theorem coe_graphY_eq_map [DecidableEq ι] (S : selfAdjoint (Matrix ι ι ℝ)) :
    (graphY S : Submodule ℝ (StdSpace ι)) =
      (S : Matrix ι ι ℝ).lagrangianChart.map
        (StdSpace.complexEuclideanEquiv ι : EuclideanSpace ℂ ι →ₗ[ℝ] StdSpace ι) :=
  (StdSpace.map_lagrangianChart _).symm

/-- A chart point determines its symmetric matrix. -/
theorem graphY_injective :
    Function.Injective (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) :=
  fun _ _ h ↦ Subtype.ext (StdSpace.graphY_injective (congrArg toSubmodule h))

/-- The chart point of `0` is the vertical Lagrangian `{x = 0}`. -/
@[simp]
theorem graphY_zero : graphY (0 : selfAdjoint (Matrix ι ι ℝ)) = vertical ι :=
  toSubmodule_injective <| by simp

/-- The chart point `graphY S` is the Lagrangian spanned by the frame `fromRows S 1`. -/
theorem graphY_eq_ofFrame [DecidableEq ι] (S : selfAdjoint (Matrix ι ι ℝ)) :
    graphY S = ofFrame (S : Matrix ι ι ℝ) 1
      (isLagrangian_range_fromRows_one (isHermitian_iff_isSymm.1 S.property)) :=
  toSubmodule_injective <| by
    rw [coe_graphY, coe_ofFrame]
    exact (StdSpace.range_toEuclideanLin_fromRows_one_eq_graphY _).symm

/-- A Lagrangian spanned by the frame `fromRows X Y` is the chart point `{(S y, y)}` exactly when
`Y` is invertible and `S = X Y⁻¹`. -/
theorem eq_graphY_iff_of_coe_eq [DecidableEq ι] {Λ : ℒ ι} {X Y : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = LinearMap.range (toEuclideanLin (fromRows X Y)))
    {S : selfAdjoint (Matrix ι ι ℝ)} :
    Λ = graphY S ↔ IsUnit Y ∧ X * Y⁻¹ = S := by
  have hL := hΛ ▸ Λ.isLagrangian
  rw [← toSubmodule_injective.eq_iff, hΛ, coe_graphY]
  constructor
  · intro h
    have hY := (StdSpace.disjoint_range_toEuclideanLin_fromRows_ker_y_iff_of_isLagrangian hL).1
      (h ▸ (StdSpace.isCompl_graphY_ker_y _).disjoint)
    exact ⟨hY, StdSpace.graphY_injective
      ((StdSpace.range_toEuclideanLin_fromRows_eq_graphY hY).symm.trans h)⟩
  · rintro ⟨hY, hS⟩
    rw [StdSpace.range_toEuclideanLin_fromRows_eq_graphY hY, hS]

/-- A unitary frame of `graphY S`: the real orthonormalization of the complex frame `S + i` of
the Lagrangian frame `fromRows S 1`. -/
theorem graphY_eq_unitaryFrame [DecidableEq ι] (S : selfAdjoint (Matrix ι ι ℝ)) :
    graphY S = unitaryFrame (unitaryOfFrame
      (isLagrangian_range_fromRows_one (isHermitian_iff_isSymm.1 S.property))) := by
  rw [unitaryFrame_unitaryOfFrame, graphY_eq_ofFrame]

section Blocks

variable [DecidableEq ι] (g : GLSymplectic ι ℝ)

local notation "M" => ((g : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)

/-- The image of the chart point `{(S y, y)}` under a symplectic matrix `g` with blocks
`A, B, C, D` is spanned by the frame `fromRows (A S + B) (C S + D)`. -/
theorem coe_smul_graphY (S : selfAdjoint (Matrix ι ι ℝ)) :
    ((g • graphY S : ℒ ι) : Submodule ℝ (StdSpace ι)) =
      LinearMap.range (toEuclideanLin (fromRows
        (toBlocks₁₁ M * (S : Matrix ι ι ℝ) + toBlocks₁₂ M)
        (toBlocks₂₁ M * (S : Matrix ι ι ℝ) + toBlocks₂₂ M))) := by
  rw [graphY_eq_ofFrame, coe_smul_of_coe_eq g (coe_ofFrame _ _ _)]
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_mul_fromRows]
  simp only [Matrix.mul_one]

end Blocks

/-! ### The points of the second chart -/

/-- The Lagrangian `{(x, S x)}` of a real symmetric matrix `S`. -/
noncomputable def graph (S : selfAdjoint (Matrix ι ι ℝ)) : ℒ ι :=
  ⟨StdSpace.graph S, (isLagrangian_graph_iff _).2 (isHermitian_iff_isSymm.1 S.property)⟩

@[simp]
theorem coe_graph (S : selfAdjoint (Matrix ι ι ℝ)) :
    (graph S : Submodule ℝ (StdSpace ι)) = StdSpace.graph S :=
  (rfl)

@[simp]
theorem mem_graph_iff {S : selfAdjoint (Matrix ι ι ℝ)} {z : StdSpace ι} :
    z ∈ graph S ↔ z.y = (S : Matrix ι ι ℝ) *ᵥ z.x :=
  StdSpace.mem_graph_iff

/-- A point of the second chart determines its symmetric matrix. -/
theorem graph_injective : Function.Injective (graph : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) :=
  fun _ _ h ↦ Subtype.ext (StdSpace.graph_injective (congrArg toSubmodule h))

/-- If a Lagrangian is the graph `{(x, A x)}` of a real matrix `A`, then `A` is symmetric. -/
theorem isHermitian_of_coe_eq_graph {Λ : ℒ ι} {A : Matrix ι ι ℝ}
    (hΛ : (Λ : Submodule ℝ (StdSpace ι)) = StdSpace.graph A) : A.IsHermitian :=
  isHermitian_iff_isSymm.2 ((isLagrangian_graph_iff _).1 (hΛ ▸ Λ.isLagrangian))

/-- The point of `0` in the second chart is the horizontal Lagrangian `{y = 0}`. -/
@[simp]
theorem graph_zero : graph (0 : selfAdjoint (Matrix ι ι ℝ)) = horizontal ι :=
  toSubmodule_injective <| by simp

/-- The matrix `J` of `TauCeti.GLSymplectic.symJ`, `(x, y) ↦ (-y, x)`, carries the second chart
to the basic one: it maps `{(x, S x)}` to `{(-S y, y)}`. -/
theorem symJ_smul_graph [DecidableEq ι] (S : selfAdjoint (Matrix ι ι ℝ)) :
    GLSymplectic.symJ ι ℝ • graph S = graphY (-S) :=
  toSubmodule_injective <| by
    rw [coe_smul, coe_graph, coe_graphY, StdSpace.map_symJ_graph, NegMemClass.coe_neg]

/-! ### Transverse Lagrangians are graphs -/

/-- A Lagrangian is transverse to `{y = 0}` iff it is the graph `{(S y, y)}` of a symmetric
matrix. -/
theorem isCompl_horizontal_iff {Λ : ℒ ι} :
    IsCompl (Λ : Submodule ℝ (StdSpace ι)) (horizontal ι) ↔
      ∃ S : Matrix ι ι ℝ, S.IsSymm ∧
        (Λ : Submodule ℝ (StdSpace ι)) = StdSpace.graphY S := by
  refine ⟨fun h ↦ exists_eq_graphY_of_isCompl Λ.isLagrangian
    (by rwa [coe_horizontal] at h), ?_⟩
  rintro ⟨S, -, hS⟩
  rw [hS, coe_horizontal]
  exact StdSpace.isCompl_graphY_ker_y S

/-- A Lagrangian is transverse to `{x = 0}` iff it is the graph `{(x, S x)}` of a symmetric
matrix. -/
theorem isCompl_vertical_iff {Λ : ℒ ι} :
    IsCompl (Λ : Submodule ℝ (StdSpace ι)) (vertical ι) ↔
      ∃ S : Matrix ι ι ℝ, S.IsSymm ∧
        (Λ : Submodule ℝ (StdSpace ι)) = StdSpace.graph S := by
  refine ⟨fun h ↦ exists_eq_graph_of_isCompl Λ.isLagrangian
    (by rwa [coe_vertical] at h), ?_⟩
  rintro ⟨S, -, hS⟩
  rw [hS, coe_vertical]
  exact StdSpace.isCompl_graph_ker_x S

/-- The points of the basic chart are the Lagrangians transverse to `{y = 0}`. -/
theorem range_graphY :
    Set.range (graphY : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) =
      {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι)) (horizontal ι)} := by
  ext Λ
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨S, rfl⟩
    exact isCompl_horizontal_iff.2 ⟨S, isHermitian_iff_isSymm.1 S.property, rfl⟩
  · obtain ⟨S, hS, hΛ⟩ := isCompl_horizontal_iff.1 h
    exact ⟨⟨S, isHermitian_iff_isSymm.2 hS⟩, toSubmodule_injective hΛ.symm⟩

/-- The points of the second chart are the Lagrangians transverse to `{x = 0}`. -/
theorem range_graph :
    Set.range (graph : selfAdjoint (Matrix ι ι ℝ) → ℒ ι) =
      {Λ : ℒ ι | IsCompl (Λ : Submodule ℝ (StdSpace ι)) (vertical ι)} := by
  ext Λ
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨S, rfl⟩
    exact isCompl_vertical_iff.2 ⟨S, isHermitian_iff_isSymm.1 S.property, rfl⟩
  · obtain ⟨S, hS, hΛ⟩ := isCompl_vertical_iff.1 h
    exact ⟨⟨S, isHermitian_iff_isSymm.2 hS⟩, toSubmodule_injective hΛ.symm⟩

/-! ### A common transverse Lagrangian -/

section DecidableEq

variable [DecidableEq ι]

/-- Some chart point `{(t y, y)}` is transverse to a given Lagrangian. -/
private theorem exists_isCompl_graphY_smul_one (Λ : ℒ ι) :
    ∃ t : ℝ, IsCompl ((graphY (t • 1) : ℒ ι) : Submodule ℝ (StdSpace ι)) Λ := by
  obtain ⟨U, rfl⟩ := unitaryFrame_surjective Λ
  set X := (U : Matrix ι ι ℂ).map Complex.re
  set Y := (U : Matrix ι ι ℂ).map Complex.im
  have hU : X.map Complex.ofReal + Complex.I • Y.map Complex.ofReal = U := by
    ext i j
    simp [X, Y, mul_comm Complex.I]
  obtain ⟨t, ht⟩ := exists_det_sub_smul_ne_zero (X := X) (Y := Y)
    (by rw [hU]; exact (UnitaryGroup.det_isUnit U).ne_zero)
  refine ⟨t, (isCompl_iff_disjoint _ _).2 (Submodule.disjoint_def.2 fun z hz hzU ↦ ?_)⟩
  rw [coe_unitaryFrame] at hzU
  obtain ⟨u, rfl⟩ := hzU
  rw [coe_graphY, StdSpace.mem_graphY_iff, StdSpace.x_toEuclideanLin_fromRows,
    StdSpace.y_toEuclideanLin_fromRows, selfAdjoint.val_smul, selfAdjoint.val_one,
    smul_mulVec, one_mulVec] at hz
  have hu : (X - t • Y) *ᵥ u = 0 := by
    rw [sub_mulVec, hz, smul_mulVec]
    exact sub_self _
  have hu0 : u = 0 := by
    ext i
    simpa using congrFun (eq_zero_of_mulVec_eq_zero ht hu) i
  rw [hu0, map_zero]

omit [DecidableEq ι] in
/-- **A common transverse Lagrangian.** Any two Lagrangian subspaces of `StdSpace ι` have a
Lagrangian complement in common. -/
theorem exists_isCompl_isCompl (Λ Λ' : ℒ ι) :
    ∃ Λ'' : ℒ ι, IsCompl (Λ'' : Submodule ℝ (StdSpace ι)) Λ ∧
      IsCompl (Λ'' : Submodule ℝ (StdSpace ι)) Λ' := by
  classical
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GLSymplectic ι ℝ) (horizontal ι) Λ
  obtain ⟨t, ht⟩ := exists_isCompl_graphY_smul_one (g⁻¹ • Λ')
  refine ⟨g • graphY (t • 1), (isCompl_smul_iff g).2 ?_, ?_⟩
  · rw [coe_graphY, coe_horizontal]
    exact StdSpace.isCompl_graphY_ker_y _
  · have h := (isCompl_smul_iff g).2 ht
    rwa [smul_inv_smul] at h

/-! ### Transverse pairs -/

/-- The shear `fromBlocks 1 S 0 1`, `(x, y) ↦ (x + S y, y)`, of a symmetric matrix `S`, as an
element of the symplectic group. -/
private noncomputable def shear {S : Matrix ι ι ℝ} (hS : S.IsSymm) : GLSymplectic ι ℝ :=
  (GLSymplectic.mulEquivSymplecticGroup ι ℝ).symm
    ⟨fromBlocks 1 S 0 1, SymplecticGroup.fromBlocks_upper_mem hS.eq⟩

private theorem toEuclideanLin_shear {S : Matrix ι ι ℝ} (hS : S.IsSymm) (z : StdSpace ι) :
    StdSpace.x
        (toEuclideanLin ((shear hS : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) z) =
        z.x + S *ᵥ z.y ∧
      StdSpace.y
        (toEuclideanLin ((shear hS : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) z) =
        z.y := by
  have hy : z.y = fun i ↦ z (Sum.inr i) := funext (StdSpace.y_apply z)
  simp only [shear, GLSymplectic.coe_mulEquivSymplecticGroup_symm_apply,
    GLSymplectic.coe_ofSymplecticGroup]
  constructor <;> ext i <;>
    simp [StdSpace.x_apply, StdSpace.y_apply, fromBlocks_mulVec, hy, Function.comp_def]

private theorem shear_smul_horizontal {S : Matrix ι ι ℝ} (hS : S.IsSymm) :
    shear hS • horizontal ι = horizontal ι := by
  refine ext fun z ↦ ?_
  rw [← mem_toSubmodule, ← mem_toSubmodule, coe_smul, coe_horizontal, Submodule.mem_map,
    LinearMap.mem_ker]
  simp only [LinearMap.mem_ker]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(toEuclideanLin_shear hS w).2]
    exact hw
  · intro hz
    refine ⟨z, hz, StdSpace.ext ?_ (toEuclideanLin_shear hS z).2⟩
    rw [(toEuclideanLin_shear hS z).1, hz, mulVec_zero, add_zero]

private theorem shear_smul_vertical {S : Matrix ι ι ℝ} (hS : S.IsSymm) :
    shear hS • vertical ι = graphY ⟨S, isHermitian_iff_isSymm.2 hS⟩ := by
  refine ext fun z ↦ ?_
  rw [← mem_toSubmodule, coe_smul, coe_vertical, Submodule.mem_map, mem_graphY_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [(toEuclideanLin_shear hS w).1, (toEuclideanLin_shear hS w).2, LinearMap.mem_ker.1 hw,
      zero_add]
  · intro hz
    refine ⟨(StdSpace.equivProd ι).symm (0, z.y), by simp, StdSpace.ext ?_ ?_⟩
    · rw [(toEuclideanLin_shear hS _).1, hz]
      simp
    · rw [(toEuclideanLin_shear hS _).2]
      simp

/-- **Transverse pairs form one orbit.** For complementary Lagrangians `Λ`, `Λ'`, some symplectic
matrix maps `{y = 0}` to `Λ` and `{x = 0}` to `Λ'`. -/
theorem exists_smul_eq_horizontal_vertical {Λ Λ' : ℒ ι}
    (h : IsCompl (Λ : Submodule ℝ (StdSpace ι)) Λ') :
    ∃ g : GLSymplectic ι ℝ, g • horizontal ι = Λ ∧ g • vertical ι = Λ' := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GLSymplectic ι ℝ) (horizontal ι) Λ
  have h' : IsCompl ((g⁻¹ • Λ' : ℒ ι) : Submodule ℝ (StdSpace ι)) (horizontal ι) := by
    rw [← isCompl_smul_iff g, smul_inv_smul]
    exact h.symm
  obtain ⟨S, hS, hΛ'⟩ := isCompl_horizontal_iff.1 h'
  refine ⟨g * shear hS, by rw [mul_smul, shear_smul_horizontal], ?_⟩
  rw [mul_smul, shear_smul_vertical, ← eq_inv_smul_iff]
  exact toSubmodule_injective hΛ'.symm

end DecidableEq

end LagrangianGrassmannian

end SymplecticGeometry

end
