/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Matrix.Realify
public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Transverse
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.Matrix.UnitaryGroup

/-!
# Direct sums and reindexing of Lagrangian subspaces

Two operations on the Lagrangian Grassmannians `𝓛(n) = ℒ ι` of the standard models, as algebra
(their continuity is proved elsewhere).

* `SymplecticGeometry.LagrangianGrassmannian.sum : ℒ ι × ℒ κ → ℒ (ι ⊕ κ)`, the direct sum
  `Λ ⊕ Λ'`: the product `Λ × Λ'` read in `StdSpace (ι ⊕ κ)` through the splitting
  `StdSpace.sumEquiv ι κ`. It sends the horizontal and vertical Lagrangians to the horizontal and
  vertical ones (`sum_horizontal`, `sum_vertical`), the chart points of `S` and `T` to the chart
  point of the block-diagonal matrix `diag(S, T)` (`sum_graphY`), and the frames of two unitary
  matrices to the frame of their block-diagonal sum (`sum_unitaryFrame`). It intertwines the
  actions of the symplectic groups with Tau Ceti's direct sum `TauCeti.GLSymplectic.sum`
  (`sum_smul`).
* `SymplecticGeometry.LagrangianGrassmannian.reindex e : ℒ ι ≃ ℒ κ` for `e : ι ≃ κ`, the image
  under the relabelling of the coordinate pairs along `e`. It is functorial in `e`
  (`reindex_refl`, `reindex_symm`, `reindex_trans`), fixes the coordinate Lagrangians, and sends
  the frame of `U` to the frame of the reindexed unitary matrix (`reindex_unitaryFrame`).

These are the operations behind the direct-sum and naturality properties of the Maslov index of
loops of Lagrangian subspaces.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti StdSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

/-- The image of a Lagrangian subspace of `StdSpace ι` under the relabelling of the coordinate
pairs along `e : ι ≃ κ` is Lagrangian. -/
theorem isLagrangian_map_piLpCongrLeft_sumCongr (e : ι ≃ κ) {L : Submodule ℝ (StdSpace ι)}
    (hL : (stdForm ι).IsLagrangian L) :
    (stdForm κ).IsLagrangian
      (L.map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)).toLinearEquiv.toLinearMap) :=
  SymplecticForm.isSymplectomorphism_iff_transport_eq.1
      (isSymplectomorphism_piLpCongrLeft_sumCongr e) ▸
    SymplecticForm.isLagrangian_map_transport_iff.2 hL

namespace LagrangianGrassmannian

/-! ### Direct sums -/

/-- The direct sum `Λ ⊕ Λ'` of Lagrangian subspaces of `StdSpace ι` and `StdSpace κ`: the product
`Λ × Λ'`, read in `StdSpace (ι ⊕ κ)` through the splitting `StdSpace.sumEquiv ι κ`. -/
noncomputable def sum (p : (ℒ ι) × ℒ κ) : ℒ (ι ⊕ κ) :=
  ⟨((p.1 : Submodule ℝ (StdSpace ι)).prod (p.2 : Submodule ℝ (StdSpace κ))).map
      (sumEquiv ι κ).toLinearEquiv.symm.toLinearMap,
    SymplecticForm.isSymplectomorphism_iff_transport_eq.1
        (isSymplectomorphism_sumEquiv (ι := ι) (κ := κ)).symm ▸
      SymplecticForm.isLagrangian_map_transport_iff.2 (p.1.isLagrangian.prod p.2.isLagrangian)⟩

@[simp]
theorem coe_sum (p : (ℒ ι) × ℒ κ) :
    (sum p : Submodule ℝ (StdSpace (ι ⊕ κ))) =
      ((p.1 : Submodule ℝ (StdSpace ι)).prod (p.2 : Submodule ℝ (StdSpace κ))).map
        (sumEquiv ι κ).toLinearEquiv.symm.toLinearMap :=
  (rfl)

/-- A vector lies in `Λ ⊕ Λ'` exactly when its two components under `StdSpace.sumEquiv` lie in
`Λ` and in `Λ'`. -/
@[simp]
theorem mem_sum_iff {p : (ℒ ι) × ℒ κ} {z : StdSpace (ι ⊕ κ)} :
    z ∈ sum p ↔ (sumEquiv ι κ z).1 ∈ p.1 ∧ (sumEquiv ι κ z).2 ∈ p.2 := by
  rw [← mem_toSubmodule, coe_sum, Submodule.mem_map_equiv]
  rfl

/-- The direct sum of the horizontal Lagrangians is the horizontal Lagrangian. -/
@[simp]
theorem sum_horizontal : sum (horizontal ι, horizontal κ) = horizontal (ι ⊕ κ) := by
  ext z
  simp [funext_iff]

/-- The direct sum of the vertical Lagrangians is the vertical Lagrangian. -/
@[simp]
theorem sum_vertical : sum (vertical ι, vertical κ) = vertical (ι ⊕ κ) := by
  ext z
  simp [funext_iff]

/-- The direct sum of the chart points of symmetric matrices `S` and `T` is the chart point of the
block-diagonal matrix `diag(S, T)`. -/
theorem sum_graphY (S : selfAdjoint (Matrix ι ι ℝ)) (T : selfAdjoint (Matrix κ κ ℝ)) :
    sum (graphY S, graphY T) =
      graphY ⟨fromBlocks (S : Matrix ι ι ℝ) 0 0 T,
        S.property.isHermitian.fromBlocks (by simp) T.property.isHermitian⟩ := by
  ext z
  simp [fromBlocks_mulVec, funext_iff, Function.comp_def]

section DecidableEq

variable [DecidableEq ι] [DecidableEq κ]

/-- Through `StdSpace.sumEquiv`, the map of `Matrix.symplecticSum A B` is the product of the maps
of `A` and `B`, as an identity of linear maps. -/
private theorem sumEquiv_symm_comp_prodMap (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
    (B : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) :
    (sumEquiv ι κ).toLinearEquiv.symm.toLinearMap ∘ₗ (toEuclideanLin A).prodMap (toEuclideanLin B) =
      toEuclideanLin (symplecticSum A B) ∘ₗ (sumEquiv ι κ).toLinearEquiv.symm.toLinearMap :=
  LinearMap.ext fun p ↦ (sumEquiv ι κ).injective <| by
    simp [sumEquiv_toEuclideanLin_symplecticSum]

/-- The direct sum intertwines the actions of `Sp(2n) × Sp(2m)` and of `Sp(2(n + m))`, through
Tau Ceti's direct sum `TauCeti.GLSymplectic.sum` of symplectic matrices. -/
theorem sum_smul (g : GLSymplectic ι ℝ) (h : GLSymplectic κ ℝ) (Λ : ℒ ι) (Λ' : ℒ κ) :
    sum (g • Λ, h • Λ') = GLSymplectic.sum (g, h) • sum (Λ, Λ') :=
  toSubmodule_injective <| by
    rw [coe_smul, coe_sum, coe_sum, coe_smul, coe_smul, GLSymplectic.coe_sum,
      ← LinearMap.prodMap_map_prod, ← Submodule.map_comp, ← Submodule.map_comp,
      sumEquiv_symm_comp_prodMap]

/-- The realification of a block-diagonal unitary matrix is the direct sum of the realifications
of its blocks. -/
private theorem sum_ofUnitary (U : unitaryGroup ι ℂ) (U' : unitaryGroup κ ℂ) :
    GLSymplectic.sum (GLSymplectic.ofUnitary U, GLSymplectic.ofUnitary U') =
      GLSymplectic.ofUnitary (UnitaryGroup.sum (U, U')) :=
  Subtype.ext <| Units.ext <| by
    rw [GLSymplectic.coe_sum, GLSymplectic.coe_ofUnitary, GLSymplectic.coe_ofUnitary,
      GLSymplectic.coe_ofUnitary, UnitaryGroup.coe_sum, realify_fromBlocks_zero]

/-- The direct sum of the Lagrangians framed by unitary matrices `U` and `U'` is the Lagrangian
framed by their block-diagonal sum `diag(U, U')`. -/
@[simp]
theorem sum_unitaryFrame (U : unitaryGroup ι ℂ) (U' : unitaryGroup κ ℂ) :
    sum (unitaryFrame U, unitaryFrame U') = unitaryFrame (UnitaryGroup.sum (U, U')) := by
  rw [unitaryFrame_def, unitaryFrame_def, unitaryFrame_def, unitary_smul_def, unitary_smul_def,
    unitary_smul_def, sum_smul, sum_horizontal, sum_ofUnitary]

end DecidableEq

/-! ### Reindexing -/

/-- Relabelling the coordinate pairs along `e` and then along `f` is relabelling them along
`e.trans f`. -/
private theorem piLpCongrLeft_sumCongr_apply_apply {μ : Type*} [Fintype μ] (e : ι ≃ κ)
    (f : κ ≃ μ) (z : StdSpace ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (f.sumCongr f)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e) z) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ((e.trans f).sumCongr (e.trans f)) z := by
  refine PiLp.ext fun k ↦ ?_
  rcases k with i | i <;> simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- The `x`-coordinates of the relabelled vector are `z.x ∘ e`. -/
private theorem x_piLpCongrLeft_sumCongr_symm (e : ι ≃ κ) (z : StdSpace κ) :
    x (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.symm.sumCongr e.symm) z) = z.x ∘ e := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The `y`-coordinates of the relabelled vector are `z.y ∘ e`. -/
private theorem y_piLpCongrLeft_sumCongr_symm (e : ι ≃ κ) (z : StdSpace κ) :
    y (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.symm.sumCongr e.symm) z) = z.y ∘ e := by
  ext i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The relabelling `ℒ ι ≃ ℒ κ` of the Lagrangian subspaces along `e : ι ≃ κ`: the image under
the relabelling `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)` of the coordinate pairs
`(xᵢ, yᵢ)`. -/
noncomputable def reindex (e : ι ≃ κ) : (ℒ ι) ≃ ℒ κ where
  toFun Λ := ⟨_, isLagrangian_map_piLpCongrLeft_sumCongr e Λ.isLagrangian⟩
  invFun Λ := ⟨_, isLagrangian_map_piLpCongrLeft_sumCongr e.symm Λ.isLagrangian⟩
  left_inv Λ := by
    ext z
    simp [Submodule.mem_map_equiv, LinearIsometryEquiv.piLpCongrLeft_symm,
      piLpCongrLeft_sumCongr_apply_apply]
  right_inv Λ := by
    ext z
    simp [Submodule.mem_map_equiv, LinearIsometryEquiv.piLpCongrLeft_symm,
      piLpCongrLeft_sumCongr_apply_apply]

@[simp]
theorem coe_reindex (e : ι ≃ κ) (Λ : ℒ ι) :
    (reindex e Λ : Submodule ℝ (StdSpace κ)) =
      (Λ : Submodule ℝ (StdSpace ι)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e)).toLinearEquiv.toLinearMap :=
  (rfl)

/-- A vector lies in the relabelled Lagrangian exactly when its relabelling back along `e.symm`
lies in `Λ`. -/
theorem mem_reindex_iff {e : ι ≃ κ} {Λ : ℒ ι} {z : StdSpace κ} :
    z ∈ reindex e Λ ↔ LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.symm.sumCongr e.symm) z ∈ Λ := by
  rw [← mem_toSubmodule, coe_reindex, Submodule.mem_map_equiv]
  simp [LinearIsometryEquiv.piLpCongrLeft_symm]

@[simp]
theorem reindex_symm (e : ι ≃ κ) : (reindex e).symm = reindex e.symm :=
  (rfl)

@[simp]
theorem reindex_refl : reindex (Equiv.refl ι) = Equiv.refl (ℒ ι) := by
  ext Λ z
  simp [mem_reindex_iff]

@[simp]
theorem reindex_trans {μ : Type*} [Fintype μ] (e : ι ≃ κ) (f : κ ≃ μ) :
    (reindex e).trans (reindex f) = reindex (e.trans f) := by
  ext Λ z
  simp [mem_reindex_iff, piLpCongrLeft_sumCongr_apply_apply]

/-- Relabelling fixes the horizontal Lagrangian. -/
@[simp]
theorem reindex_horizontal (e : ι ≃ κ) :
    reindex e (horizontal ι) = horizontal κ := by
  ext z
  rw [mem_reindex_iff, mem_horizontal_iff, mem_horizontal_iff, y_piLpCongrLeft_sumCongr_symm]
  exact e.surjective.injective_comp_right.eq_iff' rfl

/-- Relabelling fixes the vertical Lagrangian. -/
@[simp]
theorem reindex_vertical (e : ι ≃ κ) :
    reindex e (vertical ι) = vertical κ := by
  ext z
  rw [mem_reindex_iff, mem_vertical_iff, mem_vertical_iff, x_piLpCongrLeft_sumCongr_symm]
  exact e.surjective.injective_comp_right.eq_iff' rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- Relabelling along `e` conjugates the map of a matrix `M` to the map of `M` reindexed along
`e.sumCongr e`. -/
private theorem piLpCongrLeft_sumCongr_toEuclideanLin (e : ι ≃ κ)
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (z : StdSpace ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e) (toEuclideanLin M z) =
      toEuclideanLin (Matrix.reindex (e.sumCongr e) (e.sumCongr e) M)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (e.sumCongr e) z) := by
  refine PiLp.ext fun k ↦ ?_
  change (M *ᵥ z.ofLp) ((e.sumCongr e).symm k) =
    (M.submatrix (e.sumCongr e).symm (e.sumCongr e).symm *ᵥ (z.ofLp ∘ (e.sumCongr e).symm)) k
  rw [submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id, Function.comp_apply]

/-- Relabelling along `e` sends the Lagrangian framed by `U` to the Lagrangian framed by the
reindexed unitary matrix `U.submatrix e.symm e.symm`. -/
theorem reindex_unitaryFrame (e : ι ≃ κ) (U : unitaryGroup ι ℂ) :
    reindex e (unitaryFrame U) = unitaryFrame (unitaryReindexContinuousMulEquiv ℂ e U) :=
  toSubmodule_injective <| by
    have hR : (unitaryReindexContinuousMulEquiv ℂ e U : Matrix κ κ ℂ).realify =
        Matrix.reindex (e.sumCongr e) (e.sumCongr e) (U : Matrix ι ι ℂ).realify := by
      rw [coe_unitaryReindexContinuousMulEquiv_apply, reindex_apply, reindex_apply,
        realify_submatrix, Equiv.sumCongr_symm,
        show ⇑(e.symm.sumCongr e.symm) = Sum.map e.symm e.symm from
          funext (Equiv.sumCongr_apply _ _)]
    rw [coe_reindex, unitaryFrame_def, unitaryFrame_def, coe_unitary_smul, coe_unitary_smul,
      ← reindex_horizontal e, coe_reindex, ← Submodule.map_comp, ← Submodule.map_comp, hR]
    congr 1
    exact LinearMap.ext fun z ↦ piLpCongrLeft_sumCongr_toEuclideanLin e _ z

end LagrangianGrassmannian

end SymplecticGeometry

end
