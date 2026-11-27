/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Sum
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
public import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Basic
import SymplecticGeometry.Topology.Grassmannian.Lagrangian.Quotient

/-!
# Continuity of direct sums and reindexing of Lagrangian subspaces

For the Lagrangian Grassmannians `ℒ ι` of the standard models, with the topology of orthogonal
projections, this file shows that the two operations of
`SymplecticGeometry.LinearAlgebra.Symplectic.Lagrangian.Sum` are continuous.

* `SymplecticGeometry.LagrangianGrassmannian.continuous_sum`: the direct sum
  `ℒ ι × ℒ κ → ℒ (ι ⊕ κ)` is continuous.
* `SymplecticGeometry.LagrangianGrassmannian.continuous_reindex`: the relabelling `reindex e`
  along `e : ι ≃ κ` is continuous.
* `SymplecticGeometry.LagrangianGrassmannian.reindexHomeomorph e : ℒ ι ≃ₜ ℒ κ`, the relabelling
  `reindex e` along `e : ι ≃ κ` as a homeomorphism.

Both proofs pass through the open quotient map `unitaryFrame : U(n) → ℒ ι`
(`isOpenQuotientMap_unitaryFrame`): on unitary frames, the direct sum is the block-diagonal sum
of unitary matrices and the relabelling is the reindexing of unitary matrices, and both of these
are continuous.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace SymplecticGeometry

open Matrix TauCeti StdSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "ℒ" ι => LagrangianGrassmannian (stdForm ι)

namespace LagrangianGrassmannian

/-- The direct sum `(Λ, Λ') ↦ Λ ⊕ Λ'` of Lagrangian subspaces is continuous. -/
@[continuity, fun_prop]
theorem continuous_sum : Continuous (sum : (ℒ ι) × (ℒ κ) → ℒ (ι ⊕ κ)) := by
  classical
  refine ((isOpenQuotientMap_unitaryFrame (ι := ι)).prodMap
    (isOpenQuotientMap_unitaryFrame (ι := κ))).continuous_comp_iff.1 ?_
  have h : (sum ∘ Prod.map unitaryFrame unitaryFrame :
      unitaryGroup ι ℂ × unitaryGroup κ ℂ → ℒ (ι ⊕ κ)) = unitaryFrame ∘ UnitaryGroup.sum :=
    funext fun p ↦ sum_unitaryFrame p.1 p.2
  rw [h]
  exact continuous_unitaryFrame.comp UnitaryGroup.continuous_sum

/-- The relabelling `reindex e` is continuous. -/
@[continuity, fun_prop]
theorem continuous_reindex (e : ι ≃ κ) : Continuous (reindex e) := by
  classical
  refine (isOpenQuotientMap_unitaryFrame (ι := ι)).continuous_comp_iff.1 ?_
  have h : (reindex e ∘ unitaryFrame : unitaryGroup ι ℂ → ℒ κ) =
      unitaryFrame ∘ unitaryReindexContinuousMulEquiv ℂ e :=
    funext (reindex_unitaryFrame e)
  rw [h]
  exact continuous_unitaryFrame.comp (unitaryReindexContinuousMulEquiv ℂ e).continuous

/-- The relabelling `ℒ ι ≃ₜ ℒ κ` of the Lagrangian subspaces along `e : ι ≃ κ`, the homeomorphism
whose underlying equivalence is `reindex e`. -/
noncomputable def reindexHomeomorph (e : ι ≃ κ) : (ℒ ι) ≃ₜ ℒ κ where
  toEquiv := reindex e
  continuous_toFun := continuous_reindex e
  continuous_invFun := by
    rw [Equiv.invFun_as_coe, reindex_symm]
    exact continuous_reindex e.symm

@[simp]
theorem coe_reindexHomeomorph (e : ι ≃ κ) : ⇑(reindexHomeomorph e) = reindex e :=
  (rfl)

theorem reindexHomeomorph_apply (e : ι ≃ κ) (Λ : ℒ ι) : reindexHomeomorph e Λ = reindex e Λ :=
  (rfl)

@[simp]
theorem reindexHomeomorph_symm (e : ι ≃ κ) :
    (reindexHomeomorph e).symm = reindexHomeomorph e.symm :=
  Homeomorph.toEquiv_injective (reindex_symm e)

@[simp]
theorem toEquiv_reindexHomeomorph (e : ι ≃ κ) :
    (reindexHomeomorph e).toEquiv = reindex e :=
  (rfl)

end LagrangianGrassmannian

end SymplecticGeometry

end
