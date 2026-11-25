/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Unitors of the tensor product under the module topology

For a commutative topological semiring `R` and an `R`-module `M`, when `M`, `M ⊗[R] R` and
`R ⊗[R] M` carry their `R`-module topologies, the unitors `TensorProduct.rid` and
`TensorProduct.lid` are continuous in both directions, since every linear map between modules
with the module topology is continuous.

* `TensorProduct.ridL R M : M ⊗[R] R ≃L[R] M`, `m ⊗ r ↦ r • m`, with inverse `m ↦ m ⊗ 1`;
* `TensorProduct.lidL R M : R ⊗[R] M ≃L[R] M`, `r ⊗ m ↦ r • m`, with inverse `m ↦ 1 ⊗ m`.

Both are `LinearEquiv.toContinuousLinearEquivOfIsModuleTopology` of Tau Ceti applied to
Mathlib's unitors. Mathlib's `TensorProduct.ridIsometry` and `TensorProduct.lidIsometry` are the
analogues for the inner product space structure on a tensor product, a different topology.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable (R M : Type*) [CommSemiring R] [TopologicalSpace R]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

section rid

variable [TopologicalSpace (M ⊗[R] R)] [IsModuleTopology R (M ⊗[R] R)]

/-- The right unitor `M ⊗[R] R ≃ M`, `m ⊗ r ↦ r • m`, as a continuous linear equivalence when
`M` and `M ⊗[R] R` carry their `R`-module topologies. -/
noncomputable def ridL : M ⊗[R] R ≃L[R] M :=
  (TensorProduct.rid R M).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem toLinearEquiv_ridL : (ridL R M).toLinearEquiv = TensorProduct.rid R M :=
  LinearEquiv.toLinearEquiv_toContinuousLinearEquivOfIsModuleTopology _

theorem coe_ridL : ⇑(ridL R M) = TensorProduct.rid R M :=
  LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _

@[simp]
theorem ridL_tmul (m : M) (r : R) : ridL R M (m ⊗ₜ r) = r • m := by
  rw [coe_ridL, rid_tmul]

@[simp]
theorem ridL_symm_apply (m : M) : (ridL R M).symm m = m ⊗ₜ (1 : R) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, coe_ridL, rid_tmul, one_smul]

end rid

section lid

variable [TopologicalSpace (R ⊗[R] M)] [IsModuleTopology R (R ⊗[R] M)]

/-- The left unitor `R ⊗[R] M ≃ M`, `r ⊗ m ↦ r • m`, as a continuous linear equivalence when
`M` and `R ⊗[R] M` carry their `R`-module topologies. -/
noncomputable def lidL : R ⊗[R] M ≃L[R] M :=
  (TensorProduct.lid R M).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem toLinearEquiv_lidL : (lidL R M).toLinearEquiv = TensorProduct.lid R M :=
  LinearEquiv.toLinearEquiv_toContinuousLinearEquivOfIsModuleTopology _

theorem coe_lidL : ⇑(lidL R M) = TensorProduct.lid R M :=
  LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology _

@[simp]
theorem lidL_tmul (r : R) (m : M) : lidL R M (r ⊗ₜ m) = r • m := by
  rw [coe_lidL, lid_tmul]

@[simp]
theorem lidL_symm_apply (m : M) : (lidL R M).symm m = (1 : R) ⊗ₜ m := by
  rw [ContinuousLinearEquiv.symm_apply_eq, coe_lidL, lid_tmul, one_smul]

end lid

end TensorProduct

end
