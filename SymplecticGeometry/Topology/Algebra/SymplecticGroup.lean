/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Reindex
public import TauCeti.Topology.Algebra.SymplecticGroup

/-!
# Continuity of reindexing the symplectic group

Reindexing a symplectic matrix along an equivalence of index types
(`TauCeti.GLSymplectic.reindex`) permutes its entries, so it is continuous for the topology of
`TauCeti.GLSymplectic ι R` as a subgroup of the units of the matrix ring. This complements Tau
Ceti's file of the same name, which proves the continuity of the direct sum
`TauCeti.GLSymplectic.sum`.

## Main results

* `TauCeti.GLSymplectic.continuous_reindex`: reindexing is continuous.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2.
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [CommRing R]
  [TopologicalSpace R]

/-- Reindexing a symplectic matrix along an equivalence of index types is continuous. -/
@[continuity, fun_prop]
theorem continuous_reindex (e : ι ≃ κ) : Continuous (reindex R e) := by
  have hval : Continuous fun A : GLSymplectic ι R ↦
      ((A : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_val.comp continuous_subtypeVal
  have hinv : Continuous fun A : GLSymplectic ι R ↦
      (((A : GL (ι ⊕ ι) R)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    Units.continuous_coe_inv.comp continuous_subtypeVal
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (hval.matrix_reindex _ _).congr fun A ↦ (coe_coe_reindex e A).symm
  · refine (hinv.matrix_reindex (e.sumCongr e) (e.sumCongr e)).congr fun A ↦ ?_
    simp only [Function.comp_apply, ← Subgroup.coe_inv, ← map_inv, coe_coe_reindex]

end TauCeti.GLSymplectic

end
