/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.Matrix.Realify

/-!
# Realified unitary matrices and direct sums

Tau Ceti's `TauCeti.GLSymplectic.ofUnitary` sends a complex unitary matrix `U` to its
realification, a symplectic matrix. This file shows that it turns the block-diagonal sum
`Matrix.UnitaryGroup.sum` of unitary matrices into the direct sum `TauCeti.GLSymplectic.sum` of
symplectic matrices.

## Main results

* `TauCeti.GLSymplectic.sum_ofUnitary`: `ofUnitary U ⊕ ofUnitary U' = ofUnitary (diag(U, U'))`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 (the direct-sum axiom of Theorem 2.2.12).
-/

public section

open Matrix

namespace TauCeti.GLSymplectic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The direct sum of the realifications of unitary matrices `U` and `U'` is the realification
of their block-diagonal sum `diag(U, U')`. -/
theorem sum_ofUnitary (U : unitaryGroup ι ℂ) (U' : unitaryGroup κ ℂ) :
    sum (ofUnitary U, ofUnitary U') = ofUnitary (UnitaryGroup.sum (U, U')) :=
  Subtype.ext <| Units.ext <| by
    rw [coe_sum, coe_ofUnitary, coe_ofUnitary, coe_ofUnitary, UnitaryGroup.coe_sum,
      realify_fromBlocks_zero]

end TauCeti.GLSymplectic

end
