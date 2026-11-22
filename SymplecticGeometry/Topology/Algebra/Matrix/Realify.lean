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
# Realification as a continuous linear map, and realified unitary matrices

Realification `Matrix.realify` is `ℝ`-linear (Tau Ceti's `Matrix.realifyLinearMap`) between
finite-dimensional real vector spaces, so it is a continuous linear map, `Matrix.realifyCLM`.
Hence `ContinuousLinearMap.contDiff` makes realification smooth of every order, for the
entrywise norms `Matrix.Norms.Elementwise` as well as the operator norms
`Matrix.Norms.L2Operator`, since both induce the entrywise topology.

Tau Ceti's `TauCeti.GLSymplectic.ofUnitary` sends a complex unitary matrix `U` to its
realification, a symplectic matrix. This file shows that it turns the block-diagonal sum
`Matrix.UnitaryGroup.sum` of unitary matrices into the direct sum `TauCeti.GLSymplectic.sum` of
symplectic matrices. It sits beside Tau Ceti's `TauCeti.Topology.Algebra.Matrix.Realify`, where
`ofUnitary` is defined, so that the lemma can join `ofUnitary` there.

## Main results

* `Matrix.realifyCLM`: realification of matrices, as a continuous `ℝ`-linear map.
* `TauCeti.GLSymplectic.sum_ofUnitary`: `ofUnitary U ⊕ ofUnitary U' = ofUnitary (diag(U, U'))`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 (the direct-sum axiom of Theorem 2.2.12).
-/

public section

namespace Matrix

variable (m n 𝕜 : Type*) [Finite m] [Finite n] [RCLike 𝕜]

/-- Realification of matrices `Matrix.realify`, as a continuous `ℝ`-linear map for the entrywise
topologies. -/
noncomputable def realifyCLM : Matrix m n 𝕜 →L[ℝ] Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  (realifyLinearMap m n 𝕜).toContinuousLinearMap

variable {m n 𝕜}

/-- `Matrix.realifyCLM` applied to `A` is the realification of `A`. -/
@[simp]
theorem realifyCLM_apply (A : Matrix m n 𝕜) : realifyCLM m n 𝕜 A = A.realify :=
  realifyLinearMap_apply A

/-- As a function, `Matrix.realifyCLM` is `Matrix.realify`. -/
theorem coe_realifyCLM : ⇑(realifyCLM m n 𝕜) = realify :=
  funext realifyCLM_apply

end Matrix

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
