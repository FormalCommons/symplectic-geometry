/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import Mathlib.Tactic.FinCases

/-!
# Linear independence of a pair on which an alternating form is a non-zero-divisor

This file is a part of Tau Ceti's `TauCeti/LinearAlgebra/BilinearForm/Orthogonal.lean`, taken
from Tau Ceti's commit `7377e8195911055c9f05e0c07bb73e977f749a4a`; the pinned version of Tau Ceti
does not have this declaration yet. It sits in the sibling `FromTauCeti.lean` of
`SymplecticGeometry/LinearAlgebra/BilinearForm/Orthogonal.lean`, the path that the library keeps
for its own declarations on the subject. It holds one declaration of Tau Ceti's file:

* `LinearMap.BilinForm.IsAlt.linearIndependent_pair_of_mem_nonZeroDivisors`: two vectors whose
  value under an alternating form is a non-zero-divisor are linearly independent.

Changes: this module docstring; the imports, reduced to those this declaration needs: Mathlib's
`Mathlib.LinearAlgebra.BilinearForm.Orthogonal`, which Tau Ceti's file imports too, Tau Ceti's
`TauCeti/LinearAlgebra/BilinearForm/LinearIndependent.lean`, whose pinned version has
`LinearMap.BilinForm.linearIndependent_of_isUnit_det`, which the proof uses, and the module of
`fin_cases`; and the `universe` line that the variable declaration needs here. The statement, its
docstring, its proof and its comment are as in Tau Ceti.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §1.3 (orthogonal bases).
-/

public section

universe u v

namespace LinearMap.BilinForm

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

section HyperbolicPair

variable {B : LinearMap.BilinForm R M}

/-- Two vectors whose value under an alternating form is a non-zero-divisor are linearly
independent. -/
theorem IsAlt.linearIndependent_pair_of_mem_nonZeroDivisors (hB : B.IsAlt) {e f : M}
    (hd : B e f ∈ nonZeroDivisors R) : LinearIndependent R ![e, f] :=
  -- The Gram matrix of `![e, f]` is `B e f • !![0, 1; -1, 0]`, of determinant `1`.
  linearIndependent_of_isUnit_det (B := B) hd (G := !![0, 1; -1, 0])
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [hB.self_eq_zero, ← hB.neg_eq e f])
    (by simp)

end HyperbolicPair

end LinearMap.BilinForm

end
