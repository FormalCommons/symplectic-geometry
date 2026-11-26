/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Roots
import TauCeti.RingTheory.MvPolynomial.LineRestriction

/-!
# Zeros of a multivariate polynomial on a line

On the line `s ↦ a + s • v`, a multivariate polynomial `P` over an integral domain is a
polynomial in `s` whose coefficient of degree `P.totalDegree` is the top homogeneous component of
`P` at `v` (Tau Ceti's `MvPolynomial.coeff_eval₂_C_add_C_mul_X_of_totalDegree_le`). So if that
component does not vanish at `v`, then `P` has at most `P.totalDegree` zeros on the line
(`MvPolynomial.encard_setOfPred_eval_add_smul_eq_zero_le`).
-/

public section

open Set

namespace MvPolynomial

/-- If the top homogeneous component of `P` does not vanish at `v`, then `P` vanishes at at most
`P.totalDegree` points of each line `s ↦ a + s • v`: its restriction to the line is a nonzero
polynomial in `s` of degree at most `P.totalDegree`. -/
theorem encard_setOfPred_eval_add_smul_eq_zero_le {σ R : Type*} [CommRing R] [IsDomain R]
    {P : MvPolynomial σ R} (a v : σ → R)
    (hv : eval v (homogeneousComponent P.totalDegree P) ≠ 0) :
    {s : R | eval (a + s • v) P = 0}.encard ≤ P.totalDegree := by
  classical
  set p : Polynomial R :=
    aeval (fun i ↦ Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) P
  have hcoeff : p.coeff P.totalDegree = eval v (homogeneousComponent P.totalDegree P) := by
    simpa [p, aeval_def, Polynomial.algebraMap_eq] using
      coeff_eval₂_C_add_C_mul_X_of_totalDegree_le P (RingHom.id R) a v le_rfl
  have hp : p ≠ 0 := fun h ↦ hv (by rw [← hcoeff, h, Polynomial.coeff_zero])
  have hdeg : p.natDegree ≤ P.totalDegree := by
    simpa [p, aeval_def, Polynomial.algebraMap_eq] using
      natDegree_eval₂_C_add_C_mul_X_le P (RingHom.id R) a v
  calc {s : R | eval (a + s • v) P = 0}.encard ≤ (p.roots.toFinset : Set R).encard := by
        refine encard_le_encard fun s hs ↦ ?_
        simpa [Polynomial.mem_roots hp, p] using hs
    _ ≤ P.totalDegree := by
      rw [encard_coe_eq_coe_finsetCard, Nat.cast_le]
      exact (p.roots.toFinset_card_le.trans p.card_roots').trans hdeg

end MvPolynomial

end
