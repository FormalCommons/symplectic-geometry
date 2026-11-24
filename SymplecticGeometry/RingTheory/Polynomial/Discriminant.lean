/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Nonvanishing of the discriminant

Mathlib defines the discriminant `Polynomial.discr f` of a polynomial and relates it to the
resultant of `f` and its derivative (`Polynomial.resultant_deriv`). This file shows that it does
not vanish in two situations.

* `Polynomial.discr_ne_zero_of_separable_map`: if `φ : A →+* K` is an injective ring map into a
  field of characteristic zero and the image of `f` over `K` is separable, then `f.discr ≠ 0`.
* `Irreducible.discr_ne_zero`: an irreducible polynomial of positive degree over a domain of
  characteristic zero with a gcd has nonzero discriminant. By Gauss's lemma it stays irreducible
  over the fraction field, where it is separable.

## References

* S. Lang, *Algebra*, Springer, 2002, Chapter IV, §2 and §8.
-/

public section

namespace Polynomial

/-- If an injective ring map `φ` into a field of characteristic zero takes `f` to a separable
polynomial, then the discriminant of `f` is nonzero. -/
theorem discr_ne_zero_of_separable_map {A K : Type*} [CommRing A] [Field K] [CharZero K]
    {φ : A →+* K} (hφ : Function.Injective φ) {f : A[X]} (hf : (f.map φ).Separable) :
    f.discr ≠ 0 := by
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim f 0, Polynomial.map_zero] at hf
    exact not_separable_zero hf
  by_cases hd : f.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd, discr_C]
    exact one_ne_zero
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero hd)
  have hres := resultant_ne_zero _ _ ((separable_def _).1 hf)
  rw [natDegree_derivative, derivative_map, natDegree_map_eq_of_injective hφ,
    resultant_map_map, resultant_deriv hdeg] at hres
  intro h
  simp [h] at hres

end Polynomial

/-- An irreducible polynomial of positive degree over a domain of characteristic zero with a gcd
has nonzero discriminant. -/
theorem Irreducible.discr_ne_zero {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    [CharZero R] {f : Polynomial R} (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    f.discr ≠ 0 := by
  have hirr : Irreducible (f.map (algebraMap R (FractionRing R))) :=
    ((hf.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map).1 hf
  exact Polynomial.discr_ne_zero_of_separable_map (IsFractionRing.injective R _) hirr.separable
