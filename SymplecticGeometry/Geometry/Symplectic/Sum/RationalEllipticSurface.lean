/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import SymplecticGeometry.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The rational elliptic surface

The rational elliptic surface `E(1)` is the total space of the Hesse pencil of plane cubics: the
hypersurface `s (x³ + y³ + z³) + t x y z = 0` of `ℂℙ² × ℂℙ¹`. This file starts with the algebra of
its equation, which does not depend on any manifold structure.

The variables are indexed by `Fin 3 ⊕ Fin 2`: `Sum.inl 0`, `Sum.inl 1`, `Sum.inl 2` are the
homogeneous coordinates `x, y, z` of the plane, and `Sum.inr 0`, `Sum.inr 1` are the homogeneous
coordinates `s, t` of the line. A point of the cone `K³ × K²` is written `Sum.elim v w`.

## Main declarations

* `SymplecticGeometry.hessePencil R`: the polynomial `s (x³ + y³ + z³) + t x y z`.
* `SymplecticGeometry.eval_hessePencil` and the lemmas `pderiv_inl_zero_hessePencil`, …,
  `pderiv_inr_one_hessePencil`: its evaluation and its five partial derivatives.
* `SymplecticGeometry.isWeightedHomogeneous_hessePencil`: it is weighted homogeneous of degree
  `3 a + b` for the weights `a` on `x, y, z` and `b` on `s, t`; the special cases
  `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inl` and
  `SymplecticGeometry.isWeightedHomogeneous_hessePencil_inr` say that it is bihomogeneous of
  bidegree `(3, 1)`.
* `SymplecticGeometry.sum_mul_eval_pderiv_inl_hessePencil` and
  `SymplecticGeometry.sum_mul_eval_pderiv_inr_hessePencil`: the two Euler relations.
* `SymplecticGeometry.exists_eval_pderiv_hessePencil_ne_zero`: over a field in which `3 ≠ 0`, at
  every point `(v, w)` with `v ≠ 0` and `w ≠ 0` some partial derivative is nonzero; in particular
  the hypersurface is smooth.
* `SymplecticGeometry.exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero`: in the affine chart
  where `v i ≠ 0` and `w j ≠ 0`, the nonzero partial derivative can be taken in a variable other
  than `Sum.inl i` and `Sum.inr j`, that is, in a coordinate of the chart. The step from the cone
  to the chart is `MvPolynomial.IsWeightedHomogeneous.eval_pderiv_eq_zero_of_eval_eq_zero`,
  applied to each of the two blocks of coordinates.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.2.
* [R. E. Gompf, *A new construction of symplectic manifolds*][Gompf1995].
-/

public section

open MvPolynomial

namespace SymplecticGeometry

variable (R : Type*) [CommSemiring R]

/-- The equation of the Hesse pencil, `s (x³ + y³ + z³) + t x y z`, in the variables
`x, y, z = Sum.inl 0, Sum.inl 1, Sum.inl 2` and `s, t = Sum.inr 0, Sum.inr 1`. -/
noncomputable def hessePencil : MvPolynomial (Fin 3 ⊕ Fin 2) R :=
  X (.inr 0) * (X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3) +
    X (.inr 1) * (X (.inl 0) * X (.inl 1) * X (.inl 2))

theorem hessePencil_def : hessePencil R =
    X (.inr 0) * (X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3) +
      X (.inr 1) * (X (.inl 0) * X (.inl 1) * X (.inl 2)) :=
  (rfl)

variable {R}

@[simp]
theorem eval_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    eval p (hessePencil R) = p (.inr 0) * (p (.inl 0) ^ 3 + p (.inl 1) ^ 3 + p (.inl 2) ^ 3) +
      p (.inr 1) * (p (.inl 0) * p (.inl 1) * p (.inl 2)) := by
  simp [hessePencil_def]

@[simp]
theorem pderiv_inl_zero_hessePencil :
    pderiv (.inl 0) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 0) ^ 2 + X (.inr 1) * (X (.inl 1) * X (.inl 2)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_one_hessePencil :
    pderiv (.inl 1) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 1) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 2)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inl_two_hessePencil :
    pderiv (.inl 2) (hessePencil R) =
      3 * X (.inr 0) * X (.inl 2) ^ 2 + X (.inr 1) * (X (.inl 0) * X (.inl 1)) := by
  simp [hessePencil_def, pderiv_X]
  ring

@[simp]
theorem pderiv_inr_zero_hessePencil :
    pderiv (.inr 0) (hessePencil R) = X (.inl 0) ^ 3 + X (.inl 1) ^ 3 + X (.inl 2) ^ 3 := by
  simp [hessePencil_def, pderiv_X]

@[simp]
theorem pderiv_inr_one_hessePencil :
    pderiv (.inr 1) (hessePencil R) = X (.inl 0) * X (.inl 1) * X (.inl 2) := by
  simp [hessePencil_def, pderiv_X]

/-- The Hesse pencil is weighted homogeneous of degree `3 a + b` when `x, y, z` have weight `a`
and `s, t` have weight `b`. -/
theorem isWeightedHomogeneous_hessePencil (a b : ℕ) :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim (fun _ ↦ a) (fun _ ↦ b)) (3 * a + b) := by
  have hX (i : Fin 3) :=
    isWeightedHomogeneous_X R (Sum.elim (fun _ : Fin 3 ↦ a) (fun _ : Fin 2 ↦ b)) (.inl i)
  have hY (j : Fin 2) :=
    isWeightedHomogeneous_X R (Sum.elim (fun _ : Fin 3 ↦ a) (fun _ : Fin 2 ↦ b)) (.inr j)
  simp only [Sum.elim_inl, Sum.elim_inr] at hX hY
  have hxyz := ((hX 0).mul (hX 1)).mul (hX 2)
  rw [show a + a + a = 3 • a by rw [smul_eq_mul]; ring] at hxyz
  rw [hessePencil_def]
  convert ((hY 0).mul (((hX 0).pow 3).add ((hX 1).pow 3) |>.add ((hX 2).pow 3))).add
    ((hY 1).mul hxyz) using 1
  rw [smul_eq_mul, add_comm]

/-- The Hesse pencil is homogeneous of degree `3` in the coordinates `x, y, z` of the plane. -/
theorem isWeightedHomogeneous_hessePencil_inl :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim (1 : Fin 3 → ℕ) 0) 3 :=
  isWeightedHomogeneous_hessePencil 1 0

/-- The Hesse pencil is homogeneous of degree `1` in the coordinates `s, t` of the line. -/
theorem isWeightedHomogeneous_hessePencil_inr :
    (hessePencil R).IsWeightedHomogeneous (Sum.elim 0 (1 : Fin 2 → ℕ)) 1 :=
  isWeightedHomogeneous_hessePencil 0 1

/-- Euler's relation for the plane coordinates: `x ∂ₓP + y ∂ᵧP + z ∂_zP = 3 P`. -/
theorem sum_mul_eval_pderiv_inl_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    ∑ k : Fin 3, p (.inl k) * eval p (pderiv (.inl k) (hessePencil R)) =
      3 * eval p (hessePencil R) := by
  have h := congrArg (eval p) isWeightedHomogeneous_hessePencil_inl.sum_weight_X_mul_pderiv
  simpa [Fintype.sum_sum_type, nsmul_eq_mul] using h

/-- Euler's relation for the line coordinates: `s ∂ₛP + t ∂ₜP = P`. -/
theorem sum_mul_eval_pderiv_inr_hessePencil (p : Fin 3 ⊕ Fin 2 → R) :
    ∑ k : Fin 2, p (.inr k) * eval p (pderiv (.inr k) (hessePencil R)) =
      eval p (hessePencil R) := by
  have h := congrArg (eval p) isWeightedHomogeneous_hessePencil_inr.sum_weight_X_mul_pderiv
  simp only [nsmul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, Pi.zero_apply, Nat.cast_zero,
    zero_mul, Finset.sum_const_zero, Sum.elim_inr, Pi.one_apply, Nat.cast_one, one_mul, zero_add,
    map_sum, map_mul, eval_X, one_smul] at h
  exact h

variable {K : Type*} [Field K]

/-- **The Hesse pencil is smooth.** Over a field in which `3 ≠ 0`, the partial derivatives of the
Hesse pencil have no common zero `(v, w)` with `v ≠ 0` and `w ≠ 0`; in particular none on its
zero set. The hypothesis `3 ≠ 0` is needed: in characteristic `3` they all vanish at
`v = (1, -1, 0)`, `w = (1, 0)`. -/
theorem exists_eval_pderiv_hessePencil_ne_zero (h3 : (3 : K) ≠ 0) {v : Fin 3 → K}
    (hv : v ≠ 0) {w : Fin 2 → K} (hw : w ≠ 0) :
    ∃ k, eval (Sum.elim v w) (pderiv k (hessePencil K)) ≠ 0 := by
  by_contra! H
  have h00 := H (.inl 0)
  have h01 := H (.inl 1)
  have h02 := H (.inl 2)
  have h10 := H (.inr 0)
  have h11 := H (.inr 1)
  simp only [pderiv_inl_zero_hessePencil, pderiv_inl_one_hessePencil,
    pderiv_inl_two_hessePencil, pderiv_inr_zero_hessePencil, pderiv_inr_one_hessePencil, map_add,
    map_mul, map_pow, eval_X, Sum.elim_inl, Sum.elim_inr, map_ofNat] at h00 h01 h02 h10 h11
  have key : (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) ∨ (w 0 = 0 ∧ w 1 = 0) := by grind
  rcases key with ⟨h0, h1, h2⟩ | ⟨h0, h1⟩
  · exact hv (funext fun k ↦ by fin_cases k <;> assumption)
  · exact hw (funext fun k ↦ by fin_cases k <;> assumption)

/-- In the affine chart of `ℙ² × ℙ¹` where `v i ≠ 0` and `w j ≠ 0`, a zero of the Hesse pencil has
a nonzero partial derivative in a variable other than `Sum.inl i` and `Sum.inr j`, that is, in a
coordinate of the chart. -/
theorem exists_eval_pderiv_hessePencil_ne_zero_of_ne_zero (h3 : (3 : K) ≠ 0) {v : Fin 3 → K}
    {w : Fin 2 → K} {i : Fin 3} {j : Fin 2} (hi : v i ≠ 0) (hj : w j ≠ 0)
    (h : eval (Sum.elim v w) (hessePencil K) = 0) :
    ∃ k, k ≠ .inl i ∧ k ≠ .inr j ∧ eval (Sum.elim v w) (pderiv k (hessePencil K)) ≠ 0 := by
  by_contra! H
  obtain ⟨k, hk⟩ := exists_eval_pderiv_hessePencil_ne_zero h3 (v := v) (w := w)
    (fun hv ↦ hi (congrFun hv i)) (fun hw ↦ hj (congrFun hw j))
  refine hk ?_
  rcases k with l | l
  · obtain rfl | hl := eq_or_ne l i
    · refine isWeightedHomogeneous_hessePencil_inl.eval_pderiv_eq_zero_of_eval_eq_zero h
        (by simpa using hi) (by simp) fun k hk hwk ↦ ?_
      rcases k with k | k
      · exact H _ hk (by simp)
      · simp at hwk
    · exact H _ (by simpa using hl) (by simp)
  · obtain rfl | hl := eq_or_ne l j
    · refine isWeightedHomogeneous_hessePencil_inr.eval_pderiv_eq_zero_of_eval_eq_zero h
        (by simpa using hj) (by simp) fun k hk hwk ↦ ?_
      rcases k with k | k
      · simp at hwk
      · exact H _ (by simp) hk
    · exact H _ (by simp) (by simpa using hl)

end SymplecticGeometry

end
