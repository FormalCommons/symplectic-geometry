/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Polynomial functions in the coordinates of a basis

Let `b` be a finite basis of a module `M` over a commutative ring `R`. A function `f : M → R` is
a polynomial in the coordinates of `b` if `f p = P (b.equivFun p)` for a multivariate polynomial
`P` over `R` in the indices of `b`. These functions are the range of the algebra map
`MvPolynomial ι R → (M → R)` that sends the variable `X i` to the `i`-th coordinate function, so
they form a subalgebra.

## Main definitions

* `Module.Basis.polynomialFunctions b`: the subalgebra of `M → R` of the polynomials in the
  coordinates of `b`.

## Main results

* `Module.Basis.mem_polynomialFunctions_iff`: `f` is in it exactly when `f p = P (b.equivFun p)`
  for some `P`.
* `Module.Basis.linearMap_mem_polynomialFunctions`: linear functionals are polynomial functions.
* `Module.Basis.bilin_apply_mem_polynomialFunctions`: `p ↦ β (f p) (g p)` is a polynomial
  function for a bilinear form `β` whose left argument ranges over a finite free module, if
  `f` and `g` are polynomial maps, in the sense that their composites with linear functionals
  are polynomial functions.
-/

public section

noncomputable section

namespace Module.Basis

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
  (b : Basis ι R M)

/-- The subalgebra of the functions `M → R` that are polynomials in the coordinates of the
finite basis `b`: the functions `p ↦ MvPolynomial.eval (b.equivFun p) P` for
`P : MvPolynomial ι R` (`Module.Basis.mem_polynomialFunctions_iff`). -/
def polynomialFunctions : Subalgebra R (M → R) :=
  (MvPolynomial.aeval fun i p ↦ b.equivFun p i).range

theorem polynomialFunctions_def :
    b.polynomialFunctions = (MvPolynomial.aeval fun i p ↦ b.equivFun p i).range :=
  (rfl)

/-- A function lies in `b.polynomialFunctions` exactly when it is
`p ↦ MvPolynomial.eval (b.equivFun p) P` for a polynomial `P`. -/
theorem mem_polynomialFunctions_iff {f : M → R} :
    f ∈ b.polynomialFunctions ↔
      ∃ P : MvPolynomial ι R, ∀ p, MvPolynomial.eval (b.equivFun p) P = f p := by
  have h (P : MvPolynomial ι R) (p : M) :
      MvPolynomial.aeval (fun i p ↦ b.equivFun p i) P p = MvPolynomial.eval (b.equivFun p) P := by
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => rw [map_add, Pi.add_apply, hP, hQ, map_add]
    | mul_X P i hP =>
      rw [map_mul, Pi.mul_apply, hP, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]
  simp only [polynomialFunctions_def, AlgHom.mem_range, funext_iff, h]

/-- The coordinate functions of `b` are polynomial functions. -/
theorem equivFun_apply_mem_polynomialFunctions (i : ι) :
    (fun p ↦ b.equivFun p i) ∈ b.polynomialFunctions :=
  ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ i⟩

/-- Every linear functional on `M` is a polynomial function in the coordinates of `b`. -/
theorem linearMap_mem_polynomialFunctions (ℓ : M →ₗ[R] R) : ⇑ℓ ∈ b.polynomialFunctions := by
  have := Fintype.ofFinite ι
  have hℓ : ⇑ℓ = ∑ i, ℓ (b i) • fun p ↦ b.equivFun p i := by
    ext p
    conv_lhs => rw [← b.sum_equivFun p]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_apply, Pi.smul_apply, mul_comm]
  rw [hℓ]
  exact Subalgebra.sum_mem _ fun i _ ↦
    Subalgebra.smul_mem _ (b.equivFun_apply_mem_polynomialFunctions i) _

/-- For a bilinear form `β` whose left argument ranges over a finite free module, the function
`p ↦ β (f p) (g p)` is a polynomial function in the coordinates of `b` if the composites of `f`
and of `g` with every linear functional are. -/
theorem bilin_apply_mem_polynomialFunctions {W₁ W₂ : Type*} [AddCommGroup W₁] [Module R W₁]
    [Module.Free R W₁] [Module.Finite R W₁] [AddCommGroup W₂] [Module R W₂]
    (β : W₁ →ₗ[R] W₂ →ₗ[R] R) {f : M → W₁} {g : M → W₂}
    (hf : ∀ ℓ : Module.Dual R W₁, (fun p ↦ ℓ (f p)) ∈ b.polynomialFunctions)
    (hg : ∀ ℓ : Module.Dual R W₂, (fun p ↦ ℓ (g p)) ∈ b.polynomialFunctions) :
    (fun p ↦ β (f p) (g p)) ∈ b.polynomialFunctions := by
  let c := Module.Free.chooseBasis R W₁
  have hβ : (fun p ↦ β (f p) (g p)) =
      ∑ i, (fun p ↦ c.coord i (f p)) * fun p ↦ β (c i) (g p) := by
    ext p
    conv_lhs => rw [← c.sum_repr (f p)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.sum_apply, Pi.mul_apply, Basis.coord_apply]
  rw [hβ]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _ (hf _) (hg _)

end Module.Basis

end
