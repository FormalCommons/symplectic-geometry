/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic

/-!
# Singular cap products along unitors

Tau Ceti computes the cap product of a singular simplex with a singular cochain along an
arbitrary coefficient morphism `u : T ⟶ R ⊗ S` and pairing `μ : M ⊗ S ⟶ P`
(`TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal`). This file specializes that formula to
the two choices of unitors used in practice:

* `TopCat.ιChainComplex_capChain_rightUnitor`: along `u = (ρ_ R).inv` and `μ = (ρ_ M).hom`, as in
  Tau Ceti's duality map, capping a simplex `σ` with `ψ` is `ψ(σ|[0, …, p]) σ|[p, …, n]`;
* `TopCat.ιChainComplex_capChain_leftUnitor_unit`: the same for coefficients and values in the
  tensor unit, along the left unitors, as in `TopCat.singularCapLinearMap`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Simplicial

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [Semiring k] [Linear k C] [MonoidalLinear k C]
  (X : TopCat.{w})

/-- Capping a singular simplex `σ` with a cochain `ψ` along the right unitors is
`ψ(σ|[0, …, p]) σ|[p, …, n]`: the coefficient morphism `ψ` on the front `p`-face, followed by the
inclusion of the back `q`-face. -/
theorem ιChainComplex_capChain_rightUnitor {R M : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)] {p q n : ℕ}
    (h : p + q = n) (ψ : ((toSSet.obj X).chainComplex R).X p ⟶ M) (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal (ρ_ R).inv)
          ((toSSet.obj X).chainComplexPairing (ρ_ M).hom) p q n h ψ =
      ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ ψ) ≫
        (toSSet.obj X).ιChainComplex
          ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  rw [ιChainComplex_capChain_alexanderWhitneyDiagonal, rightUnitor_naturality_assoc,
    Iso.inv_hom_id_assoc]

/-- Capping a singular simplex `σ` with a cochain `φ` with coefficients and values in the tensor
unit, along its left unitor, as in `TopCat.singularCapLinearMap`, is `φ(σ|[0, …, p]) σ|[p, …, n]`.
-/
theorem ιChainComplex_capChain_leftUnitor_unit
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))] {p q n : ℕ}
    (h : p + q = n) (φ : ((toSSet.obj X).chainComplex (𝟙_ C)).X p ⟶ 𝟙_ C)
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal (λ_ (𝟙_ C)).inv)
          ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ C)).hom) p q n h φ =
      ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ≫
        (toSSet.obj X).ιChainComplex
          ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  rw [unitors_equal, unitors_inv_equal, ιChainComplex_capChain_rightUnitor]

end TopCat

end
