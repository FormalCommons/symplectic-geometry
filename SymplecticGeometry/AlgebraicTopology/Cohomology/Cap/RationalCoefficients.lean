/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic

/-!
# The cap product with integral and with rational chains

Tau Ceti has two settings for the cap product of a space `X`. Its duality map
`TauCeti.HomologicalOrientation.dualityMap` caps integral chains, with coefficients
`ModuleCat.of ℤ (ULift ℤ)`, against cochains with values in an abelian group `L`, while
`TopCat.singularCapLinearMap ℚ` caps rational chains, with coefficients `𝟙_ (ModuleCat ℚ)`,
against `ℚ`-linear cochains. This file compares the two for `L = ℚ`. Throughout, `F` is the
restriction of scalars along `ℤ → ℚ`, through which an object of `ModuleCat ℚ` is read as an
abelian group.

* `TopCat.singularChainComplexRestrictScalarsRatIso`: the rational chains, read as abelian groups,
  are the chains with coefficients in the abelian group `ℚ`.
* `TopCat.singularChainComplexIntToRat`: the chain map `C(X; ℤ) ⟶ F (C(X; ℚ))` induced by the
  inclusion `ℤ → ℚ` of coefficients (`TauCeti.intToRatCoeff`), and the induced map on homology
  `TopCat.singularHomologyIntToRat : Hₙ(X; ℤ) ⟶ F (Hₙ(X; ℚ))`. For an oriented compact
  manifold, it sends the integral fundamental class to a rational one. For a connected
  manifold Tau Ceti also has `TauCeti.HomologicalOrientation.rationalFundamentalClass`, built
  by extension of scalars; this file does not compare the two.
* `TopCat.singularCochainComplexRatToInt`: restricting a `ℚ`-linear cochain on rational chains to
  integral chains, `φ ↦ φ ∘ ι`. Both cochain groups are functions on singular simplices
  (`TopCat.bijective_singularCochainRatToInt`), since a `ℚ`-linear map on the free `ℚ`-module on
  the simplices is determined by its values on them, as is a `ℤ`-linear map on the free abelian
  group. This is extension of scalars being left adjoint to restriction. Hence an isomorphism
  `TopCat.singularCohomologyRatIso : F (Hᵖ(X; ℚ)) ≅ Hᵖ(X; ℤ, ℚ)` of cohomology computed from
  rational chains with cohomology computed from integral chains with values in `ℚ`.
* `TopCat.singularHomologyRatIso : F (H_q(X; ℚ)) ≅ H_q(X; ℤ, ℚ)`: homology with rational chains,
  read as an abelian group, is homology with coefficients in the abelian group `ℚ`.

The main result is that the two cap products agree under these identifications
(`TopCat.singularCap_singularCohomologyRatIso_hom`): for `α ∈ Hᵖ(X; ℚ)` and `μ ∈ Hₙ(X; ℤ)`,
capping `μ` with the integral class of `α` is the rational cap product of `α` with the image of
`μ`. It is checked on simplices, where both sides evaluate the cochain on the front `p`-face and
keep the back `q`-face (`TopCat.capChain_singularCochainRatToInt`).

As a consequence, for a compact oriented manifold, injectivity of the duality map with values in
`ℚ` in degree `p` gives injectivity on `Hᵖ(M; ℚ)` of the rational cap product with the rational
fundamental class
(`TauCeti.HomologicalOrientation.injective_singularCapLinearMap_of_injective_dualityMap`), which
is the hypothesis of Tau Ceti's evenness criterion
`TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`.

## Implementation notes

The comparison of homologies is the one of Tau Ceti's `TopCat.singularHomologyModTwoIso` for
`ℤ → ℤ/2`, which uses `CategoryTheory.Functor.singularHomologyFunctorObjCompIso`. Here it is
built from Mathlib's simplicial `SSet.chainComplexFunctorObjCompMapIso` instead, whose value on a
simplex Mathlib computes (`SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f`).
The bijectivity of the cochain comparison uses the values on simplices of
`TauCeti.cochainValuesEquiv`, as Tau Ceti's `TauCeti.simplicialCochainComplexIntegralIso` does.
As in Tau Ceti's `Duality.lean`, `CategoryTheory.MonoidalPreadditive.monoidalLinearInt` is a
local instance, so that the integral cap product is the one of the duality map.

Several objects here agree only up to unfolding `ModuleCat.restrictScalars` or Mathlib's
`singularHomologyFunctor`, for instance the cycles of `F` applied to a complex and the cycles of
the complex itself. Where `rw` cannot see such an identification, proofs paste equalities as terms
or use `erw`, and say so.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (change of
  coefficients) and Section 3.3 (the cap product).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Simplicial

namespace TauCeti

/-- The coefficient map `ℤ → ℚ`, from the integral coefficients `ULift ℤ` of the fundamental class
to the abelian group `ℚ`. -/
def intToRatCoeff : ModuleCat.of ℤ (ULift.{0} ℤ) ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom ((Int.castAddHom ℚ).toIntLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap)

/-- The coefficient map `ℤ → ℚ` is the cast of integers to rationals. -/
@[simp]
theorem intToRatCoeff_apply (m : ULift.{0} ℤ) : intToRatCoeff m = (m.down : ℚ) :=
  (rfl)

end TauCeti

namespace TopCat

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

open TauCeti

/-! ### Cap products along unitors, on a simplex -/

section Unitor

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [Semiring k] [Linear k C] [MonoidalLinear k C]
  (X : TopCat.{0})

/-- Capping a singular simplex `σ` with a cochain `ψ` along the right unitors is
`ψ(σ|[0, …, p]) σ|[p, …, n]`: the coefficient morphism `ψ` on the front `p`-face, followed by the
inclusion of the back `q`-face. -/
theorem ιChainComplex_capChain_rightUnitor {R M : C}
    [∀ J : Type, PreservesColimitsOfShape (Discrete J) (tensorLeft M)] {p q n : ℕ}
    (h : p + q = n) (ψ : ((toSSet.obj X).chainComplex R).X p ⟶ M) (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        ChainComplex.capChain k (X.alexanderWhitneyDiagonal (ρ_ R).inv)
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
    [∀ J : Type, PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))] {p q n : ℕ}
    (h : p + q = n) (φ : ((toSSet.obj X).chainComplex (𝟙_ C)).X p ⟶ 𝟙_ C)
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        ChainComplex.capChain k (X.alexanderWhitneyDiagonal (λ_ (𝟙_ C)).inv)
          ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ C)).hom) p q n h φ =
      ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ≫
        (toSSet.obj X).ιChainComplex
          ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  rw [unitors_equal, unitors_inv_equal, ιChainComplex_capChain_rightUnitor]

end Unitor

variable (X : TopCat.{0})

/-! ### Chains -/

/-- The singular chains with rational coefficients, read as abelian groups, are the singular
chains with coefficients in the abelian group `ℚ`. -/
def singularChainComplexRestrictScalarsRatIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))) ≅
      (toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ) :=
  (SSet.chainComplexFunctorObjCompMapIso
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)) (𝟙_ (ModuleCat.{0} ℚ))).app (toSSet.obj X) ≪≫
    ((SSet.chainComplexFunctor _).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ)).app (toSSet.obj X)

/-- The identification of rational chains with chains with coefficients in the abelian group `ℚ`
keeps each singular simplex. -/
@[reassoc]
theorem map_ιChainComplex_singularChainComplexRestrictScalarsRatIso_hom_f {n : ℕ}
    (σ : (toSSet.obj X) _⦋n⦌) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ) ≫
      X.singularChainComplexRestrictScalarsRatIso.hom.f n =
    (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom ≫
      (toSSet.obj X).ιChainComplex σ := by
  have h := SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)) (R := 𝟙_ (ModuleCat.{0} ℚ))
    (X := toSSet.obj X) σ
  rw [singularChainComplexRestrictScalarsRatIso]
  -- The composite is stated with the image under a composite functor, which `Iso.trans_hom`
  -- sees as the image complex only after unfolding `Functor.comp`.
  erw [Iso.trans_hom, HomologicalComplex.comp_f, reassoc_of% h]
  exact SSet.ιChainComplex_chainComplexFunctor_map_app_f _ _

/-- The inverse identification of chains with coefficients in the abelian group `ℚ` with rational
chains keeps each singular simplex. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_singularChainComplexRestrictScalarsRatIso_inv_f {n : ℕ}
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ X.singularChainComplexRestrictScalarsRatIso.inv.f n =
      (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).inv ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ) := by
  rw [← cancel_mono (X.singularChainComplexRestrictScalarsRatIso.hom.f n)]
  simp only [Category.assoc]
  rw [map_ιChainComplex_singularChainComplexRestrictScalarsRatIso_hom_f,
    Iso.inv_hom_id_assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
    Category.comp_id]

/-- The chain map from integral to rational singular chains, read as abelian groups, induced by
the inclusion `ℤ → ℚ` of coefficients. -/
def singularChainComplexIntToRat :
    (toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟶
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))) :=
  ((SSet.chainComplexFunctor _).map intToRatCoeff).app (toSSet.obj X) ≫
    X.singularChainComplexRestrictScalarsRatIso.inv

/-- The chain map from integral to rational chains keeps each singular simplex and casts its
coefficient to `ℚ`. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_singularChainComplexIntToRat_f {n : ℕ} (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ X.singularChainComplexIntToRat.f n =
      intToRatCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).inv ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ) := by
  rw [singularChainComplexIntToRat, HomologicalComplex.comp_f,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc,
    ιChainComplex_singularChainComplexRestrictScalarsRatIso_inv_f]

/-! ### Cochains -/

/-- Restriction of a `ℚ`-linear cochain of degree `p` on rational singular chains to integral
singular chains, `φ ↦ φ ∘ ι`, with values in the abelian group `ℚ`. -/
def singularCochainRatToInt (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).obj
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).X p) ⟶
      (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℚ)).X p :=
  let f : (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) →+
      (((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p ⟶ ModuleCat.of ℤ ℚ) :=
    { toFun φ := X.singularChainComplexIntToRat.f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map φ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom
      map_zero' := by simp
      map_add' φ ψ := by simp }
  -- The integers act on the restricted module through `ℚ`, so `ℤ`-linearity is the
  -- compatibility of additive maps with integer multiples.
  ModuleCat.ofHom { f with map_smul' := map_intCast_smul f ℤ ℤ }

/-- The restriction of a cochain `φ` to integral chains is `φ` precomposed with the chain map
from integral to rational chains. -/
theorem singularCochainRatToInt_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    X.singularCochainRatToInt p φ = X.singularChainComplexIntToRat.f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map φ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom :=
  (rfl)

/-- The restriction of a cochain `φ` takes the integral chain `a σ` to `a φ(σ)`. -/
theorem singularCochainRatToInt_apply_ιChainComplex {p : ℕ} (σ : (toSSet.obj X) _⦋p⦌)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ))
    (a : ULift.{0} ℤ) :
    ConcreteCategory.hom (X := ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p)
        (Y := ModuleCat.of ℤ ℚ) (X.singularCochainRatToInt p φ)
        ((toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ a) =
      (a.down : ℚ) * φ ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ 1) := by
  rw [singularCochainRatToInt_apply, ← ModuleCat.comp_apply,
    ιChainComplex_singularChainComplexIntToRat_f_assoc, ← smul_eq_mul, ← map_smul, ← map_smul,
    smul_eq_mul, mul_one]
  -- The identifications of a restricted module with the abelian group `ℚ`, and restrictions of
  -- scalars of morphisms, are the identity on elements, but their evaluation lemmas are stated
  -- for the underlying types, which `rw` does not identify with the carriers here.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ModuleCat.restrictScalarsAlgebraMapIso_hom_apply,
    ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsAlgebraMapIso_inv_apply, intToRatCoeff_apply,
    ModuleCat.restrictScalars.map_apply]

/-- **Restriction of cochains to integral chains is bijective**: a `ℚ`-linear cochain on rational
chains and a `ℤ`-linear cochain on integral chains with values in `ℚ` are both determined by
arbitrary values on the singular simplices. -/
theorem bijective_singularCochainRatToInt (p : ℕ) :
    Function.Bijective (X.singularCochainRatToInt p) := by
  constructor
  · intro φ₁ φ₂ hφ
    refine SSet.chainComplex_hom_ext fun σ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    have h₁ := X.singularCochainRatToInt_apply_ιChainComplex σ φ₁ ⟨1⟩
    rw [hφ, X.singularCochainRatToInt_apply_ιChainComplex σ φ₂ ⟨1⟩, Int.cast_one, one_mul,
      one_mul] at h₁
    exact h₁.symm
  · intro (ψ : ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p ⟶
      ModuleCat.of ℤ ℚ)
    refine ⟨(cochainValuesEquiv ℚ (𝟙_ (ModuleCat.{0} ℚ)) (toSSet.obj X) p).symm
      fun σ ↦ ψ ((toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ ⟨1⟩), ?_⟩
    refine SSet.chainComplex_hom_ext fun σ ↦ ?_
    -- a morphism out of `ULift ℤ` is determined by its value at `1`
    ext ⟨a⟩
    have ha : (⟨a⟩ : ModuleCat.of ℤ (ULift.{0} ℤ)) =
        a • (⟨1⟩ : ModuleCat.of ℤ (ULift.{0} ℤ)) := by
      ext
      simp
    rw [ha, LinearMap.map_smul, LinearMap.map_smul]
    refine congrArg (a • ·) ((X.singularCochainRatToInt_apply_ιChainComplex σ _ ⟨1⟩).trans ?_)
    rw [Int.cast_one, one_mul]
    exact (cochainValuesEquiv_symm_apply ℚ _ _ p _ σ 1).trans (one_smul _ _)

/-- **Restriction of cochains to integral chains**, as a map of cochain complexes of abelian
groups from the rational cochains `Hom_ℚ(C(X; ℚ), ℚ)` to the integral cochains
`Hom_ℤ(C(X; ℤ), ℚ)`. It is an isomorphism (`TopCat.bijective_singularCochainRatToInt`). -/
def singularCochainComplexRatToInt :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))) ⟶
      X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℚ) where
  f p := X.singularCochainRatToInt p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext φ
    -- restate the square for `φ` as a morphism of rational chains, which the differentials of
    -- the two cochain complexes precompose
    have key (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X i ⟶
        𝟙_ (ModuleCat.{0} ℚ)) :
        ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).d (i + 1) i ≫
          X.singularChainComplexIntToRat.f i ≫
            (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map φ ≫
              (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom =
        X.singularChainComplexIntToRat.f (i + 1) ≫
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
            (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).d (i + 1) i ≫ φ) ≫
              (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom := by
      rw [Functor.map_comp, ← HomologicalComplex.Hom.comm_assoc,
        Functor.mapHomologicalComplex_obj_d, Category.assoc]
    exact key φ

/-- In each degree, the cochain map restricts cochains to integral chains. -/
@[simp]
theorem singularCochainComplexRatToInt_f (p : ℕ) :
    X.singularCochainComplexRatToInt.f p = X.singularCochainRatToInt p :=
  (rfl)

instance : IsIso X.singularCochainComplexRatToInt :=
  have (p : ℕ) : IsIso (X.singularCochainComplexRatToInt.f p) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (X.bijective_singularCochainRatToInt p)
  HomologicalComplex.Hom.isIso_of_components _

/-- **Capping with the restriction of a cochain.** Capping an integral chain with the restriction
of a cochain `φ` to integral chains, along the right unitors as in the duality map, is the
rational cap product with `φ` of the chain made rational. -/
theorem capChain_singularCochainRatToInt {p q n : ℕ} (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
          (X.singularCochainRatToInt p φ) =
      X.singularChainComplexIntToRat.f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (ChainComplex.capChain ℚ (X.alexanderWhitneyDiagonal (λ_ _).inv)
            ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) p q n h φ) ≫
        X.singularChainComplexRestrictScalarsRatIso.hom.f q := by
  rw [singularCochainRatToInt_apply]
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  have hc := congrArg (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
    (X.ιChainComplex_capChain_leftUnitor_unit (k := ℚ) h φ σ)
  rw [Functor.map_comp, Functor.map_comp] at hc
  rw [ιChainComplex_capChain_rightUnitor, ιChainComplex_singularChainComplexIntToRat_f_assoc,
    ιChainComplex_singularChainComplexIntToRat_f_assoc, reassoc_of% hc,
    map_ιChainComplex_singularChainComplexRestrictScalarsRatIso_hom_f]
  simp only [Functor.map_comp, Category.assoc]

/-! ### Cohomology and homology -/

/-- **Rational cohomology from integral chains**: singular cohomology computed from rational
chains, read as an abelian group, is singular cohomology computed from integral chains with
values in `ℚ`. -/
def singularCohomologyRatIso (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).obj
        (X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) p) ≅
      X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℚ) p :=
  (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapHomologyIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).symm ≪≫
    HomologicalComplex.homologyMapIso (asIso X.singularCochainComplexRatToInt) p

/-- The comparison of cohomologies is the comparison of the homology of the restricted complex
with the restricted homology, followed by the map induced by restricting cochains. -/
theorem singularCohomologyRatIso_hom (p : ℕ) :
    (X.singularCohomologyRatIso p).hom =
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
        (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.homologyMap X.singularCochainComplexRatToInt p :=
  (rfl)

/-- **Rational homology as homology with coefficients in the abelian group `ℚ`**: singular
homology with rational chains, read as an abelian group, is singular homology with coefficients in
the abelian group `ℚ`. -/
def singularHomologyRatIso (q : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).obj
        (((singularHomologyFunctor (ModuleCat.{0} ℚ) q).obj (𝟙_ (ModuleCat.{0} ℚ))).obj X) ≅
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj (ModuleCat.of ℤ ℚ)).obj X :=
  ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapHomologyIso
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).symm ≪≫
    HomologicalComplex.homologyMapIso X.singularChainComplexRestrictScalarsRatIso q

/-- The comparison of homologies is the comparison of the homology of the restricted complex with
the restricted homology, followed by the map induced by
`TopCat.singularChainComplexRestrictScalarsRatIso`. -/
theorem singularHomologyRatIso_hom (q : ℕ) :
    (X.singularHomologyRatIso q).hom =
      ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapHomologyIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.homologyMap X.singularChainComplexRestrictScalarsRatIso.hom q :=
  (rfl)

/-- **Integral to rational homology**: the map `Hₙ(X; ℤ) ⟶ Hₙ(X; ℚ)` induced by the inclusion
`ℤ → ℚ` of coefficients, with `Hₙ(X; ℚ)` read as an abelian group. -/
def singularHomologyIntToRat (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X ⟶
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).obj
        (((singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj (𝟙_ (ModuleCat.{0} ℚ))).obj X) :=
  HomologicalComplex.homologyMap X.singularChainComplexIntToRat n ≫
    ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapHomologyIso
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom

/-- The comparison of cohomologies on the class of a rational cocycle `φ` is the class of the
restriction of `φ` to integral chains. -/
@[reassoc]
theorem map_homologyπ_singularCohomologyRatIso_hom (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p) ≫
      (X.singularCohomologyRatIso p).hom =
    (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.cyclesMap X.singularCochainComplexRatToInt p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ ℚ)).homologyπ p := by
  have h : (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
          (𝟙_ (ModuleCat.{0} ℚ))).sc p).homologyπ ≫
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
        (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv =
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
        (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc p).map
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).homologyπ := by
    rw [Iso.comp_inv_eq, Category.assoc, ShortComplex.homologyπ_comp_mapHomologyIso_hom,
      Iso.inv_hom_id_assoc]
  rw [singularCohomologyRatIso_hom]
  -- The class map of the image short complex is that of the restricted cochain complex only
  -- after unfolding, so the two squares are pasted as terms.
  exact ((reassoc_of% h) _).trans
    (congrArg (_ ≫ ·) (HomologicalComplex.homologyπ_naturality X.singularCochainComplexRatToInt p))

/-- The map from integral to rational homology on the class of an integral cycle `z` is the class
of `z` made rational. -/
@[reassoc]
theorem homologyπ_singularHomologyIntToRat (n : ℕ) :
    ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n ≫
        X.singularHomologyIntToRat n =
      HomologicalComplex.cyclesMap X.singularChainComplexIntToRat n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ n) := by
  rw [singularHomologyIntToRat]
  refine ((reassoc_of% (HomologicalComplex.homologyπ_naturality
    X.singularChainComplexIntToRat n)) _).trans ?_
  exact congrArg (_ ≫ ·) (ShortComplex.homologyπ_comp_mapHomologyIso_hom
    (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n)
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)))

/-- The comparison of homologies on the class of a rational cycle is the class of the same chain
with coefficients in the abelian group `ℚ`. -/
@[reassoc]
theorem map_homologyπ_singularHomologyRatIso_hom (q : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ q) ≫
      (X.singularHomologyRatIso q).hom =
    ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.cyclesMap X.singularChainComplexRestrictScalarsRatIso.hom q ≫
        ((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).homologyπ q := by
  have h : (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).homologyπ ≫
      ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapHomologyIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv =
      ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).map
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).homologyπ := by
    rw [Iso.comp_inv_eq, Category.assoc, ShortComplex.homologyπ_comp_mapHomologyIso_hom,
      Iso.inv_hom_id_assoc]
  rw [singularHomologyRatIso_hom]
  -- as in `map_homologyπ_singularCohomologyRatIso_hom`
  exact ((reassoc_of% h) _).trans (congrArg (_ ≫ ·)
    (HomologicalComplex.homologyπ_naturality X.singularChainComplexRestrictScalarsRatIso.hom q))

/-! ### The cap product -/

/-- On cocycles, restricting a rational cocycle to integral chains is restricting the underlying
cochain. -/
@[reassoc]
theorem mapCyclesIso_inv_cyclesMap_singularCochainComplexRatToInt_iCycles (p : ℕ) :
    (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc
        p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.cyclesMap X.singularCochainComplexRatToInt p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ ℚ)).iCycles p =
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
            (𝟙_ (ModuleCat.{0} ℚ))).iCycles p) ≫
        X.singularCochainRatToInt p := by
  rw [HomologicalComplex.cyclesMap_i, singularCochainComplexRatToInt_f]
  -- The cycles of the restricted complex are those of the image short complex only after
  -- unfolding, so the square is pasted as a term.
  exact (reassoc_of% (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
    (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapCyclesIso_inv_comp_iCycles
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)))) _

/-- **Capping with the restriction of a cocycle**, on cycles: capping integral cycles with the
restriction of a rational cocycle `φ` is making them rational, capping with `φ`, and reading the
result with coefficients in the abelian group `ℚ`. -/
theorem capCycles_cyclesMap_singularCochainComplexRatToInt {p q n : ℕ} (h : p + q = n)
    (φ : (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).cycles p) :
    ChainComplex.capCycles ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
        (HomologicalComplex.cyclesMap X.singularCochainComplexRatToInt p
          ((((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc
            p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv φ)) =
      HomologicalComplex.cyclesMap X.singularChainComplexIntToRat n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (ChainComplex.capCycles ℚ (X.alexanderWhitneyDiagonal (λ_ _).inv)
            ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) p q n h φ) ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
        HomologicalComplex.cyclesMap X.singularChainComplexRestrictScalarsRatIso.hom q := by
  rw [← cancel_mono (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).iCycles q),
    ChainComplex.capCycles_i]
  have hφ : (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ ℚ)).iCycles p
      (HomologicalComplex.cyclesMap X.singularCochainComplexRatToInt p
        ((((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc
          p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv φ)) =
      X.singularCochainRatToInt p
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
          (𝟙_ (ModuleCat.{0} ℚ))).iCycles p φ) :=
    ConcreteCategory.congr_hom
      (X.mapCyclesIso_inv_cyclesMap_singularCochainComplexRatToInt_iCycles p) φ
  have e₁ := (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc
    q).mapCyclesIso_inv_comp_iCycles (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))
  have e₂ := (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc
    n).mapCyclesIso_hom_iCycles (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))
  rw [hφ]
  -- In the remaining steps, the cochains and cycles of a restricted complex appear both as
  -- those of the complex and as those of the image short complex, which agree only after
  -- unfolding `ModuleCat.restrictScalars`; `erw` sees through this.
  erw [capChain_singularCochainRatToInt]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  erw [reassoc_of% e₁]
  rw [← Functor.map_comp_assoc]
  erw [ChainComplex.capCycles_i]
  rw [Functor.map_comp, Category.assoc]
  erw [reassoc_of% e₂]
  exact ((reassoc_of% (HomologicalComplex.cyclesMap_i X.singularChainComplexIntToRat n)) _).symm

/-- **The integral and the rational cap product agree.** For `α ∈ Hᵖ(X; ℚ)` and `μ ∈ Hₙ(X; ℤ)`,
`p + q = n`, capping `μ` with the class of `α` in the cohomology of integral chains with values in
`ℚ`, along the right unitors as in the duality map, is the rational cap product `ρ(μ) ⌢ α` of
`α` with the image `ρ(μ)` of `μ` in `Hₙ(X; ℚ)`, read in homology with coefficients in the abelian
group `ℚ`. -/
theorem singularCap_singularCohomologyRatIso_hom {p q n : ℕ} (h : p + q = n)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ)) p)
    (μ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X) :
    (X.singularCap ℤ (ρ_ _).inv (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h
        ((X.singularCohomologyRatIso p).hom α)).hom μ =
      (X.singularHomologyRatIso q).hom
        (X.singularCapLinearMap ℚ h (X.singularHomologyIntToRat n μ) α) := by
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p)).1
      inferInstance α
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n)).1 inferInstance μ
  -- the classes of `φ` and `z` on the two sides, computed from the formulas for the comparisons
  have hc : (X.singularCohomologyRatIso p).hom
      ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p φ) =
      (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℚ)).homologyπ p
        (HomologicalComplex.cyclesMap X.singularCochainComplexRatToInt p
          ((((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc
            p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv φ)) :=
    ConcreteCategory.congr_hom (X.map_homologyπ_singularCohomologyRatIso_hom p) φ
  have hρ : X.singularHomologyIntToRat n
      (((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n z) =
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ n
        (((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom
            (HomologicalComplex.cyclesMap X.singularChainComplexIntToRat n z)) :=
    ConcreteCategory.congr_hom (X.homologyπ_singularHomologyIntToRat n) z
  have hcap (w : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).cycles n) :
      X.singularCapLinearMap ℚ h
          (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ n w)
          ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
            (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p φ) =
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ q
          (ChainComplex.capCycles ℚ (X.alexanderWhitneyDiagonal (λ_ _).inv)
            ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) p q n h φ w) :=
    (X.singularCapLinearMap_apply ℚ h _ _).trans <| ConcreteCategory.congr_hom
      (X.singularCap_homologyπ ℚ (λ_ _).inv
      (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom p q n h φ) w
  have hr (w : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).cycles q) :
      (X.singularHomologyRatIso q).hom
        (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ q w) =
      ((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).homologyπ q
        (HomologicalComplex.cyclesMap X.singularChainComplexRestrictScalarsRatIso.hom q
          (((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q).mapCyclesIso
            (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv w)) :=
    ConcreteCategory.congr_hom (X.map_homologyπ_singularHomologyRatIso_hom q) w
  rw [hc]
  -- Elements of a restricted module and of the module itself have the same type only after
  -- unfolding, which `rw` does not do, so the two sides are compared through `Eq.trans`.
  refine (ConcreteCategory.congr_hom (X.singularCap_homologyπ ℤ (ρ_ _).inv
    (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h _) z).trans (Eq.trans ?_
      ((congrArg (fun x ↦ (X.singularHomologyRatIso q).hom (X.singularCapLinearMap ℚ h x
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
          (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p φ))) hρ).trans
        ((congrArg (X.singularHomologyRatIso q).hom (hcap _)).trans (hr _))).symm)
  exact congrArg (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).homologyπ q)
    (ConcreteCategory.congr_hom (X.capCycles_cyclesMap_singularCochainComplexRatToInt h φ) z)

end TopCat

namespace TauCeti.HomologicalOrientation

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n)

/-- **Rational duality from the duality map.** For a compact oriented `n`-manifold `M` and
`p + q = n`, if the duality map `Hᵖ_c(M; ℚ) ⟶ H_q(M; ℚ)`, computed from integral chains, is
injective, then capping with the image of the fundamental class in `Hₙ(M; ℚ)` is injective on
`Hᵖ(M; ℚ)`, computed from rational chains. -/
theorem injective_singularCapLinearMap_of_injective_dualityMap [CompactSpace M] {p q : ℕ}
    (h : p + q = n) (hinj : Function.Injective (o.dualityMap hn (ModuleCat.of ℤ ℚ) p q h)) :
    Function.Injective ((TopCat.of M).singularCapLinearMap ℚ h
      ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn))) := by
  intro α β hαβ
  have hd (α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ)) p) :
      o.dualityMap hn (ModuleCat.of ℤ ℚ) p q h
          ((TopCat.compactSupportCohomologyIsoOfCompactSpace p).inv
            (((TopCat.of M).singularCohomologyRatIso p).hom α)) =
        ((TopCat.of M).singularHomologyRatIso q).hom ((TopCat.of M).singularCapLinearMap ℚ h
          ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn)) α) := by
    rw [dualityMap_compactSupportCohomologyIsoOfCompactSpace_inv]
    exact TopCat.singularCap_singularCohomologyRatIso_hom _ h α _
  exact (ConcreteCategory.bijective_of_isIso ((TopCat.of M).singularCohomologyRatIso p).hom).1
    ((ConcreteCategory.bijective_of_isIso
      (TopCat.compactSupportCohomologyIsoOfCompactSpace p).inv).1
        (hinj ((hd α).trans ((congrArg _ hαβ).trans (hd β).symm))))

end TauCeti.HomologicalOrientation

end
