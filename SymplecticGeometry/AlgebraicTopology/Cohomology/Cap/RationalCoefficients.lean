/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import SymplecticGeometry.Algebra.Homology.ShortComplex.PreservesHomology
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.IntegralComparison
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Signature

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
  are the chains with coefficients in the abelian group `ℚ`: the inverse of the change of
  coefficients `SSet.restrictScalarsChainIso` along `ModuleCat.restrictScalarsAlgebraMapIso`.
* `TopCat.singularChainComplexIntToRat`: the chain map `C(X; ℤ) ⟶ F (C(X; ℚ))` induced by the
  inclusion `ℤ → ℚ` of coefficients (`SymplecticGeometry.intToRatCoeff`), an instance of the
  change of coefficients `SSet.restrictScalarsChainMap`, and the induced map on homology
  `TopCat.singularHomologyIntToRat : Hₙ(X; ℤ) ⟶ F (Hₙ(X; ℚ))`. For an oriented compact
  manifold, it sends the integral fundamental class to a rational one. For a connected
  manifold Tau Ceti also has `TauCeti.HomologicalOrientation.rationalFundamentalClass`, built
  by extension of scalars; this file does not compare the two.
* `TopCat.singularCochainComplexRatIso`: the `ℚ`-linear cochains on rational chains, read as
  abelian groups, are the integral cochains with values in `ℚ`. It is the composite of Tau Ceti's
  `TauCeti.singularCochainComplexIntegralIso`, which compares cochains over a ring with integral
  cochains by their values on simplices, with the change of chain coefficients along
  `TauCeti.uliftIntIso`. It restricts a cochain `φ` to integral chains, `φ ↦ φ ∘ ι`
  (`TopCat.singularCochainComplexRatIso_hom_f_apply`). Hence an isomorphism
  `TopCat.singularCohomologyRatIso : F (Hᵖ(X; ℚ)) ≅ Hᵖ(X; ℤ, ℚ)` of cohomology computed from
  rational chains with cohomology computed from integral chains with values in `ℚ`.
* `TopCat.singularHomologyRatIso : F (H_q(X; ℚ)) ≅ H_q(X; ℤ, ℚ)`: homology with rational chains,
  read as an abelian group, is homology with coefficients in the abelian group `ℚ`.

The main result is that the two cap products agree under these identifications
(`TopCat.singularCap_singularCohomologyRatIso_hom`): for `α ∈ Hᵖ(X; ℚ)` and `μ ∈ Hₙ(X; ℤ)`,
capping `μ` with the integral class of `α` is the rational cap product of `α` with the image of
`μ`. It is checked on simplices, where both sides evaluate the cochain on the front `p`-face and
keep the back `q`-face (`TopCat.capChain_singularCochainComplexRatIso_hom_f`, using the formulas
of `SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Basic`).

As a consequence, for a compact oriented manifold, Tau Ceti's Poincaré duality for closed
manifolds with values in `ℚ`
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`) makes the rational cap
product with the rational fundamental class bijective
(`TauCeti.HomologicalOrientation.bijective_singularCapLinearMap_fundamentalClass`). Its
injectivity is the hypothesis of Tau Ceti's evenness criterion
`TopCat.even_finrank_singularHomology_of_injective_singularCapLinearMap`. With Tau
Ceti's `TopCat.finrank_singularHomology_eq_of_bijective_singularCapLinearMap`, it follows that the
rational Betti numbers of a compact oriented `n`-manifold satisfy `b_q = b_p` for `p + q = n`
(`TauCeti.HomologicalOrientation.bettiNumber_eq_bettiNumber`).

For `p + p = n`, the intersection form `TauCeti.HomologicalOrientation.intersectionForm` is the
cup pairing `(α, β) ↦ ⟨α ⌣ β, μ⟩` on `Hᵖ(M; ℚ)`, `μ` being the image of the fundamental class;
`TauCeti.HomologicalOrientation.intersectionQuadraticForm` is its quadratic form, and
`TauCeti.HomologicalOrientation.signature` is the signature `QuadraticForm.signature`, the
difference `sigPos - sigNeg` of the indices of inertia, of that quadratic form. Injectivity of the
cap product makes the intersection form nondegenerate, by Tau Ceti's
`TopCat.nondegenerate_singularCupPairing_iff`
(`TauCeti.HomologicalOrientation.nondegenerate_intersectionForm`). For `p` even the form is
symmetric, so its quadratic form is nondegenerate too
(`TauCeti.HomologicalOrientation.nondegenerate_intersectionQuadraticForm`), and the indices of
inertia add up to `b_p`
(`TauCeti.HomologicalOrientation.sigPos_add_sigNeg_intersectionQuadraticForm`).

## Implementation notes

`SymplecticGeometry.intToRatCoeff` and `SymplecticGeometry.intToRatCoeff_apply` are Tau Ceti's
`TauCeti.intToRealCoeff` and `TauCeti.intToRealCoeff_apply` with `ℚ` in place of `ℝ`.

The comparisons of chains and of homologies follow the steps of Tau Ceti's
`SSet.homologyExtendScalarsIso`, for restriction instead of extension of scalars: the change of
coefficients `SSet.restrictScalarsChainIso`, built on Mathlib's
`SSet.chainComplexFunctorObjCompMapIso`, then `CategoryTheory.ShortComplex.mapHomologyIso`.
Tau Ceti's `CategoryTheory.Functor.singularHomologyFunctorObjCompIso`, used by
`TopCat.singularHomologyModTwoIso`, gives the same comparison of homologies, but its chain-level
part `CategoryTheory.Functor.singularChainComplexFunctorObjCompMapIso` is not exposed and has no
formula on simplices, which the cap product computation needs; the change of coefficients has
one (`SSet.map_ιChainComplex_restrictScalarsChainIso_inv_f`).
As in Tau Ceti's `Duality.lean`, `CategoryTheory.MonoidalPreadditive.monoidalLinearInt` is a
local instance, so that the integral cap product is the one of the duality map.

Several objects here agree only up to unfolding `ModuleCat.restrictScalars` or Mathlib's
`singularHomologyFunctor`, for instance the cycles of `F` applied to a complex and the cycles of
the complex itself. Where `rw` cannot see such an identification, proofs paste equalities as terms
or use `erw`, and say so.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1 (change of
  coefficients) and Section 3.3 (the cap product, and Theorem 3.30, Poincaré duality).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Simplicial

namespace SymplecticGeometry

/-- The coefficient map `ℤ → ℚ`, from the integral coefficients `ULift ℤ` of the fundamental class
to the abelian group `ℚ`. -/
def intToRatCoeff : ModuleCat.of ℤ (ULift.{0} ℤ) ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom ((Int.castAddHom ℚ).toIntLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap)

/-- The coefficient map `ℤ → ℚ` is the cast of integers to rationals. -/
@[simp]
theorem intToRatCoeff_apply (m : ULift.{0} ℤ) : intToRatCoeff m = (m.down : ℚ) :=
  (rfl)

end SymplecticGeometry

namespace TopCat

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

open TauCeti SymplecticGeometry

variable (X : TopCat.{0})

/-! ### Chains -/

/-- The singular chains with rational coefficients, read as abelian groups, are the singular
chains with coefficients in the abelian group `ℚ`. -/
def singularChainComplexRestrictScalarsRatIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))) ≅
      (toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ) :=
  (SSet.restrictScalarsChainIso (algebraMap ℤ ℚ) (N := 𝟙_ (ModuleCat.{0} ℚ))
    (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).symm (toSSet.obj X)).symm

/-- The identification of rational chains with chains with coefficients in the abelian group `ℚ`
is the inverse of the change of coefficients along the identification of the abelian group `ℚ`
with the restricted `ℚ`-module `ℚ`. -/
theorem singularChainComplexRestrictScalarsRatIso_def :
    X.singularChainComplexRestrictScalarsRatIso =
      (SSet.restrictScalarsChainIso (algebraMap ℤ ℚ) (N := 𝟙_ (ModuleCat.{0} ℚ))
        (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).symm (toSSet.obj X)).symm :=
  (rfl)

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
  rw [singularChainComplexRestrictScalarsRatIso_def, Iso.symm_hom,
    SSet.map_ιChainComplex_restrictScalarsChainIso_inv_f, Iso.symm_inv]

/-- The chain map from integral to rational singular chains, read as abelian groups, induced by
the inclusion `ℤ → ℚ` of coefficients: the change of coefficients `SSet.restrictScalarsChainMap`
along `SymplecticGeometry.intToRatCoeff`, with `ℚ` read as a restricted `ℚ`-module. -/
def singularChainComplexIntToRat :
    (toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟶
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))) :=
  SSet.restrictScalarsChainMap (algebraMap ℤ ℚ) (N := 𝟙_ (ModuleCat.{0} ℚ))
    (intToRatCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).inv)
    (toSSet.obj X)

/-- The chain map from integral to rational chains is the change of coefficients
`SSet.restrictScalarsChainMap` along `SymplecticGeometry.intToRatCoeff`, followed by the
identification of the abelian group `ℚ` with the restricted `ℚ`-module `ℚ`. -/
theorem singularChainComplexIntToRat_def :
    X.singularChainComplexIntToRat =
      SSet.restrictScalarsChainMap (algebraMap ℤ ℚ) (N := 𝟙_ (ModuleCat.{0} ℚ))
        (intToRatCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).inv)
        (toSSet.obj X) :=
  (rfl)

/-- The chain map from integral to rational chains keeps each singular simplex and casts its
coefficient to `ℚ`. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_singularChainComplexIntToRat_f {n : ℕ} (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ X.singularChainComplexIntToRat.f n =
      intToRatCoeff ≫ (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).inv ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ) := by
  rw [singularChainComplexIntToRat_def, SSet.ιChainComplex_restrictScalarsChainMap_f,
    Category.assoc]

/-! ### Cochains -/

/-- The `ℚ`-linear singular cochains, read as abelian groups, are the same morphisms with the
action of `ℤ` of the `ℤ`-linear category `ModuleCat ℚ`. -/
def singularCochainComplexRestrictScalarsRatIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))) ≅
      X.singularCochainComplex (ModuleCat.of ℚ ℚ) ℤ (ModuleCat.of ℚ ℚ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ LinearEquiv.toModuleIso
      { toFun φ := φ
        invFun φ := φ
        map_add' _ _ := rfl
        map_smul' a φ := Int.cast_smul_eq_zsmul ℚ a φ
        left_inv _ := rfl
        right_inv _ := rfl })
    fun _ _ _ ↦ rfl

/-- The identification of restricted `ℚ`-linear cochains with `ℚ`-linear cochains under the
action of `ℤ` is the identity on cochains. -/
theorem singularCochainComplexRestrictScalarsRatIso_hom_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    X.singularCochainComplexRestrictScalarsRatIso.hom.f p φ = φ :=
  (rfl)

/-- The inverse identification of `ℚ`-linear cochains under the action of `ℤ` with restricted
`ℚ`-linear cochains is the identity on cochains. -/
theorem singularCochainComplexRestrictScalarsRatIso_inv_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    X.singularCochainComplexRestrictScalarsRatIso.inv.f p φ = φ :=
  (rfl)

/-- **Rational cochains as integral cochains**: the `ℚ`-linear cochains `Hom_ℚ(C(X; ℚ), ℚ)`,
read as abelian groups, are the integral cochains `Hom_ℤ(C(X; ℤ), ℚ)`. A cochain goes to its
restriction to integral chains (`TopCat.singularCochainComplexRatIso_hom_f_apply`). -/
def singularCochainComplexRatIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).mapHomologicalComplex _).obj
        (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))) ≅
      X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ ℚ) :=
  X.singularCochainComplexRestrictScalarsRatIso ≪≫
    singularCochainComplexIntegralIso ℚ (ModuleCat.of ℚ ℚ) X ≪≫
      (ChainComplex.linearYonedaFunctor ℤ (ModuleCat.of ℤ ℚ)).mapIso
        (((SSet.chainComplexFunctor _).mapIso uliftIntIso).app (toSSet.obj X)).op

/-- The comparison of cochains takes a cochain `φ` to the integral cochain sending `a σ` to
`a φ(σ)`. -/
theorem singularCochainComplexRatIso_hom_f_apply_ιChainComplex {p : ℕ}
    (σ : (toSSet.obj X) _⦋p⦌)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ))
    (a : ULift.{0} ℤ) :
    ConcreteCategory.hom (X := ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p)
        (Y := ModuleCat.of ℤ ℚ) (X.singularCochainComplexRatIso.hom.f p φ)
        ((toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ a) =
      (a.down : ℚ) * φ ((toSSet.obj X).ιChainComplex (R := 𝟙_ (ModuleCat.{0} ℚ)) σ 1) := by
  -- The comparison is the identity on morphisms, then Tau Ceti's comparison, then precomposition
  -- with the chain map induced by `ULift ℤ ≅ ℤ`, which takes `a σ` to `a.down σ`. The first step
  -- is stated by `rfl`: rewriting with the lemmas of the three pieces fails, since `φ` is typed
  -- as a cochain on chains with coefficients `𝟙_ (ModuleCat ℚ)` and not `ModuleCat.of ℚ ℚ`.
  have e : X.singularCochainComplexRatIso.hom.f p φ =
      (((SSet.chainComplexFunctor _).map uliftIntIso.hom).app (toSSet.obj X)).f p ≫
        (singularCochainComplexIntegralIso ℚ (ModuleCat.of ℚ ℚ) X).hom.f p φ :=
    rfl
  have h := SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc uliftIntIso.hom σ
    ((singularCochainComplexIntegralIso ℚ (ModuleCat.of ℚ ℚ) X).hom.f p φ)
  rw [← e] at h
  refine (ConcreteCategory.congr_hom h a).trans ?_
  rw [ModuleCat.comp_apply, uliftIntIso_hom_apply]
  exact (simplicialCochainComplexIntegralIso_hom_f_apply_ιChainComplex ℚ (ModuleCat.of ℚ ℚ)
    (toSSet.obj X) p φ σ a.down).trans (zsmul_eq_mul _ _)

/-- The comparison of cochains restricts a `ℚ`-linear cochain `φ` on rational chains to integral
chains: it is `φ` precomposed with the chain map from integral to rational chains. -/
theorem singularCochainComplexRatIso_hom_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    X.singularCochainComplexRatIso.hom.f p φ = X.singularChainComplexIntToRat.f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map φ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := ℚ) ℚ).hom := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  ext a
  refine (X.singularCochainComplexRatIso_hom_f_apply_ιChainComplex σ φ a).trans ?_
  symm
  rw [ιChainComplex_singularChainComplexIntToRat_f_assoc, ← smul_eq_mul, ← map_smul, ← map_smul,
    smul_eq_mul, mul_one]
  -- The identifications of a restricted module with the abelian group `ℚ`, and restrictions of
  -- scalars of morphisms, are the identity on elements, but their evaluation lemmas are stated
  -- for the underlying types, which `rw` does not identify with the carriers here.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ModuleCat.restrictScalarsAlgebraMapIso_hom_apply,
    ModuleCat.restrictScalars.map_apply, ModuleCat.restrictScalars.map_apply,
    ModuleCat.restrictScalarsAlgebraMapIso_inv_apply, intToRatCoeff_apply,
    ModuleCat.restrictScalars.map_apply]

/-- **Capping with the restriction of a cochain.** Capping an integral chain with the restriction
of a cochain `φ` to integral chains, along the right unitors as in the duality map, is the
rational cap product with `φ` of the chain made rational. -/
theorem capChain_singularCochainComplexRatIso_hom_f {p q n : ℕ} (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).X p ⟶ 𝟙_ (ModuleCat.{0} ℚ)) :
    ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
          (X.singularCochainComplexRatIso.hom.f p φ) =
      X.singularChainComplexIntToRat.f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (ChainComplex.capChain ℚ (X.alexanderWhitneyDiagonal (λ_ _).inv)
            ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) p q n h φ) ≫
        X.singularChainComplexRestrictScalarsRatIso.hom.f q := by
  rw [singularCochainComplexRatIso_hom_f_apply]
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
    HomologicalComplex.homologyMapIso (X.singularCochainComplexRatIso) p

/-- The comparison of cohomologies is the comparison of the homology of the restricted complex
with the restricted homology, followed by the map induced by restricting cochains. -/
theorem singularCohomologyRatIso_hom (p : ℕ) :
    (X.singularCohomologyRatIso p).hom =
      (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
        (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.homologyMap X.singularCochainComplexRatIso.hom p :=
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

/-- The map from integral to rational homology is the map induced on homology by the chain map
from integral to rational chains, followed by the comparison of the homology of the restricted
complex with the restricted homology. -/
theorem singularHomologyIntToRat_def (n : ℕ) :
    X.singularHomologyIntToRat n =
      HomologicalComplex.homologyMap X.singularChainComplexIntToRat n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom :=
  (rfl)

/-- The comparison of cohomologies on the class of a rational cocycle `φ` is the class of the
restriction of `φ` to integral chains. -/
@[reassoc, elementwise]
theorem map_homologyπ_singularCohomologyRatIso_hom (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p) ≫
      (X.singularCohomologyRatIso p).hom =
    (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
      (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.cyclesMap X.singularCochainComplexRatIso.hom p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ ℚ)).homologyπ p := by
  rw [singularCohomologyRatIso_hom]
  -- The class map of the image short complex is that of the restricted cochain complex only
  -- after unfolding, so the two squares are pasted as terms.
  exact ((ShortComplex.map_homologyπ_comp_mapHomologyIso_inv_assoc
    ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc p)
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))) _).trans
    (congrArg (_ ≫ ·)
      (HomologicalComplex.homologyπ_naturality X.singularCochainComplexRatIso.hom p))

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
  rw [singularHomologyIntToRat_def]
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
  rw [singularHomologyRatIso_hom]
  -- as in `map_homologyπ_singularCohomologyRatIso_hom`
  exact ((ShortComplex.map_homologyπ_comp_mapHomologyIso_inv_assoc
    (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q)
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))) _).trans (congrArg (_ ≫ ·)
    (HomologicalComplex.homologyπ_naturality X.singularChainComplexRestrictScalarsRatIso.hom q))

/-! ### The cap product -/

/-- On cocycles, restricting a rational cocycle to integral chains is restricting the underlying
cochain. -/
@[reassoc, elementwise nosimp]
theorem mapCyclesIso_inv_cyclesMap_singularCochainComplexRatIso_hom_iCycles (p : ℕ) :
    (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).sc
        p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv ≫
      HomologicalComplex.cyclesMap X.singularCochainComplexRatIso.hom p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ ℚ)).iCycles p =
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
            (𝟙_ (ModuleCat.{0} ℚ))).iCycles p) ≫
        X.singularCochainComplexRatIso.hom.f p := by
  rw [HomologicalComplex.cyclesMap_i]
  -- The cycles of the restricted complex are those of the image short complex only after
  -- unfolding, so the square is pasted as a term.
  exact (reassoc_of% (((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
    (𝟙_ (ModuleCat.{0} ℚ))).sc p).mapCyclesIso_inv_comp_iCycles
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)))) _

/-- **Capping with the restriction of a cocycle**, on cycles: capping integral cycles with the
restriction of a rational cocycle `φ` is making them rational, capping with `φ`, and reading the
result with coefficients in the abelian group `ℚ`. -/
@[elementwise nosimp]
theorem capCycles_cyclesMap_singularCochainComplexRatIso_hom {p q n : ℕ} (h : p + q = n)
    (φ : (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ (ModuleCat.{0} ℚ))).cycles p) :
    ChainComplex.capCycles ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
        (HomologicalComplex.cyclesMap X.singularCochainComplexRatIso.hom p
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
  have e₁ := (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc
    q).mapCyclesIso_inv_comp_iCycles (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))
  have e₂ := (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc
    n).mapCyclesIso_hom_iCycles (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))
  rw [X.mapCyclesIso_inv_cyclesMap_singularCochainComplexRatIso_hom_iCycles_apply p φ]
  -- In the remaining steps, the cochains and cycles of a restricted complex appear both as
  -- those of the complex and as those of the image short complex, which agree only after
  -- unfolding `ModuleCat.restrictScalars`; `erw` sees through this.
  erw [capChain_singularCochainComplexRatIso_hom_f]
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
  obtain ⟨φ, rfl⟩ := (X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
    (𝟙_ (ModuleCat.{0} ℚ))).moduleCat_homologyπ_surjective p α
  obtain ⟨z, rfl⟩ := ((toSSet.obj X).chainComplex
    (ModuleCat.of ℤ (ULift.{0} ℤ))).moduleCat_homologyπ_surjective n μ
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
  rw [X.map_homologyπ_singularCohomologyRatIso_hom_apply p φ]
  -- Elements of a restricted module and of the module itself have the same type only after
  -- unfolding, which `rw` does not do, so the two sides are compared through `Eq.trans`.
  refine (ConcreteCategory.congr_hom (X.singularCap_homologyπ ℤ (ρ_ _).inv
    (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h _) z).trans (Eq.trans ?_
      ((congrArg (fun x ↦ (X.singularHomologyRatIso q).hom (X.singularCapLinearMap ℚ h x
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
          (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p φ))) hρ).trans
        ((congrArg (X.singularHomologyRatIso q).hom (hcap _)).trans (hr _))).symm)
  exact congrArg (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).homologyπ q)
    (X.capCycles_cyclesMap_singularCochainComplexRatIso_hom_apply h φ z)

end TopCat

namespace TauCeti.HomologicalOrientation

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : Module.finrank ℝ E = n)

/-- **Rational Poincaré duality for a compact manifold.** For a compact homologically oriented
`n`-manifold `M` without boundary and `p + q = n`, capping with the image of the fundamental
class in `Hₙ(M; ℚ)` is a bijection `Hᵖ(M; ℚ) → H_q(M; ℚ)`, computed from rational chains. -/
theorem bijective_singularCapLinearMap_fundamentalClass [CompactSpace M] {p q : ℕ}
    (h : p + q = n) :
    Function.Bijective ((TopCat.of M).singularCapLinearMap ℚ h
      ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn))) := by
  refine (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso ((TopCat.of M).singularHomologyRatIso q).hom) _).1 ?_
  -- Through `singularHomologyRatIso` and `singularCohomologyRatIso`, the rational cap product is
  -- the integral one with values in `ℚ`, which Tau Ceti shows to be bijective.
  have e : ⇑(ConcreteCategory.hom ((TopCat.of M).singularHomologyRatIso q).hom) ∘
      ⇑((TopCat.of M).singularCapLinearMap ℚ h
        ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn))) =
      (fun β ↦ ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h
        β).hom (o.fundamentalClass hn)) ∘
        ⇑(ConcreteCategory.hom ((TopCat.of M).singularCohomologyRatIso p).hom) :=
    funext fun α ↦
      (TopCat.singularCap_singularCohomologyRatIso_hom _ h α (o.fundamentalClass hn)).symm
  rw [e]
  exact (o.bijective_singularCap_fundamentalClass hn (ModuleCat.of ℤ ℚ) p q h).comp
    (ConcreteCategory.bijective_of_isIso _)

include o hn in
/-- **Poincaré duality for rational Betti numbers.** For a compact homologically oriented
`n`-manifold `M` and `p + q = n`, the `q`-th and the `p`-th Betti numbers of `M` with rational
coefficients agree. -/
theorem bettiNumber_eq_bettiNumber [CompactSpace M] {p q : ℕ} (h : p + q = n) :
    bettiNumber ℚ M q = bettiNumber ℚ M p := by
  rw [bettiNumber_def, bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of ℚ ℚ`, which is `𝟙_ (ModuleCat ℚ)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularHomology_eq_of_bijective_singularCapLinearMap ℚ h _
    (o.bijective_singularCapLinearMap_fundamentalClass hn h)

section IntersectionForm

variable [CompactSpace M] {p : ℕ} (h : p + p = n)

/-- The rational **intersection form** of a compact homologically oriented `n`-manifold `M` in
degree `p`, for `p + p = n`: the cup pairing `(α, β) ↦ ⟨α ⌣ β, μ⟩` on `Hᵖ(M; ℚ)`, for `μ` the
image of the fundamental class in `Hₙ(M; ℚ)`.

Tau Ceti's `TauCeti.HomologicalOrientation.cupPairing` is the integral counterpart, on
`Hᵖ(M; ℤ)`. -/
def intersectionForm :
    LinearMap.BilinForm ℚ ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :=
  (TopCat.of M).singularCupPairing ℚ h
    ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn))

theorem intersectionForm_def :
    o.intersectionForm hn h = (TopCat.of M).singularCupPairing ℚ h
      ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn)) :=
  (rfl)

/-- The intersection form of `α` and `β` is the cup pairing of `α` and `β` on the image of the
fundamental class, which `TopCat.singularCupPairing_apply` evaluates to `⟨α ⌣ β, μ⟩`. -/
@[simp]
theorem intersectionForm_apply
    (α β : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :
    o.intersectionForm hn h α β = (TopCat.of M).singularCupPairing ℚ h
      ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn)) α β :=
  (rfl)

/-- For `p` even, the intersection form is symmetric. -/
theorem isSymm_intersectionForm (hp : Even p) : LinearMap.IsSymm (o.intersectionForm hn h) := by
  rw [intersectionForm_def]
  exact (TopCat.of M).isSymm_singularCupPairing ℚ hp h _

/-- The quadratic form `α ↦ ⟨α ⌣ α, μ⟩` on `Hᵖ(M; ℚ)` of the intersection form
`TauCeti.HomologicalOrientation.intersectionForm`. -/
def intersectionQuadraticForm :
    QuadraticForm ℚ ((TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :=
  LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn h)

theorem intersectionQuadraticForm_def :
    o.intersectionQuadraticForm hn h =
      LinearMap.BilinMap.toQuadraticMap (o.intersectionForm hn h) :=
  (rfl)

@[simp]
theorem intersectionQuadraticForm_apply
    (α : (TopCat.of M).singularCohomology (𝟙_ (ModuleCat.{0} ℚ)) ℚ (𝟙_ _) p) :
    o.intersectionQuadraticForm hn h α = o.intersectionForm hn h α α :=
  (rfl)

/-- The **signature** of a compact homologically oriented `n`-manifold `M` in degree `p`, for
`p + p = n`: the signature `sigPos - sigNeg` of the quadratic form of the intersection form on
`Hᵖ(M; ℚ)`. The signature of a `4k`-manifold is the case `p = 2k`. -/
def signature : ℤ :=
  (o.intersectionQuadraticForm hn h).signature

theorem signature_def : o.signature hn h = (o.intersectionQuadraticForm hn h).signature :=
  (rfl)

/-- **Poincaré duality for the cup pairing.** For a compact homologically oriented `n`-manifold
`M` and `p` with `p + p = n`, the intersection form on `Hᵖ(M; ℚ)` is nondegenerate. -/
theorem nondegenerate_intersectionForm : (o.intersectionForm hn h).Nondegenerate := by
  rw [intersectionForm_def]
  exact ((TopCat.of M).nondegenerate_singularCupPairing_iff ℚ h _).2
    (o.bijective_singularCapLinearMap_fundamentalClass hn h).injective

/-- **The intersection form of a compact manifold is nondegenerate.** For a compact homologically
oriented `n`-manifold `M` and an even `p` with `p + p = n`, the quadratic form
`α ↦ ⟨α ⌣ α, μ⟩` of the intersection form on `Hᵖ(M; ℚ)` is nondegenerate. -/
theorem nondegenerate_intersectionQuadraticForm (hp : Even p) :
    (o.intersectionQuadraticForm hn h).Nondegenerate := by
  rw [intersectionQuadraticForm_def]
  exact LinearMap.BilinForm.Nondegenerate.toQuadraticMap (o.nondegenerate_intersectionForm hn h)
    (LinearMap.isSymm_iff_eq_flip.1 (o.isSymm_intersectionForm hn h hp)).symm

/-- **The indices of inertia of the intersection form add up to the middle Betti number.** For a
compact homologically oriented `n`-manifold `M` and an even `p` with `p + p = n`, the positive
and negative indices of inertia of the quadratic form of the intersection form on `Hᵖ(M; ℚ)` add
up to the `p`-th rational Betti number. -/
theorem sigPos_add_sigNeg_intersectionQuadraticForm (hp : Even p) :
    sigPos (o.intersectionQuadraticForm hn h) + sigNeg (o.intersectionQuadraticForm hn h) =
      bettiNumber ℚ M p := by
  rw [QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    (o.nondegenerate_intersectionQuadraticForm hn h hp), bettiNumber_def]
  -- `bettiNumber` takes coefficients `ModuleCat.of ℚ ℚ`, which is `𝟙_ (ModuleCat ℚ)` by the
  -- definition of the monoidal structure; Mathlib states no lemma for it.
  exact (TopCat.of M).finrank_singularCohomology p

end IntersectionForm

end TauCeti.HomologicalOrientation

end
