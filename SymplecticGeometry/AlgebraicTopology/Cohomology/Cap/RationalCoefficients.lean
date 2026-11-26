/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import SymplecticGeometry.Algebra.Homology.ShortComplex.PreservesHomology
public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Basic
public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.Duality.Manifold
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import SymplecticGeometry.LinearAlgebra.QuadraticForm.Signature
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.CapDuality
public import TauCeti.AlgebraicTopology.Singular.BettiNumber

import TauCeti.LinearAlgebra.QuadraticForm.Radical
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The cap product with integral and with rational chains

Tau Ceti has two settings for the cap product of a space `X`. The integral cap product
`TopCat.singularCap ℤ (ρ_ _).inv (ρ_ L).hom` caps integral chains, with coefficients
`ModuleCat.of ℤ (ULift ℤ)`, against cochains with values in an abelian group `L`, while
`TopCat.singularCapLinearMap ℚ` caps rational chains, with coefficients `𝟙_ (ModuleCat ℚ)`,
against `ℚ`-linear cochains. This file compares the two for `L = ℚ`. Tau Ceti's duality map
`TauCeti.HomologicalOrientation.dualityMap` is the compactly supported form of the integral
one. Throughout, `F` is the
restriction of scalars along `ℤ → ℚ`, through which an object of `ModuleCat ℚ` is read as an
abelian group.

* `TopCat.singularChainComplexRestrictScalarsRatIso`: the rational chains, read as abelian groups,
  are the chains with coefficients in the abelian group `ℚ`: the inverse of the change of
  coefficients `SSet.restrictScalarsChainIso` along `ModuleCat.restrictScalarsAlgebraMapIso`.
* `TopCat.singularHomologyIntToRat : Hₙ(X; ℤ) ⟶ F (Hₙ(X; ℚ))`: the map on homology induced by
  `SymplecticGeometry.intCastChainMap`, from
  `SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains`, the chain map
  `C(X; ℤ) ⟶ F (C(X; ℚ))` that casts integral coefficients to `ℚ`. For an oriented compact
  manifold, it sends the integral fundamental class to a rational one. For a connected
  manifold Tau Ceti also has `TauCeti.HomologicalOrientation.rationalFundamentalClass`, built
  by extension of scalars; this file does not compare the two.
* `TopCat.singularCochainComplexIntChainsIso ℚ`, from
  `SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains`: the `ℚ`-linear cochains on
  rational chains, read as abelian groups, are the integral cochains with values in `ℚ`. Here
  it restricts a cochain `φ` to integral chains, `φ ↦ φ ∘ ι`
  (`TopCat.singularCochainComplexIntChainsIso_hom_f_apply`). The induced isomorphism
  `TopCat.singularCohomologyIntChainsIso ℚ : F (Hᵖ(X; ℚ)) ≅ Hᵖ(X; ℤ, ℚ)` compares cohomology
  computed from rational chains with cohomology computed from integral chains with values in `ℚ`.
* `TopCat.singularHomologyRatIso : F (H_q(X; ℚ)) ≅ H_q(X; ℤ, ℚ)`: homology with rational chains,
  read as an abelian group, is homology with coefficients in the abelian group `ℚ`.

The main result is that the two cap products agree under these identifications
(`TopCat.singularCap_singularCohomologyIntChainsIso_hom`): for `α ∈ Hᵖ(X; ℚ)` and `μ ∈ Hₙ(X; ℤ)`,
capping `μ` with the integral class of `α` is the rational cap product of `α` with the image of
`μ`. It is checked on simplices, where both sides evaluate the cochain on the front `p`-face and
keep the back `q`-face (`TopCat.capChain_singularCochainComplexIntChainsIso_hom_f`, using the
formulas of `SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Basic`).

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
local instance, so that the integral cap product here is built with the same instance as in
Tau Ceti's `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClass`.

The rational cochains and cohomology classes of the cochain-side and cap product statements are
taken with coefficients `ModuleCat.of ℚ ℚ`, as in `TopCat.singularCochainComplexIntChainsIso`,
so that its lemmas rewrite them. Tau Ceti's rational cap product takes them with coefficients
`𝟙_ (ModuleCat ℚ)`, which is `ModuleCat.of ℚ ℚ` by definition; Lean identifies the two when it
checks the statements, so no bridging lemma is needed.

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

/-! ### Cochains -/

/-- **Capping with the restriction of a cochain.** Capping an integral chain with the restriction
of a cochain `φ` to integral chains, along the right unitors as in the duality map, is the
rational cap product with `φ` of the chain made rational. -/
theorem capChain_singularCochainComplexIntChainsIso_hom_f {p q n : ℕ} (h : p + q = n)
    (φ : ((toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X p ⟶ ModuleCat.of ℚ ℚ) :
    ChainComplex.capChain ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
          ((X.singularCochainComplexIntChainsIso ℚ).hom.f p φ) =
      (intCastChainMap ℚ (toSSet.obj X)).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (ChainComplex.capChain ℚ (X.alexanderWhitneyDiagonal (λ_ _).inv)
            ((toSSet.obj X).chainComplexPairing (λ_ (𝟙_ (ModuleCat.{0} ℚ))).hom) p q n h φ) ≫
        X.singularChainComplexRestrictScalarsRatIso.hom.f q := by
  rw [singularCochainComplexIntChainsIso_hom_f_apply]
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  have hc := congrArg (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
    (X.ιChainComplex_capChain_leftUnitor_unit (k := ℚ) h φ σ)
  rw [Functor.map_comp, Functor.map_comp] at hc
  rw [ιChainComplex_capChain_rightUnitor, ιChainComplex_intCastChainMap_f_assoc,
    ιChainComplex_intCastChainMap_f_assoc, reassoc_of% hc,
    map_ιChainComplex_singularChainComplexRestrictScalarsRatIso_hom_f]
  simp only [Functor.map_comp, Category.assoc]

/-! ### Cohomology and homology -/

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
  HomologicalComplex.homologyMap (intCastChainMap ℚ (toSSet.obj X)) n ≫
    ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapHomologyIso
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom

/-- The map from integral to rational homology is the map induced on homology by the chain map
from integral to rational chains, followed by the comparison of the homology of the restricted
complex with the restricted homology. -/
theorem singularHomologyIntToRat_def (n : ℕ) :
    X.singularHomologyIntToRat n =
      HomologicalComplex.homologyMap (intCastChainMap ℚ (toSSet.obj X)) n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom :=
  (rfl)

/-- The map from integral to rational homology on the class of an integral cycle `z` is the class
of `z` made rational. -/
@[reassoc]
theorem homologyπ_singularHomologyIntToRat (n : ℕ) :
    ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n ≫
        X.singularHomologyIntToRat n =
      HomologicalComplex.cyclesMap (intCastChainMap ℚ (toSSet.obj X)) n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ)).map
          (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ n) := by
  rw [singularHomologyIntToRat_def]
  refine ((reassoc_of% (HomologicalComplex.homologyπ_naturality
    (intCastChainMap ℚ (toSSet.obj X)) n)) _).trans ?_
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
  -- as in `TopCat.map_homologyπ_singularCohomologyIntChainsIso_hom`
  exact ((ShortComplex.map_homologyπ_comp_mapHomologyIso_inv_assoc
    (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc q)
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))) _).trans (congrArg (_ ≫ ·)
    (HomologicalComplex.homologyπ_naturality X.singularChainComplexRestrictScalarsRatIso.hom q))

/-! ### The cap product -/

/-- **Capping with the restriction of a cocycle**, on cycles: capping integral cycles with the
restriction of a rational cocycle `φ` is making them rational, capping with `φ`, and reading the
result with coefficients in the abelian group `ℚ`. -/
@[elementwise nosimp]
theorem capCycles_cyclesMap_singularCochainComplexIntChainsIso_hom {p q n : ℕ} (h : p + q = n)
    (φ : (X.singularCochainComplex (ModuleCat.of ℚ ℚ) ℚ (ModuleCat.of ℚ ℚ)).cycles p) :
    ChainComplex.capCycles ℤ (X.alexanderWhitneyDiagonal (ρ_ _).inv)
        ((toSSet.obj X).chainComplexPairing (ρ_ (ModuleCat.of ℤ ℚ)).hom) p q n h
        (HomologicalComplex.cyclesMap (X.singularCochainComplexIntChainsIso ℚ).hom p
          ((((X.singularCochainComplex (ModuleCat.of ℚ ℚ) ℚ (ModuleCat.of ℚ ℚ)).sc
            p).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).inv φ)) =
      HomologicalComplex.cyclesMap (intCastChainMap ℚ (toSSet.obj X)) n ≫
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
  rw [X.mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsIso_hom_iCycles_apply ℚ p φ]
  -- In the next steps, the cochains and cycles of a restricted complex appear both as
  -- those of the complex and as those of the image short complex, which agree only after
  -- unfolding `ModuleCat.restrictScalars`; `erw` sees through this.
  erw [capChain_singularCochainComplexIntChainsIso_hom_f]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  erw [reassoc_of% e₁]
  rw [← Functor.map_comp_assoc]
  erw [ChainComplex.capCycles_i]
  rw [Functor.map_comp, Category.assoc]
  erw [reassoc_of% e₂]
  exact ((reassoc_of% (HomologicalComplex.cyclesMap_i
    (intCastChainMap ℚ (toSSet.obj X)) n)) _).symm

/-- **The integral and the rational cap product agree.** For `α ∈ Hᵖ(X; ℚ)` and `μ ∈ Hₙ(X; ℤ)`,
`p + q = n`, capping `μ` with the class of `α` in the cohomology of integral chains with values in
`ℚ`, along the right unitors as in the duality map, is the rational cap product `ρ(μ) ⌢ α` of
`α` with the image `ρ(μ)` of `μ` in `Hₙ(X; ℚ)`, read in homology with coefficients in the abelian
group `ℚ`. -/
theorem singularCap_singularCohomologyIntChainsIso_hom {p q n : ℕ} (h : p + q = n)
    (α : X.singularCohomology (ModuleCat.of ℚ ℚ) ℚ (ModuleCat.of ℚ ℚ) p)
    (μ : ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj X) :
    (X.singularCap ℤ (ρ_ _).inv (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h
        ((X.singularCohomologyIntChainsIso ℚ p).hom α)).hom μ =
      (X.singularHomologyRatIso q).hom
        (X.singularCapLinearMap ℚ h (X.singularHomologyIntToRat n μ) α) := by
  obtain ⟨φ, rfl⟩ := (X.singularCochainComplex (ModuleCat.of ℚ ℚ) ℚ
    (ModuleCat.of ℚ ℚ)).moduleCat_homologyπ_surjective p α
  obtain ⟨z, rfl⟩ := ((toSSet.obj X).chainComplex
    (ModuleCat.of ℤ (ULift.{0} ℤ))).moduleCat_homologyπ_surjective n μ
  have hρ : X.singularHomologyIntToRat n
      (((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n z) =
      ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).homologyπ n
        (((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{0} ℚ))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ ℚ))).hom
            (HomologicalComplex.cyclesMap (intCastChainMap ℚ (toSSet.obj X)) n z)) :=
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
  rw [X.map_homologyπ_singularCohomologyIntChainsIso_hom_apply ℚ p φ]
  -- Elements of a restricted module and of the module itself have the same type only after
  -- unfolding, which `rw` does not do, so the two sides are compared through `Eq.trans`.
  refine (ConcreteCategory.congr_hom (X.singularCap_homologyπ ℤ (ρ_ _).inv
    (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h _) z).trans (Eq.trans ?_
      ((congrArg (fun x ↦ (X.singularHomologyRatIso q).hom (X.singularCapLinearMap ℚ h x
        ((X.singularCochainComplex (𝟙_ (ModuleCat.{0} ℚ)) ℚ
          (𝟙_ (ModuleCat.{0} ℚ))).homologyπ p φ))) hρ).trans
        ((congrArg (X.singularHomologyRatIso q).hom (hcap _)).trans (hr _))).symm)
  exact congrArg (((toSSet.obj X).chainComplex (ModuleCat.of ℤ ℚ)).homologyπ q)
    (X.capCycles_cyclesMap_singularCochainComplexIntChainsIso_hom_apply h φ z)

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
  -- Through `singularHomologyRatIso` and `singularCohomologyIntChainsIso ℚ`, the rational cap
  -- product is the integral one with values in `ℚ`, which Tau Ceti shows to be bijective.
  have e : ⇑(ConcreteCategory.hom ((TopCat.of M).singularHomologyRatIso q).hom) ∘
      ⇑((TopCat.of M).singularCapLinearMap ℚ h
        ((TopCat.of M).singularHomologyIntToRat n (o.fundamentalClass hn))) =
      (fun β ↦ ((TopCat.of M).singularCap ℤ (ρ_ _).inv (ρ_ (ModuleCat.of ℤ ℚ)).hom p q n h
        β).hom (o.fundamentalClass hn)) ∘
        ⇑(ConcreteCategory.hom ((TopCat.of M).singularCohomologyIntChainsIso ℚ p).hom) :=
    funext fun α ↦
      (TopCat.singularCap_singularCohomologyIntChainsIso_hom _ h α (o.fundamentalClass hn)).symm
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
