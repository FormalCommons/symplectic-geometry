/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.Relative
import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing
import all TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Change of coefficients in the singular homology of a pair

A morphism of coefficients `φ : R ⟶ R'` induces a map of relative singular chains
`C(X, A; R) ⟶ C(X, A; R')`, the component of the bifunctor `SSetPair.chainComplexFunctor`, and
hence a map `Hₙ(X, A; R) ⟶ Hₙ(X, A; R')`. This map commutes with the maps induced by maps of
pairs (`TopPair.singularHomologyMap_coefficient_naturality`): this is
`SSetPair.homologyMap_coefficient_naturality` for the pairs of singular simplicial sets. It is the
homology counterpart of `TopPair.singularCohomologyChainCoefficientMap_naturality`
(`SymplecticGeometry/AlgebraicTopology/Cohomology/PairChangeOfCoefficients.lean`).

In an abelian category the change of coefficients is a morphism of the short exact sequences of
singular chains of a pair, so it also commutes with the connecting morphism
(`TopPair.singularHomologyδ_coefficient_naturality`).

Tau Ceti's isomorphism `TopPair.uliftIntSingularHomologyIso`, from coefficients `ULift ℤ` to `ℤ`,
is such a change of coefficients, along `TauCeti.uliftIntIso`
(`TopPair.uliftIntSingularHomologyIso_hom`).
-/

public section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

/-- The change of coefficients along `φ : R ⟶ R'` commutes with the map on relative singular
homology induced by a map of pairs `f : P ⟶ P'`. -/
@[reassoc]
theorem singularHomologyMap_coefficient_naturality {P P' : TopPair.{w}} (f : P ⟶ P') {R R' : C}
    (φ : R ⟶ R') (n : ℕ) :
    homologyMap (((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P)) n ≫
        TopPair.singularHomologyMap f R' n =
      TopPair.singularHomologyMap f R n ≫
        homologyMap (((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P')) n :=
  SSetPair.homologyMap_coefficient_naturality (toSSetPair.map f) φ n

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The change of coefficients along `φ : R ⟶ R'`, as a morphism from the short exact sequence
`C(A; R) ⟶ C(X; R) ⟶ C(X, A; R)` of singular chains of a pair `(X, A)` to the one with
coefficients `R'`. -/
private noncomputable def singularChainComplexShortComplexCoefficientMap (P : TopPair.{w})
    {R R' : C} (φ : R ⟶ R') :
    P.singularChainComplexShortComplex R ⟶ P.singularChainComplexShortComplex R' where
  τ₁ := ((SSet.chainComplexFunctor C).map φ).app (toSSetPair.obj P).left
  τ₂ := ((SSet.chainComplexFunctor C).map φ).app (toSSetPair.obj P).right
  τ₃ := ((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P)
  comm₁₂ := (((SSet.chainComplexFunctor C).map φ).naturality (toSSetPair.obj P).hom).symm
  comm₂₃ := by
    have h := P.singularChainComplexπ_coefficient_naturality φ
    rw [TauCeti.singularChainComplexFunctor_map_app] at h
    exact h

/-- The change of coefficients along `φ : R ⟶ R'` commutes with the connecting morphism
`Hₙ(X, A) ⟶ Hₘ(A)` of a pair. -/
@[reassoc]
theorem singularHomologyδ_coefficient_naturality (P : TopPair.{w}) {R R' : C} (φ : R ⟶ R')
    (n m : ℕ) (h : m + 1 = n := by lia) :
    P.singularHomologyδ R n m h ≫
        homologyMap (((SSet.chainComplexFunctor C).map φ).app (toSSetPair.obj P).left) m =
      homologyMap (((SSetPair.chainComplexFunctor C).map φ).app (toSSetPair.obj P)) n ≫
        P.singularHomologyδ R' n m h := by
  rw [TopPair.singularHomologyδ, TopPair.singularHomologyδ, SSetPair.homologyδ.eq_1,
    SSetPair.homologyδ.eq_1]
  exact HomologicalComplex.HomologySequence.δ_naturality
    (singularChainComplexShortComplexCoefficientMap P φ)
    (P.shortExact_singularChainComplexShortComplex R)
    (P.shortExact_singularChainComplexShortComplex R') n m (by simpa)

end Abelian

/-- Tau Ceti's change of coefficients `TopPair.uliftIntSingularHomologyIso`, from `ULift ℤ` to `ℤ`,
is the map in homology induced by `TauCeti.uliftIntIso` on relative singular chains. -/
lemma uliftIntSingularHomologyIso_hom (P : TopPair.{0}) (k : ℕ) :
    (uliftIntSingularHomologyIso P k).hom =
      homologyMap (((SSetPair.chainComplexFunctor (ModuleCat.{0} ℤ)).map
        TauCeti.uliftIntIso.hom).app (toSSetPair.obj P)) k :=
  (rfl)

end TopPair

end
