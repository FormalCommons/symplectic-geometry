/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.IntegralComparison
public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Cohomology over a commutative ring from integral chains

For a commutative ring `k` and a space `X`, the `k`-linear singular cochains on chains with
coefficients in `k`, read as abelian groups through the restriction of scalars `F` along
`ℤ → k`, are the integral cochains `Hom_ℤ(C(X; ℤ), k)` with values in the abelian group `k`.
Here integral chains have coefficients `ModuleCat.of ℤ (ULift ℤ)`, as those of Tau Ceti's
fundamental class.

* `SymplecticGeometry.intCastChainMap k S : C(S; ℤ) ⟶ F (C(S; k))`: the chain map that casts
  the coefficients of the integral chains of a simplicial set `S` to `k`, the change of
  coefficients `SSet.restrictScalarsChainMap` along the cast of integers
  `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k) : ULift ℤ ⟶ F k` of Tau Ceti, which
  serves for `k = ℚ` as well as `k = ℝ`; on simplices it is
  `SymplecticGeometry.ιChainComplex_intCastChainMap_f`, on an element it is
  `SymplecticGeometry.intCastChainMap_f_ιChainComplex`, and followed by a cochain it is
  `SymplecticGeometry.intCastChainMap_f_comp_apply`.
* `SymplecticGeometry.intCastCyclesMap k S n : Z_n(S; ℤ) ⟶ F (Z_n(S; k))`: the map it induces on
  cycles, the change of coefficients `SSet.restrictScalarsCyclesMap` along the same map, which
  `SymplecticGeometry.intCastCyclesMap_eq_cyclesMap` writes with `HomologicalComplex.cyclesMap`
  and `SymplecticGeometry.intCastCyclesMap_iCycles` relates to `intCastChainMap` on chains.
* `TopCat.singularCochainComplexRestrictScalarsIso`: the restricted `k`-linear cochains are the
  same morphisms, with the action of `ℤ` of the `ℤ`-linear category `ModuleCat k`.
* `TopCat.singularCochainComplexIntChainsIso`: the comparison of cochains, the composite of the
  previous one with Tau Ceti's `TauCeti.singularCochainComplexIntegralIso` and with the change
  of chain coefficients along `TauCeti.uliftIntIso`. It takes a cochain `φ` to the integral
  cochain `a σ ↦ a φ(σ)` (`TopCat.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex`),
  and commutes with the maps induced by continuous maps
  (`TopCat.singularCochainComplexIntChainsIso_hom_naturality`).
* `TopCat.singularCochainComplexIntChainsIso_hom_f_apply`: read through integral chains, a
  cochain `ψ` is `ψ` precomposed with the chain map that casts coefficients to `k`; on the
  integral chains of a simplicial set over the singular one, this is
  `TopCat.chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f`.
* `TopCat.singularCohomologyIntChainsIso : F (Hᵖ(X; k)) ≅ Hᵖ(X; ℤ, k)`: the induced isomorphism of
  cohomology, natural under continuous maps
  (`TopCat.singularCohomologyIntChainsIso_hom_naturality`), and its value on the class of a
  cocycle (`TopCat.map_homologyπ_singularCohomologyIntChainsIso_hom`).
* `TopCat.injective_singularCohomologyMap_of_surjective`: when the abelian group `k` is
  injective, as for `ℚ` and `ℝ`, a map that is onto integral homology in degree `p` is injective
  on `Hᵖ(-; k)`, by the universal coefficient theorem `TopCat.singularKronecker_bijective` for
  integral chains with values in `k`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Simplicial TauCeti
open scoped MonoidalCategory

namespace SymplecticGeometry

variable (k : Type) [CommRing k]

/-- The chain map `C(S; ℤ) ⟶ F (C(S; k))` that casts the coefficients of the integral chains of
a simplicial set `S` to `k`, the target read as a complex of abelian groups through the
restriction of scalars `F` along `ℤ → k`: the change of coefficients
`SSet.restrictScalarsChainMap` along the cast `ULift ℤ → k` of integers into the restricted
`k`-module `k`. -/
def intCastChainMap (S : SSet.{0}) :
    S.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟶
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (S.chainComplex (ModuleCat.of k k)) :=
  SSet.restrictScalarsChainMap (algebraMap ℤ k) (N := ModuleCat.of k k)
    (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) S

variable {k} in
/-- The chain map casting integral chains to `k` is the change of coefficients
`SSet.restrictScalarsChainMap` along `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`,
the cast of integers into the restricted `k`-module `k`. -/
theorem intCastChainMap_def (S : SSet.{0}) :
    intCastChainMap k S =
      SSet.restrictScalarsChainMap (algebraMap ℤ k) (N := ModuleCat.of k k)
        (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) S :=
  (rfl)

variable {k} in
/-- The chain map casting integral chains to `k` keeps each simplex and casts its coefficient
to `k`. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_intCastChainMap_f (S : SSet.{0}) {n : ℕ} (σ : S _⦋n⦌) :
    S.ιChainComplex σ ≫ (intCastChainMap k S).f n =
      ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k) ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          (S.ιChainComplex (R := ModuleCat.of k k) σ) := by
  rw [intCastChainMap_def, SSet.ιChainComplex_restrictScalarsChainMap_f]

variable {k} in
/-- The chain map casting integral chains to `k` sends the simplex `σ` with integral coefficient
`a` to `σ` with coefficient `a` cast to `k`. -/
theorem intCastChainMap_f_ιChainComplex (S : SSet.{0}) {n : ℕ} (σ : S _⦋n⦌) (a : ULift.{0} ℤ) :
    (intCastChainMap k S).f n (S.ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ a) =
      S.ιChainComplex (R := ModuleCat.of k k) σ (a.down : k) := by
  rw [intCastChainMap_def, SSet.restrictScalarsChainMap_f_ιChainComplex,
    ModuleCat.uliftUnitToRestrictScalars_apply, eq_intCast]

variable {k} in
/-- Casting coefficients to `k` commutes with the chain maps induced by maps of simplicial sets. -/
@[reassoc]
theorem chainComplexMap_f_intCastChainMap {S T : SSet.{0}} (j : S ⟶ T) (n : ℕ) :
    (SSet.chainComplexMap j (ModuleCat.of ℤ (ULift.{0} ℤ))).f n ≫
        (intCastChainMap k T).f n =
      (intCastChainMap k S).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((SSet.chainComplexMap j (ModuleCat.of k k)).f n) := by
  rw [intCastChainMap_def, intCastChainMap_def, SSet.chainComplexMap_f_restrictScalarsChainMap]

variable {k} in
/-- Casting the coefficients of an integral chain to `k` and then applying a `k`-linear map `φ`
on chains with coefficients in `k`, read as abelian groups: the simplex `σ` with coefficient `a`
goes to `a φ(σ)`. -/
theorem intCastChainMap_f_comp_apply (S : SSet.{0}) {n : ℕ}
    (σ : S _⦋n⦌) (φ : (S.chainComplex (ModuleCat.of k k)).X n ⟶ ModuleCat.of k k)
    (a : ULift.{0} ℤ) :
    ((intCastChainMap k S).f n ≫ (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map φ ≫
        (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom)
        (S.ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ a) =
      (a.down : k) * φ (S.ιChainComplex (R := ModuleCat.of k k) σ 1) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, intCastChainMap_f_ιChainComplex]
  -- The identification of `k` with the restricted `k`-module `k`, and the restriction of scalars
  -- of `φ`, are the identity on elements, but their evaluation lemmas are stated for the
  -- underlying types, which `rw` does not identify with the carriers here.
  erw [ModuleCat.restrictScalarsAlgebraMapIso_hom_apply, ModuleCat.restrictScalars.map_apply]
  rw [← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one]

/-- The map `Z_n(S; ℤ) ⟶ F (Z_n(S; k))` that casts the coefficients of the integral `n`-cycles
of a simplicial set `S` to `k`, the target read as an abelian group through the restriction of
scalars `F` along `ℤ → k`: the change of coefficients `SSet.restrictScalarsCyclesMap` along
the cast `ULift ℤ → k` of integers into the restricted `k`-module `k`. -/
def intCastCyclesMap (S : SSet.{0}) (n : ℕ) :
    (S.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).cycles n ⟶
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).obj
        ((S.chainComplex (ModuleCat.of k k)).cycles n) :=
  SSet.restrictScalarsCyclesMap (algebraMap ℤ k) (N := ModuleCat.of k k)
    (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) S n

variable {k} in
/-- The map casting integral cycles to `k` is the change of coefficients
`SSet.restrictScalarsCyclesMap` along `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`,
the cast of integers into the restricted `k`-module `k`. -/
theorem intCastCyclesMap_def (S : SSet.{0}) (n : ℕ) :
    intCastCyclesMap k S n =
      SSet.restrictScalarsCyclesMap (algebraMap ℤ k) (N := ModuleCat.of k k)
        (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k))
        S n :=
  (rfl)

variable {k} in
/-- The map casting integral cycles to `k` is the map induced on cycles by
`SymplecticGeometry.intCastChainMap`, followed by the identification of the cycles of the
restricted complex with the restriction of the cycles. -/
theorem intCastCyclesMap_eq_cyclesMap (S : SSet.{0}) (n : ℕ) :
    intCastCyclesMap k S n =
      HomologicalComplex.cyclesMap (intCastChainMap k S) n ≫
        (((S.chainComplex (ModuleCat.of k k)).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).hom := by
  rw [intCastCyclesMap_def, SSet.restrictScalarsCyclesMap_def, intCastChainMap_def]

variable {k} in
/-- The underlying chain of an integral cycle cast to `k` is the underlying chain cast to `k`. -/
@[reassoc, elementwise nosimp]
theorem intCastCyclesMap_iCycles (S : SSet.{0}) (n : ℕ) :
    intCastCyclesMap k S n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((S.chainComplex (ModuleCat.of k k)).iCycles n) =
      (S.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).iCycles n ≫
        (intCastChainMap k S).f n := by
  rw [intCastCyclesMap_def, SSet.restrictScalarsCyclesMap_iCycles, intCastChainMap_def]

end SymplecticGeometry

namespace TopCat

variable (k : Type) [CommRing k] (X : TopCat.{0})

/-! ### Cochains -/

/-- The `k`-linear singular cochains, read as abelian groups, are the same morphisms with the
action of `ℤ` of the `ℤ`-linear category `ModuleCat k`: in each degree, Tau Ceti's
`RingHom.restrictScalarsIsoOfAddEquiv` for the identity of cochains. -/
def singularCochainComplexRestrictScalarsIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)) ≅
      X.singularCochainComplex (ModuleCat.of k k) ℤ (ModuleCat.of k k) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (algebraMap ℤ k).restrictScalarsIsoOfAddEquiv
      (Z := (X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X p)
      (W := (X.singularCochainComplex (ModuleCat.of k k) ℤ (ModuleCat.of k k)).X p)
      (AddEquiv.refl _) fun a φ ↦ by
        -- `ℤ` acts on the restricted module through `algebraMap ℤ k`, and both carriers are the
        -- cochains, on which `AddEquiv.refl` is the identity.
        change (algebraMap ℤ k a) • φ = a • φ
        rw [algebraMap_int_eq, eq_intCast]
        exact Int.cast_smul_eq_zsmul k a φ)
    fun _ _ _ ↦ by
      ext φ
      -- The cochains of the restricted complex have the type of its objects, which `rw` does not
      -- identify with the carrier in the evaluation lemmas.
      erw [ModuleCat.comp_apply, ModuleCat.comp_apply,
        RingHom.restrictScalarsIsoOfAddEquiv_hom_apply,
        RingHom.restrictScalarsIsoOfAddEquiv_hom_apply]
      rfl

/-- The identification of restricted `k`-linear cochains with `k`-linear cochains under the
action of `ℤ` is the identity on cochains. -/
theorem singularCochainComplexRestrictScalarsIso_hom_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (X.singularCochainComplexRestrictScalarsIso k).hom.f p φ = φ :=
  RingHom.restrictScalarsIsoOfAddEquiv_hom_apply (algebraMap ℤ k)
    (Z := (X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X p)
    (W := (X.singularCochainComplex (ModuleCat.of k k) ℤ (ModuleCat.of k k)).X p)
    (AddEquiv.refl _) _ φ

/-- The inverse identification of `k`-linear cochains under the action of `ℤ` with restricted
`k`-linear cochains is the identity on cochains. -/
theorem singularCochainComplexRestrictScalarsIso_inv_f_apply (p : ℕ)
    (φ : ((toSSet.obj X).chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (X.singularCochainComplexRestrictScalarsIso k).inv.f p φ = φ :=
  RingHom.restrictScalarsIsoOfAddEquiv_inv_apply (algebraMap ℤ k)
    (Z := (X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X p)
    (W := (X.singularCochainComplex (ModuleCat.of k k) ℤ (ModuleCat.of k k)).X p)
    (AddEquiv.refl _) _ φ

/-- **Cochains over `k` as integral cochains**: the `k`-linear cochains `Hom_k(C(X; k), k)`,
read as abelian groups, are the integral cochains `Hom_ℤ(C(X; ℤ), k)`. A cochain `φ` goes to
the integral cochain `a σ ↦ a φ(σ)`
(`TopCat.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex`). -/
def singularCochainComplexIntChainsIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)) ≅
      X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) :=
  X.singularCochainComplexRestrictScalarsIso k ≪≫
    singularCochainComplexIntegralIso k (ModuleCat.of k k) X ≪≫
      (ChainComplex.linearYonedaFunctor ℤ (ModuleCat.of ℤ k)).mapIso
        (((SSet.chainComplexFunctor _).mapIso uliftIntIso).app (toSSet.obj X)).op

/-- The comparison of cochains is the identification of restricted cochains with cochains under
the action of `ℤ`, then Tau Ceti's comparison with integral cochains, then the change of chain
coefficients along `ULift ℤ ≅ ℤ`. -/
theorem singularCochainComplexIntChainsIso_def :
    X.singularCochainComplexIntChainsIso k =
      X.singularCochainComplexRestrictScalarsIso k ≪≫
        singularCochainComplexIntegralIso k (ModuleCat.of k k) X ≪≫
          (ChainComplex.linearYonedaFunctor ℤ (ModuleCat.of ℤ k)).mapIso
            (((SSet.chainComplexFunctor _).mapIso uliftIntIso).app (toSSet.obj X)).op :=
  (rfl)

/-- The comparison of cochains takes a cochain `φ` to the integral cochain sending `a σ` to
`a φ(σ)`. -/
theorem singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex {p : ℕ}
    (σ : (toSSet.obj X) _⦋p⦌)
    (φ : ((toSSet.obj X).chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k)
    (a : ULift.{0} ℤ) :
    ConcreteCategory.hom (X := ((toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).X p)
        (Y := ModuleCat.of ℤ k) ((X.singularCochainComplexIntChainsIso k).hom.f p φ)
        ((toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) σ a) =
      (a.down : k) * φ ((toSSet.obj X).ιChainComplex (R := ModuleCat.of k k) σ 1) := by
  -- The comparison is the identity on morphisms, then Tau Ceti's comparison, then precomposition
  -- with the chain map induced by `ULift ℤ ≅ ℤ`, which takes `a σ` to `a.down σ`.
  have e : (X.singularCochainComplexIntChainsIso k).hom.f p φ =
      (((SSet.chainComplexFunctor _).map uliftIntIso.hom).app (toSSet.obj X)).f p ≫
        (singularCochainComplexIntegralIso k (ModuleCat.of k k) X).hom.f p φ := by
    -- The cochains of the restricted complex and their image under the first isomorphism have
    -- different types, which `rw` does not identify.
    rw [singularCochainComplexIntChainsIso_def, Iso.trans_hom, HomologicalComplex.comp_f]
    erw [ConcreteCategory.comp_apply, singularCochainComplexRestrictScalarsIso_hom_f_apply]
    rfl
  have h := SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc uliftIntIso.hom σ
    ((singularCochainComplexIntegralIso k (ModuleCat.of k k) X).hom.f p φ)
  rw [← e] at h
  refine (ConcreteCategory.congr_hom h a).trans ?_
  rw [ModuleCat.comp_apply, uliftIntIso_hom_apply]
  exact (simplicialCochainComplexIntegralIso_hom_f_apply_ιChainComplex k (ModuleCat.of k k)
    (toSSet.obj X) p φ σ a.down).trans (zsmul_eq_mul _ _)

variable {X} in
/-- The comparison of cochains commutes with the maps induced by a continuous map. -/
@[reassoc]
theorem singularCochainComplexIntChainsIso_hom_naturality {Y : TopCat.{0}} (f : X ⟶ Y) :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
        (singularCochainComplexMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k) f) ≫
      (X.singularCochainComplexIntChainsIso k).hom =
    (Y.singularCochainComplexIntChainsIso k).hom ≫
      singularCochainComplexMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ k) f := by
  ext p φ : 3
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  ext a
  refine (X.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex k σ _ a).trans ?_
  -- Both sides evaluate `φ` on the image `f ∘ σ` of the simplex; the maps induced by `f` act
  -- by precomposition with the chain map, and restriction of scalars keeps morphisms.
  refine congrArg (_ * ·) (ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f_assoc (f := toSSet.map f) (x := σ) (h := φ)) 1) |>.trans ?_
  exact ((ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f_assoc (f := toSSet.map f) (x := σ)
    (h := (Y.singularCochainComplexIntChainsIso k).hom.f p φ)) a).trans
    (Y.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex k _ φ a)).symm

/-- **Restricting a cochain to integral chains.** Read through integral chains, a `k`-linear
cochain `ψ` of `X` is `ψ` precomposed with the chain map that casts the coefficients of integral
chains to `k` (`SymplecticGeometry.intCastChainMap`). -/
theorem singularCochainComplexIntChainsIso_hom_f_apply (p : ℕ)
    (ψ : ((toSSet.obj X).chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (X.singularCochainComplexIntChainsIso k).hom.f p ψ =
      (SymplecticGeometry.intCastChainMap k (toSSet.obj X)).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map ψ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom := by
  refine SSet.chainComplex_hom_ext fun σ ↦ ?_
  ext a
  refine (X.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex k σ ψ a).trans ?_
  rw [ConcreteCategory.comp_apply,
    SymplecticGeometry.intCastChainMap_f_comp_apply]

variable {X} in
/-- **Restricting a cochain to integral chains of a simplicial set over `X`.** For a map
`j : S ⟶ toSSet X` of simplicial sets and a `k`-linear cochain `ψ` of `X`, the cochain `ψ` read
through integral chains, on the image under `j` of a chain of `S` with coefficients `ULift ℤ`, is
`ψ` on the image under `j` of that chain with its coefficients cast to `k`
(`SymplecticGeometry.intCastChainMap`). -/
theorem chainComplexMap_f_singularCochainComplexIntChainsIso_hom_f {S : SSet.{0}}
    (j : S ⟶ toSSet.obj X) (p : ℕ)
    (ψ : ((toSSet.obj X).chainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (SSet.chainComplexMap j (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫
        (X.singularCochainComplexIntChainsIso k).hom.f p ψ =
      (SymplecticGeometry.intCastChainMap k S).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
            ((SSet.chainComplexMap j (ModuleCat.of k k)).f p ≫ ψ) ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom := by
  rw [singularCochainComplexIntChainsIso_hom_f_apply,
    SymplecticGeometry.chainComplexMap_f_intCastChainMap_assoc, Functor.map_comp, Category.assoc]

/-! ### Cohomology -/

/-- **Cohomology over `k` from integral chains**: singular cohomology computed from chains with
coefficients in `k`, read as an abelian group, is singular cohomology computed from integral
chains with values in `k`. -/
def singularCohomologyIntChainsIso (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).obj
        (X.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) p) ≅
      X.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) p :=
  (((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapHomologyIso
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).symm ≪≫
    HomologicalComplex.homologyMapIso (X.singularCochainComplexIntChainsIso k) p

/-- The comparison of cohomologies is the comparison of the homology of the restricted complex
with the restricted homology, followed by the map induced by the comparison of cochains. -/
theorem singularCohomologyIntChainsIso_hom (p : ℕ) :
    (X.singularCohomologyIntChainsIso k p).hom =
      (((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapHomologyIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ≫
      HomologicalComplex.homologyMap (X.singularCochainComplexIntChainsIso k).hom p :=
  (rfl)

/-- The comparison of cohomologies on the class of a cocycle `φ` is the class of the integral
cocycle `a σ ↦ a φ(σ)`. -/
@[reassoc, elementwise]
theorem map_homologyπ_singularCohomologyIntChainsIso_hom (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
        ((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ p) ≫
      (X.singularCohomologyIntChainsIso k p).hom =
    (((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ≫
      HomologicalComplex.cyclesMap (X.singularCochainComplexIntChainsIso k).hom p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ k)).homologyπ p := by
  rw [singularCohomologyIntChainsIso_hom]
  -- The class map of the image short complex is that of the restricted cochain complex only
  -- after unfolding, so the two squares are pasted as terms.
  exact ((ShortComplex.map_homologyπ_comp_mapHomologyIso_inv_assoc
    ((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p)
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))) _).trans
    (congrArg (_ ≫ ·)
      (HomologicalComplex.homologyπ_naturality (X.singularCochainComplexIntChainsIso k).hom p))

/-- On cocycles, the comparison of cohomologies is the comparison of the underlying cochains. -/
@[reassoc, elementwise nosimp]
theorem mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsIso_hom_iCycles (p : ℕ) :
    (((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ≫
      HomologicalComplex.cyclesMap (X.singularCochainComplexIntChainsIso k).hom p ≫
        (X.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ k)).iCycles p =
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((X.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles p) ≫
        (X.singularCochainComplexIntChainsIso k).hom.f p := by
  rw [HomologicalComplex.cyclesMap_i]
  -- The cycles of the restricted complex are those of the image short complex only after
  -- unfolding, so the square is pasted as a term.
  exact (reassoc_of% (((X.singularCochainComplex (ModuleCat.of k k) k
    (ModuleCat.of k k)).sc p).mapCyclesIso_inv_comp_iCycles
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)))) _

variable {X} in
/-- The comparison of cohomologies commutes with the maps induced by a continuous map. -/
@[reassoc]
theorem singularCohomologyIntChainsIso_hom_naturality {Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
        (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k)
          f p) ≫
      (X.singularCohomologyIntChainsIso k p).hom =
    (Y.singularCohomologyIntChainsIso k p).hom ≫
      TopCat.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ k) f p := by
  rw [singularCohomologyIntChainsIso_hom, singularCohomologyIntChainsIso_hom, Category.assoc,
    TopCat.singularCohomologyMap, TopCat.singularCohomologyMap,
    ← HomologicalComplex.homologyMap_comp, ← singularCochainComplexIntChainsIso_hom_naturality,
    HomologicalComplex.homologyMap_comp]
  -- The map on cohomology is the map on the homology of the short complexes in degree `p`, and
  -- the restriction of the map of complexes is the map of the restricted short complexes.
  exact (ShortComplex.mapHomologyIso_inv_naturality_assoc
    ((HomologicalComplex.shortComplexFunctor _ _ p).map
      (singularCochainComplexMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k) f))
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)) _)

variable {X} in
open AlgebraicTopology in
/-- **Injectivity on cohomology over `k` from surjectivity on integral homology.** Let `k` be a
commutative ring whose underlying abelian group is an injective `ℤ`-module, such as `ℚ` or `ℝ`.
If a continuous map `f : X ⟶ Y` induces a surjection `Hₚ(X; ℤ) → Hₚ(Y; ℤ)`, then it induces an
injection `Hᵖ(Y; k) → Hᵖ(X; k)`. -/
theorem injective_singularCohomologyMap_of_surjective [Injective (ModuleCat.of ℤ k)]
    {Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (hf : Function.Surjective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (𝟙_ (ModuleCat.{0} ℤ))).map f)) :
    Function.Injective
      (TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k)
        f p) := by
  -- Homology with the coefficients `ULift ℤ` of integral chains is homology with coefficients
  -- `ℤ`, naturally in the space, so `f` is onto it too.
  let E := (singularHomologyFunctor (ModuleCat.{0} ℤ) p).mapIso integralCoeffIso
  have hf' : Function.Surjective
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        f) := by
    have h : ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map f = (E.app X).hom ≫
          ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (𝟙_ (ModuleCat.{0} ℤ))).map f ≫
            (E.app Y).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      exact E.hom.naturality f
    rw [h]
    exact ((ConcreteCategory.bijective_of_isIso (E.app Y).inv).2.comp hf).comp
      (ConcreteCategory.bijective_of_isIso (E.app X).hom).2
  -- Read through integral chains, a class is determined by its Kronecker pairings, as the
  -- values `k` are injective.
  have key : ∀ c : Y.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) p,
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) p).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map f ≫
        Y.singularKronecker ℤ p ((Y.singularCohomologyIntChainsIso k p).hom c) =
      X.singularKronecker ℤ p ((X.singularCohomologyIntChainsIso k p).hom
        (TopCat.singularCohomologyMap f p c)) := fun c => by
    rw [← singularKronecker_naturality]
    exact congrArg _
      (congrArg (fun φ => φ c) (singularCohomologyIntChainsIso_hom_naturality k f p)).symm
  intro a b hab
  refine (ConcreteCategory.bijective_of_isIso (Y.singularCohomologyIntChainsIso k p).hom).1 ?_
  refine (Y.singularKronecker_bijective (R := ModuleCat.of ℤ (ULift.{0} ℤ))
    (M := ModuleCat.of ℤ k) ℤ p).1 ?_
  ext z
  obtain ⟨y, rfl⟩ := hf' z
  have h := congrArg (fun φ => φ y) ((key a).trans (hab ▸ key b).symm)
  simpa using h

end TopCat

end
