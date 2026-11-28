/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RelativeClass
import SymplecticGeometry.Algebra.Homology.Additive
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Change of coefficients on relative simplicial chains along restriction of scalars

Let `f : R →+* S` be a ring homomorphism, `M` an `R`-module, `N` an `S`-module and
`g : M ⟶ f^* N` an `R`-linear map. For a pair `P` of simplicial sets, the change of coefficients
`SSet.restrictScalarsChainMap f g` on the chains of the ambient simplicial set descends to the
relative chains, a map of complexes of `R`-modules `C(P; M) ⟶ f^* C(P; N)`. Its case along the
cast of integers into a ring `k` casts integral relative chains to `k`; integral chains have
coefficients `ModuleCat.of ℤ (ULift ℤ)`.

## Main declarations

* `SSetPair.restrictScalarsChainMap f g P : C(P; M) ⟶ f^* C(P; N)`: the change of coefficients
  on relative chains, obtained from `SSet.restrictScalarsChainMap` of the ambient simplicial set
  by passing to the cokernel `SSetPair.isColimitCokernelCoforkChainComplex`.
* `SSetPair.chainComplexπ_restrictScalarsChainMap`: it is characterized by its composite with
  the quotient map from ambient chains.
* `SSetPair.chainComplexMap_f_restrictScalarsChainMap`: it commutes with the chain maps of maps
  of pairs.
* `SSetPair.restrictScalarsHomologyMap f g P n : Hₙ(P; M) ⟶ f^* Hₙ(P; N)`: the induced map on
  relative homology. `SSetPair.homologyπ_restrictScalarsHomologyMap` gives it on the class of a
  relative cycle, `SSetPair.relClass_restrictScalarsHomologyMap` on the relative class
  `SSetPair.relClass` of a simplex whose faces lie in the subcomplex, and
  `SSetPair.restrictScalarsHomologyMap_naturality` says that it commutes with maps of pairs.
* `SSetPair.intCastChainMap k P : C(P; ℤ) ⟶ F (C(P; k))`: for `F` the restriction of scalars
  along `ℤ → k`, the chain map casting the coefficients of integral relative chains to `k`, the
  change of coefficients along `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`, with the
  same three lemmas.
* `SSetPair.intCastHomologyMap k P n : Hₙ(P; ℤ) ⟶ F (Hₙ(P; k))`: the induced map on relative
  homology, with `SSetPair.homologyπ_intCastHomologyMap` on classes of relative cycles,
  `SSetPair.relClass_intCastHomologyMap` on relative classes of simplices and
  `SSetPair.intCastHomologyMap_naturality` for maps of pairs.

The maps on homology follow Tau Ceti's `TopCat.restrictScalarsHomologyMap`,
`TopCat.homologyπ_restrictScalarsHomologyMap` and `TopCat.restrictScalarsHomologyMap_naturality`,
with the relative chain map in place of
`TopCat.restrictScalarsChainMap`.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Simplicial

namespace SSetPair

section RestrictScalars

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{u} R}
  {N : ModuleCat.{u} S} (g : M ⟶ (ModuleCat.restrictScalars f).obj N)

/-- Changing the coefficients of the chains of the subspace of a pair `P` of simplicial sets
along `g`, and then sending them to relative chains, gives zero. -/
theorem chainComplexMap_restrictScalarsChainMap_chainComplexπ (P : SSetPair.{u}) :
    SSet.chainComplexMap P.hom M ≫ SSet.restrictScalarsChainMap f g P.right ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (P.chainComplexπ N) = 0 := by
  ext n : 1
  have h := SSet.chainComplexMap_f_restrictScalarsChainMap f g P.hom n
  simp only [Functor.id_obj] at h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ← Category.assoc, h, Category.assoc, ← Functor.map_comp, SSetPair.chainComplex_condition_f,
    Functor.map_zero, comp_zero, HomologicalComplex.zero_f]

/-- The change of coefficients on the relative chains of a pair `P` of simplicial sets along
`g : M ⟶ f^* N`: the map of complexes of `R`-modules `C(P; M) ⟶ f^* C(P; N)` induced by
`SSet.restrictScalarsChainMap f g` on the chains of the ambient simplicial set. -/
def restrictScalarsChainMap (P : SSetPair.{u}) :
    P.chainComplex M ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj (P.chainComplex N) :=
  (P.isColimitCokernelCoforkChainComplex _).desc (CokernelCofork.ofπ
    (SSet.restrictScalarsChainMap f g P.right ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (P.chainComplexπ N))
    (chainComplexMap_restrictScalarsChainMap_chainComplexπ f g P))

/-- The change of coefficients on relative chains is the map out of the cokernel presentation
of the relative chains induced by the change of coefficients on the ambient chains followed by
the quotient map to relative chains. -/
theorem restrictScalarsChainMap_def (P : SSetPair.{u}) :
    restrictScalarsChainMap f g P =
      (P.isColimitCokernelCoforkChainComplex _).desc (CokernelCofork.ofπ
        (SSet.restrictScalarsChainMap f g P.right ≫
          ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (P.chainComplexπ N))
        (chainComplexMap_restrictScalarsChainMap_chainComplexπ f g P)) :=
  (rfl)

/-- Changing the coefficients of relative chains after the quotient map from ambient chains is
changing the coefficients of the ambient chains, followed by the quotient map. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_restrictScalarsChainMap (P : SSetPair.{u}) :
    P.chainComplexπ M ≫ restrictScalarsChainMap f g P =
      SSet.restrictScalarsChainMap f g P.right ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (P.chainComplexπ N) :=
  Cofork.IsColimit.π_desc (P.isColimitCokernelCoforkChainComplex _)

/-- `SSetPair.chainComplexπ_restrictScalarsChainMap` in degree `n`. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_f_restrictScalarsChainMap_f (P : SSetPair.{u}) (n : ℕ) :
    (P.chainComplexπ M).f n ≫ (restrictScalarsChainMap f g P).f n =
      (SSet.restrictScalarsChainMap f g P.right).f n ≫
        (ModuleCat.restrictScalars f).map ((P.chainComplexπ N).f n) := by
  rw [← HomologicalComplex.comp_f, chainComplexπ_restrictScalarsChainMap,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]

/-- The change of coefficients on relative chains commutes with the chain maps induced by maps
of pairs of simplicial sets. -/
@[reassoc]
theorem chainComplexMap_f_restrictScalarsChainMap {P Q : SSetPair.{u}} (h : P ⟶ Q) (n : ℕ) :
    (SSetPair.chainComplexMap h M).f n ≫ (restrictScalarsChainMap f g Q).f n =
      (restrictScalarsChainMap f g P).f n ≫
        (ModuleCat.restrictScalars f).map ((SSetPair.chainComplexMap h N).f n) := by
  refine (cancel_epi ((P.chainComplexπ M).f n)).1 ?_
  rw [← HomologicalComplex.comp_f_assoc, ← SSetPair.chainComplexπ_naturality,
    HomologicalComplex.comp_f_assoc, chainComplexπ_f_restrictScalarsChainMap_f,
    chainComplexπ_f_restrictScalarsChainMap_f_assoc,
    SSet.chainComplexMap_f_restrictScalarsChainMap_assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
    SSetPair.chainComplexπ_naturality]

/-- The change of coefficients on the relative homology of a pair `P` of simplicial sets along
`g : M ⟶ f^* N`: the map `Hₙ(P; M) ⟶ f^* Hₙ(P; N)` induced by `SSetPair.restrictScalarsChainMap`,
followed by the identification of the homology of the restricted complex with the restriction of
the homology. -/
def restrictScalarsHomologyMap (P : SSetPair.{u}) (n : ℕ) :
    P.homology M n ⟶ (ModuleCat.restrictScalars f).obj (P.homology N n) :=
  HomologicalComplex.homologyMap (restrictScalarsChainMap f g P) n ≫
    ((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app
      (P.chainComplex N)

/-- The change of coefficients on relative homology is the map induced on homology by the change
of coefficients on relative chains, followed by the identification of the homology of the
restricted complex with the restriction of the homology. -/
theorem restrictScalarsHomologyMap_def (P : SSetPair.{u}) (n : ℕ) :
    restrictScalarsHomologyMap f g P n =
      HomologicalComplex.homologyMap (restrictScalarsChainMap f g P) n ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app
          (P.chainComplex N) :=
  (rfl)

open HomologicalComplex in
/-- The change of coefficients on relative homology sends the class of a relative cycle `z` to
the restriction of the class of the relative cycle obtained by changing the coefficients of `z`. -/
@[reassoc]
theorem homologyπ_restrictScalarsHomologyMap (P : SSetPair.{u}) (n : ℕ) :
    (P.chainComplex M).homologyπ n ≫ restrictScalarsHomologyMap f g P n =
      HomologicalComplex.cyclesMap (restrictScalarsChainMap f g P) n ≫
        (((P.chainComplex N).sc n).mapCyclesIso (ModuleCat.restrictScalars f)).hom ≫
          (ModuleCat.restrictScalars f).map ((P.chainComplex N).homologyπ n) := by
  rw [restrictScalarsHomologyMap_def,
    homologyπ_comp_homologyMap_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app]

/-- The change of coefficients on relative homology sends the relative class of an
`(n + 1)`-simplex `s` whose faces lie in the subcomplex, with coefficients in `M`, to the relative
class of `s` with coefficients in `N`, through `g` on coefficients. -/
@[reassoc]
theorem relClass_restrictScalarsHomologyMap {P : SSetPair.{u}} {n : ℕ} (s : P.right _⦋n + 1⦌)
    (t : Fin (n + 2) → P.left _⦋n⦌) (ht : ∀ i, P.right.δ i s = P.hom.app _ (t i)) :
    SSetPair.relClass M s t ht ≫ restrictScalarsHomologyMap f g P (n + 1) =
      g ≫ (ModuleCat.restrictScalars f).map (SSetPair.relClass N s t ht) := by
  rw [SSetPair.relClass_def, SSetPair.relClass_def, Category.assoc,
    homologyπ_restrictScalarsHomologyMap, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  congr 1
  -- Both sides are maps into the restricted cycles, which `F.map iCycles` detects.
  rw [← cancel_mono ((ModuleCat.restrictScalars f).map ((P.chainComplex N).iCycles (n + 1))),
    Category.assoc, Category.assoc,
    HomologicalComplex.cyclesMap_comp_mapCyclesIso_hom_comp_map_iCycles,
    HomologicalComplex.liftCycles_i_assoc, Category.assoc,
    chainComplexπ_f_restrictScalarsChainMap_f, SSet.ιChainComplex_restrictScalarsChainMap_f_assoc,
    Category.assoc g, ← Functor.map_comp, ← Functor.map_comp, HomologicalComplex.liftCycles_i]

/-- The change of coefficients on relative homology commutes with the maps induced on relative
homology by maps of pairs of simplicial sets. -/
@[reassoc]
theorem restrictScalarsHomologyMap_naturality {P Q : SSetPair.{u}} (h : P ⟶ Q) (n : ℕ) :
    SSetPair.homologyMap h M n ≫ restrictScalarsHomologyMap f g Q n =
      restrictScalarsHomologyMap f g P n ≫
        (ModuleCat.restrictScalars f).map (SSetPair.homologyMap h N n) := by
  have hc : SSetPair.chainComplexMap h M ≫ restrictScalarsChainMap f g Q =
      restrictScalarsChainMap f g P ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map
          (SSetPair.chainComplexMap h N) := by
    ext n : 1
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, chainComplexMap_f_restrictScalarsChainMap]
  rw [restrictScalarsHomologyMap_def, restrictScalarsHomologyMap_def,
    ← HomologicalComplex.homologyMap_comp_assoc, hc, HomologicalComplex.homologyMap_comp_assoc]
  exact congrArg (_ ≫ ·)
    (((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ n).hom.naturality
      (SSetPair.chainComplexMap h N))

end RestrictScalars

section IntCast

variable (k : Type) [Ring k]

/-- The chain map `C(P; ℤ) ⟶ F (C(P; k))` that casts the coefficients of the integral relative
chains of a pair `P` of simplicial sets to `k`, the target read as a complex of abelian groups
through the restriction of scalars `F` along `ℤ → k`: the change of coefficients
`SSetPair.restrictScalarsChainMap` along the cast `ULift ℤ → k` of integers into the restricted
`k`-module `k`. -/
def intCastChainMap (P : SSetPair.{0}) :
    P.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟶
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (P.chainComplex (ModuleCat.of k k)) :=
  restrictScalarsChainMap (algebraMap ℤ k) (N := ModuleCat.of k k)
    (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) P

variable {k}

/-- The chain map casting integral relative chains to `k` is the change of coefficients
`SSetPair.restrictScalarsChainMap` along `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`,
the cast of integers into the restricted `k`-module `k`. -/
theorem intCastChainMap_def (P : SSetPair.{0}) :
    intCastChainMap k P =
      restrictScalarsChainMap (algebraMap ℤ k) (N := ModuleCat.of k k)
        (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) P :=
  (rfl)

/-- Casting the coefficients of relative chains to `k` after the quotient map from ambient
chains is casting the coefficients of the ambient chains, followed by the quotient map. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_intCastChainMap (P : SSetPair.{0}) :
    P.chainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ)) ≫ intCastChainMap k P =
      SSet.intCastChainMap k P.right ≫
        ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
          (P.chainComplexπ (ModuleCat.of k k)) := by
  rw [intCastChainMap_def, chainComplexπ_restrictScalarsChainMap, SSet.intCastChainMap_def]

/-- `SSetPair.chainComplexπ_intCastChainMap` in degree `n`. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_f_intCastChainMap_f (P : SSetPair.{0}) (n : ℕ) :
    (P.chainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ))).f n ≫ (intCastChainMap k P).f n =
      (SSet.intCastChainMap k P.right).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((P.chainComplexπ (ModuleCat.of k k)).f n) := by
  rw [intCastChainMap_def, chainComplexπ_f_restrictScalarsChainMap_f, SSet.intCastChainMap_def]

/-- Casting the coefficients of relative chains to `k` commutes with the chain maps induced by
maps of pairs of simplicial sets. -/
@[reassoc]
theorem chainComplexMap_f_intCastChainMap {P Q : SSetPair.{0}} (h : P ⟶ Q) (n : ℕ) :
    (SSetPair.chainComplexMap h (ModuleCat.of ℤ (ULift.{0} ℤ))).f n ≫
        (intCastChainMap k Q).f n =
      (intCastChainMap k P).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((SSetPair.chainComplexMap h (ModuleCat.of k k)).f n) := by
  rw [intCastChainMap_def, intCastChainMap_def, chainComplexMap_f_restrictScalarsChainMap]

variable (k) in
/-- The map `Hₙ(P; ℤ) ⟶ F (Hₙ(P; k))` that casts integral relative homology classes of a pair `P`
of simplicial sets to `k`, the target read as an abelian group through the restriction of scalars
`F` along `ℤ → k`: the change of coefficients `SSetPair.restrictScalarsHomologyMap` along the
cast `ULift ℤ → k` of integers into the restricted `k`-module `k`. -/
def intCastHomologyMap (P : SSetPair.{0}) (n : ℕ) :
    P.homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n ⟶
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).obj (P.homology (ModuleCat.of k k) n) :=
  restrictScalarsHomologyMap (algebraMap ℤ k) (N := ModuleCat.of k k)
    (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) P n

/-- The map casting integral relative homology to `k` is the change of coefficients
`SSetPair.restrictScalarsHomologyMap` along
`ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`. -/
theorem intCastHomologyMap_def (P : SSetPair.{0}) (n : ℕ) :
    intCastHomologyMap k P n =
      restrictScalarsHomologyMap (algebraMap ℤ k) (N := ModuleCat.of k k)
        (ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)) P n :=
  (rfl)

/-- The map casting integral relative homology to `k` sends the class of an integral relative
cycle `z` to the restriction of the class of `z` with its coefficients cast to `k`. -/
@[reassoc]
theorem homologyπ_intCastHomologyMap (P : SSetPair.{0}) (n : ℕ) :
    (P.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).homologyπ n ≫ intCastHomologyMap k P n =
      HomologicalComplex.cyclesMap (intCastChainMap k P) n ≫
        (((P.chainComplex (ModuleCat.of k k)).sc n).mapCyclesIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).hom ≫
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
            ((P.chainComplex (ModuleCat.of k k)).homologyπ n) := by
  rw [intCastHomologyMap_def, homologyπ_restrictScalarsHomologyMap, intCastChainMap_def]

/-- The map casting integral relative homology to `k` sends the integral relative class of an
`(n + 1)`-simplex `s` whose faces lie in the subcomplex to the relative class of `s` over `k`,
through the cast of integers to `k` on coefficients. -/
@[reassoc]
theorem relClass_intCastHomologyMap {P : SSetPair.{0}} {n : ℕ} (s : P.right _⦋n + 1⦌)
    (t : Fin (n + 2) → P.left _⦋n⦌) (ht : ∀ i, P.right.δ i s = P.hom.app _ (t i)) :
    SSetPair.relClass (ModuleCat.of ℤ (ULift.{0} ℤ)) s t ht ≫ intCastHomologyMap k P (n + 1) =
      ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k) ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          (SSetPair.relClass (ModuleCat.of k k) s t ht) := by
  rw [intCastHomologyMap_def, relClass_restrictScalarsHomologyMap]

/-- Casting integral relative homology to `k` commutes with the maps induced on relative homology
by maps of pairs of simplicial sets. -/
@[reassoc]
theorem intCastHomologyMap_naturality {P Q : SSetPair.{0}} (h : P ⟶ Q) (n : ℕ) :
    SSetPair.homologyMap h (ModuleCat.of ℤ (ULift.{0} ℤ)) n ≫ intCastHomologyMap k Q n =
      intCastHomologyMap k P n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          (SSetPair.homologyMap h (ModuleCat.of k k) n) := by
  rw [intCastHomologyMap_def, intCastHomologyMap_def, restrictScalarsHomologyMap_naturality]

end IntCast

end SSetPair

end
