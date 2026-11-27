/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RestrictScalars
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Basic

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
* `SSetPair.intCastChainMap k P : C(P; ℤ) ⟶ F (C(P; k))`: for `F` the restriction of scalars
  along `ℤ → k`, the chain map casting the coefficients of integral relative chains to `k`, the
  change of coefficients along `ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k)`, with the
  same three lemmas.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits

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

end IntCast

end SSetPair

end
