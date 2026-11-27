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
# Casting integral relative simplicial chains to a commutative ring

For a commutative ring `k`, a pair `P` of simplicial sets, and `F` the restriction of scalars
along `ℤ → k`, this file casts the coefficients of the integral relative chains of `P` to `k`.
Integral chains have coefficients `ModuleCat.of ℤ (ULift ℤ)`.

## Main declarations

* `SSetPair.intCastChainMap k P : C(P; ℤ) ⟶ F (C(P; k))`: the chain map casting the coefficients
  of integral relative chains to `k`, obtained from `SSet.intCastChainMap` of the ambient
  simplicial set by passing to the cokernel `SSetPair.isColimitCokernelCoforkChainComplex`.
* `SSetPair.chainComplexπ_intCastChainMap`: it is characterized by its composite with the
  quotient map from ambient chains.
* `SSetPair.chainComplexMap_f_intCastChainMap`: it commutes with the chain maps of maps of pairs.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace SSetPair

variable (k : Type) [CommRing k]

/-- Casting the coefficients of the chains of the subspace of a pair `P` of simplicial sets to
`k`, and then sending them to relative chains, gives zero. -/
theorem chainComplexMap_intCastChainMap_chainComplexπ (P : SSetPair.{0}) :
    SSet.chainComplexMap P.hom (ModuleCat.of ℤ (ULift.{0} ℤ)) ≫ SSet.intCastChainMap k P.right ≫
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
        (P.chainComplexπ (ModuleCat.of k k)) = 0 := by
  ext n : 1
  have h := SSet.chainComplexMap_f_intCastChainMap (k := k) P.hom n
  simp only [Functor.id_obj] at h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ← Category.assoc, h, Category.assoc, ← Functor.map_comp, SSetPair.chainComplex_condition_f,
    Functor.map_zero, comp_zero, HomologicalComplex.zero_f]

/-- The chain map `C(P; ℤ) ⟶ F (C(P; k))` that casts the coefficients of the integral relative
chains of a pair `P` of simplicial sets to `k`, the target read as a complex of abelian groups
through the restriction of scalars `F` along `ℤ → k`: the chain map
`SSet.intCastChainMap` of the ambient simplicial set, followed by the quotient map
to relative chains, descended along the cokernel presentation of the relative chains. -/
def intCastChainMap (P : SSetPair.{0}) :
    P.chainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ⟶
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (P.chainComplex (ModuleCat.of k k)) :=
  (P.isColimitCokernelCoforkChainComplex _).desc (CokernelCofork.ofπ
    (SSet.intCastChainMap k P.right ≫
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
        (P.chainComplexπ (ModuleCat.of k k)))
    (chainComplexMap_intCastChainMap_chainComplexπ k P))

variable {k} in
/-- The chain map casting integral relative chains to `k` is the map out of the cokernel
presentation of the relative chains induced by `SSet.intCastChainMap` of the
ambient simplicial set followed by the quotient map to relative chains. -/
theorem intCastChainMap_def (P : SSetPair.{0}) :
    SSetPair.intCastChainMap k P =
      (P.isColimitCokernelCoforkChainComplex _).desc (CokernelCofork.ofπ
        (SSet.intCastChainMap k P.right ≫
          ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
            (P.chainComplexπ (ModuleCat.of k k)))
        (chainComplexMap_intCastChainMap_chainComplexπ k P)) :=
  (rfl)

variable {k}

/-- Casting the coefficients of relative chains to `k` after the quotient map from ambient
chains is casting the coefficients of the ambient chains, followed by the quotient map. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_intCastChainMap (P : SSetPair.{0}) :
    P.chainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ)) ≫ SSetPair.intCastChainMap k P =
      SSet.intCastChainMap k P.right ≫
        ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
          (P.chainComplexπ (ModuleCat.of k k)) :=
  Cofork.IsColimit.π_desc (P.isColimitCokernelCoforkChainComplex _)

/-- `SSetPair.chainComplexπ_intCastChainMap` in degree `n`. -/
@[reassoc (attr := simp)]
theorem chainComplexπ_f_intCastChainMap_f (P : SSetPair.{0}) (n : ℕ) :
    (P.chainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ))).f n ≫ (SSetPair.intCastChainMap k P).f n =
      (SSet.intCastChainMap k P.right).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((P.chainComplexπ (ModuleCat.of k k)).f n) := by
  rw [← HomologicalComplex.comp_f, SSetPair.chainComplexπ_intCastChainMap,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]

/-- Casting the coefficients of relative chains to `k` commutes with the chain maps induced by
maps of pairs of simplicial sets. -/
@[reassoc]
theorem chainComplexMap_f_intCastChainMap {P Q : SSetPair.{0}} (f : P ⟶ Q) (n : ℕ) :
    (SSetPair.chainComplexMap f (ModuleCat.of ℤ (ULift.{0} ℤ))).f n ≫
        (SSetPair.intCastChainMap k Q).f n =
      (SSetPair.intCastChainMap k P).f n ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((SSetPair.chainComplexMap f (ModuleCat.of k k)).f n) := by
  refine (cancel_epi ((P.chainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ))).f n)).1 ?_
  rw [← HomologicalComplex.comp_f_assoc, ← SSetPair.chainComplexπ_naturality,
    HomologicalComplex.comp_f_assoc, SSetPair.chainComplexπ_f_intCastChainMap_f,
    SSetPair.chainComplexπ_f_intCastChainMap_f_assoc, SSet.chainComplexMap_f_intCastChainMap_assoc,
    ← Functor.map_comp, ← Functor.map_comp, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, SSetPair.chainComplexπ_naturality]

end SSetPair

end
