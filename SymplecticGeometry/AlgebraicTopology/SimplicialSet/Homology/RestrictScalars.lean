/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing

/-!
# Change of coefficients on simplicial chains along restriction of scalars

Let `f : R →+* S` be a ring homomorphism, `M` an `R`-module, `N` an `S`-module and
`g : M ⟶ f^* N` an `R`-linear map into `N` with scalars restricted along `f`. For a simplicial set
`X`, the map `g` on coefficients induces a map of complexes of `R`-modules
`C(X; M) ⟶ f^* C(X; N)`, `∑ mᵢ xᵢ ↦ ∑ g(mᵢ) xᵢ`. The typical case is `ℤ → ℝ`, which turns an
integral chain into a real one.

## Main declarations

* `SSet.restrictScalarsChainMap f g X`: the chain map `C(X; M) ⟶ f^* C(X; N)` induced by `g`.
* `SSet.ιChainComplex_restrictScalarsChainMap_f`, `SSet.restrictScalarsChainMap_f_ιChainComplex`:
  it sends the simplex `x` with coefficient `m` to `x` with coefficient `g m`.
* `SSet.chainComplexMap_f_restrictScalarsChainMap`: it commutes with the chain maps induced by
  maps of simplicial sets.
* `SSet.restrictScalarsChainIso f e X`: for an isomorphism `e : M ≅ f^* N`, the isomorphism
  `C(X; M) ≅ f^* C(X; N)` whose forward map is `SSet.restrictScalarsChainMap f e.hom X`, with
  `SSet.ιChainComplex_restrictScalarsChainIso_hom_f` and
  `SSet.map_ιChainComplex_restrictScalarsChainIso_inv_f` on simplices.

## Implementation notes

The chain map is the map induced by `g` on chain complexes, followed by the inverse of Mathlib's
`SSet.chainComplexFunctorObjCompMapIso`, which identifies the chains with coefficients `f^* N`
with the restriction of scalars of the chains with coefficients `N`.
-/

public section

noncomputable section

universe u

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace SSet

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S) {M : ModuleCat.{u} R}
  {N : ModuleCat.{u} S} (g : M ⟶ (ModuleCat.restrictScalars f).obj N)

/-- The change of coefficients on simplicial chains along `g : M ⟶ f^* N`,
`∑ mᵢ xᵢ ↦ ∑ g(mᵢ) xᵢ`: a map of complexes of `R`-modules from the chains of `X` with
coefficients in `M` to the chains of `X` with coefficients in `N`, with scalars restricted
along `f`. -/
def restrictScalarsChainMap (X : SSet.{u}) :
    X.chainComplex M ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj (X.chainComplex N) :=
  ((chainComplexFunctor _).map g).app X ≫
    (chainComplexFunctorObjCompMapIso (ModuleCat.restrictScalars f) N).inv.app X

/-- The change of coefficients along `g` sends the summand of a simplex `x` to the summand
of `x`, through `g` on coefficients. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_restrictScalarsChainMap_f (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (restrictScalarsChainMap f g X).f n =
      g ≫ (ModuleCat.restrictScalars f).map (X.ιChainComplex x) := by
  rw [restrictScalarsChainMap, HomologicalComplex.comp_f,
    ιChainComplex_chainComplexFunctor_map_app_f_assoc,
    ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f]

/-- The change of coefficients along `g` sends the simplex `x` with coefficient `m` to `x` with
coefficient `g m`. -/
theorem restrictScalarsChainMap_f_ιChainComplex (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) (m : M) :
    ((restrictScalarsChainMap f g X).f n).hom ((X.ιChainComplex (R := M) x).hom m) =
      (X.ιChainComplex (R := N) x).hom (g.hom m) := by
  rw [← ModuleCat.comp_apply, ιChainComplex_restrictScalarsChainMap_f, ModuleCat.comp_apply,
    ModuleCat.restrictScalars.map_apply]

/-- The change of coefficients along `g` commutes with the chain maps induced by maps of
simplicial sets. -/
@[reassoc]
theorem chainComplexMap_f_restrictScalarsChainMap {X Y : SSet.{u}} (h : X ⟶ Y) (n : ℕ) :
    (chainComplexMap h M).f n ≫ (restrictScalarsChainMap f g Y).f n =
      (restrictScalarsChainMap f g X).f n ≫
        (ModuleCat.restrictScalars f).map ((chainComplexMap h N).f n) := by
  refine chainComplex_hom_ext fun x ↦ ?_
  rw [ι_chainComplexMap_f_assoc, ιChainComplex_restrictScalarsChainMap_f,
    ιChainComplex_restrictScalarsChainMap_f_assoc, ← Functor.map_comp, ι_chainComplexMap_f]

section Iso

variable (e : M ≅ (ModuleCat.restrictScalars f).obj N)

/-- The change of coefficients along an isomorphism `e : M ≅ f^* N`: an isomorphism of
complexes of `R`-modules from the chains of `X` with coefficients in `M` to the chains of `X`
with coefficients in `N`, with scalars restricted along `f`. -/
def restrictScalarsChainIso (X : SSet.{u}) :
    X.chainComplex M ≅
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj (X.chainComplex N) :=
  ((chainComplexFunctor _).mapIso e).app X ≪≫
    (chainComplexFunctorObjCompMapIso (ModuleCat.restrictScalars f) N).symm.app X

/-- The forward map of the change of coefficients along `e` is the change of coefficients
along `e.hom`. -/
theorem restrictScalarsChainIso_hom (X : SSet.{u}) :
    (restrictScalarsChainIso f e X).hom = restrictScalarsChainMap f e.hom X :=
  (rfl)

/-- The change of coefficients along `e` sends the summand of a simplex `x` to the summand
of `x`, through `e` on coefficients. -/
@[reassoc (attr := simp)]
theorem ιChainComplex_restrictScalarsChainIso_hom_f (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (restrictScalarsChainIso f e X).hom.f n =
      e.hom ≫ (ModuleCat.restrictScalars f).map (X.ιChainComplex x) := by
  rw [restrictScalarsChainIso_hom, ιChainComplex_restrictScalarsChainMap_f]

/-- The inverse of the change of coefficients along `e` sends the restricted summand of a
simplex `x` to the summand of `x`, through `e⁻¹` on coefficients. -/
@[reassoc (attr := simp)]
theorem map_ιChainComplex_restrictScalarsChainIso_inv_f (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) :
    (ModuleCat.restrictScalars f).map (X.ιChainComplex x) ≫
        (restrictScalarsChainIso f e X).inv.f n =
      e.inv ≫ X.ιChainComplex x := by
  rw [← cancel_epi e.hom, ← ιChainComplex_restrictScalarsChainIso_hom_f_assoc,
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f, Category.comp_id,
    e.hom_inv_id_assoc]

/-- The change of coefficients along `e` sends the simplex `x` with coefficient `m` to `x`
with coefficient `e m`. -/
theorem restrictScalarsChainIso_hom_f_ιChainComplex (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (m : M) :
    ((restrictScalarsChainIso f e X).hom.f n).hom ((X.ιChainComplex (R := M) x).hom m) =
      (X.ιChainComplex (R := N) x).hom (e.hom.hom m) := by
  rw [restrictScalarsChainIso_hom, restrictScalarsChainMap_f_ιChainComplex]

/-- The inverse of the change of coefficients along `e` sends the simplex `x` with
coefficient `m` to `x` with coefficient `e⁻¹ m`. -/
theorem restrictScalarsChainIso_inv_f_ιChainComplex (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (m : N) :
    ((restrictScalarsChainIso f e X).inv.f n).hom ((X.ιChainComplex (R := N) x).hom m) =
      (X.ιChainComplex (R := M) x).hom (e.inv.hom m) :=
  -- The coefficient `m` is read in `f^* N`, whose carrier is that of `N`.
  ConcreteCategory.congr_hom (map_ιChainComplex_restrictScalarsChainIso_inv_f f e X x) m

end Iso

end SSet
