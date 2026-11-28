/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.IntegralChains
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Relative.RestrictScalars
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import SymplecticGeometry.AlgebraicTopology.Singular.RelativeClass

/-!
# Cohomology of a pair over a commutative ring from integral chains

For a commutative ring `k` and a topological pair `P = (X, A)`, the `k`-linear relative cochains
`Hom_k(C(X, A; k), k)`, read as abelian groups through the restriction of scalars `F` along
`ℤ → k`, are the integral relative cochains `Hom_ℤ(C(X, A; ℤ), k)`, integral chains having
coefficients `ModuleCat.of ℤ (ULift ℤ)`. This is the counterpart for pairs of
`TopCat.singularCohomologyIntChainsIso` (`IntegralChains.lean`).

* `TopPair.singularCochainComplexIntChainsIso`: the comparison of relative cochains, precomposing
  a cochain with the chain map `SSetPair.intCastChainMap` that casts integral relative chains to
  `k` (`SimplicialSet/Homology/Relative/RestrictScalars.lean`) and identifying the values with
  the abelian group `k` (`TopPair.singularCochainComplexIntChainsHom_f_apply`). It is an
  isomorphism by the four lemma `CategoryTheory.ShortComplex.epi_of_mono_of_epi_of_mono`,
  applied to the comparison of the short exact cochain sequences of the pair (Tau Ceti's
  `TopPair.shortExact_singularCochainComplexShortComplex`) that the absolute comparisons for `X`
  and for `A` complete.
* `TopPair.singularCohomologyIntChainsIso : F (Hᵖ(X, A; k)) ≅ Hᵖ(X, A; ℤ, k)`: the induced
  isomorphism of cohomology, natural in maps of pairs
  (`TopPair.singularCohomologyIntChainsIso_hom_naturality`), and compatible with the map to the
  cohomology of `X` and `TopCat.singularCohomologyIntChainsIso` there
  (`TopPair.singularCohomologyπ_singularCohomologyIntChainsIso_hom`). On the class of a cocycle it
  is the class of the compared cocycle (`TopPair.map_homologyπ_singularCohomologyIntChainsIso_hom`,
  `TopPair.mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsHom_iCycles`).
* `TopPair.singularKronecker_singularCohomologyIntChainsIso_hom_relClass`: a class over `k`, read
  through integral chains, evaluates on the integral class `TopPair.relClass` of a singular
  simplex whose faces lie in the subspace as the class itself evaluates on the class of that
  simplex over `k`: both pairings evaluate a cocycle on the simplex
  (`TopPair.relClass_comp_singularKronecker_homologyπ`), and the comparison of cochains casts the
  coefficient `1` to `k`.

The cochain comparison follows Tau Ceti's `TopCat.restrictScalarsCochainMap`, with the relative
chain map in place of `TopCat.restrictScalarsChainMap`, and the cohomology comparison and its
naturality follow `TopCat.singularCohomologyIntChainsIso` and
`TopCat.singularCohomologyIntChainsIso_hom_naturality` of this library, as its values on cocycles
follow `TopCat.map_homologyπ_singularCohomologyIntChainsIso_hom` and
`TopCat.mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsIso_hom_iCycles`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 3.1 and 3.A.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti

namespace TopPair

variable (k : Type) [CommRing k] (P : TopPair.{0})

/-! ### Cochains -/

/-- The comparison of relative cochains: a `k`-linear relative cochain `ψ` of `P`, read as an
element of an abelian group, goes to the integral relative cochain obtained by precomposing `ψ`
with the chain map `SSetPair.intCastChainMap` that casts integral coefficients to
`k`, and identifying the values with the abelian group `k`. -/
def singularCochainComplexIntChainsHom :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)) ⟶
      P.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) where
  f p := ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).obj
      ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).X p))
    { toFun ψ := (SSetPair.intCastChainMap k (toSSetPair.obj P)).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map ψ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom
      -- The identification of the values is additive and `ℤ`-linear, and an integer acts on the
      -- cochains over `k`, with scalars restricted, through its cast to `k`.
      map_add' ψ ψ' := by
        ext x
        exact map_add (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom.hom _ _
      map_smul' r ψ := by
        ext x
        simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, LinearMap.comp_apply,
          LinearMap.smul_apply, RingHom.id_apply]
        erw [ModuleCat.restrictScalarsAlgebraMapIso_hom_apply,
          ModuleCat.restrictScalarsAlgebraMapIso_hom_apply, ModuleCat.restrictScalars.map_apply]
        exact algebraMap_smul k r _ }
  comm' i j _ := by
    ext ψ
    -- Both sides are the cochain `d ≫ θ ≫ F ψ ≫ e`, read through the definitional unfolding of
    -- the differentials of the two cochain complexes.
    have key (ψ' : (P.singularChainComplex (ModuleCat.of k k)).X i ⟶ ModuleCat.of k k) :
        (P.singularChainComplex (ModuleCat.of ℤ (ULift.{0} ℤ))).d j i ≫
            (SSetPair.intCastChainMap k (toSSetPair.obj P)).f i ≫
              (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map ψ' ≫
                (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom =
          (SSetPair.intCastChainMap k (toSSetPair.obj P)).f j ≫
            (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
              ((P.singularChainComplex (ModuleCat.of k k)).d j i ≫ ψ') ≫
                (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom := by
      rw [Functor.map_comp, Category.assoc, ← Category.assoc _ _ (_ ≫ _),
        ← (SSetPair.intCastChainMap k (toSSetPair.obj P)).comm, Functor.mapHomologicalComplex_obj_d,
        Category.assoc]
    exact key ψ

/-- The comparison of relative cochains precomposes a cochain with the chain map casting integral
coefficients to `k`, and identifies the values with the abelian group `k`. -/
theorem singularCochainComplexIntChainsHom_f_apply (p : ℕ)
    (ψ : (P.singularChainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (P.singularCochainComplexIntChainsHom k).f p ψ =
      (SSetPair.intCastChainMap k (toSSetPair.obj P)).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map ψ ≫
          (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom :=
  (rfl)

/-- Read on ambient chains, the comparison of relative cochains is the comparison of cochains of
the ambient space `TopCat.singularCochainComplexIntChainsIso`: precomposing with the quotient map
from ambient to relative integral chains, it takes `ψ` to the comparison of `ψ` precomposed with
the quotient map from ambient to relative chains over `k`. -/
theorem singularChainComplexπ_f_comp_singularCochainComplexIntChainsHom_f (p : ℕ)
    (ψ : (P.singularChainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
    (P.singularChainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫
        (P.singularCochainComplexIntChainsHom k).f p ψ =
      (P.fst.singularCochainComplexIntChainsIso k).hom.f p
        ((P.singularChainComplexπ (ModuleCat.of k k)).f p ≫ ψ) := by
  rw [singularCochainComplexIntChainsHom_f_apply,
    TopCat.singularCochainComplexIntChainsIso_hom_f_apply,
    SSetPair.chainComplexπ_f_intCastChainMap_f_assoc]
  exact congrArg _ (Functor.map_comp_assoc _ _ _ _).symm

variable {P} in
/-- The comparison of relative cochains commutes with the maps induced by a map of pairs. -/
@[reassoc]
theorem singularCochainComplexIntChainsHom_naturality {P' : TopPair.{0}} (f : P ⟶ P') :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
        (singularCochainComplexMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k) f) ≫
      P.singularCochainComplexIntChainsHom k =
    P'.singularCochainComplexIntChainsHom k ≫
      singularCochainComplexMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ k) f := by
  ext p ψ : 3
  -- Both sides apply to `ψ` the maps of the comparison and of `f`, which act on a cochain by
  -- precomposition, the restriction of scalars of a morphism being that morphism.
  have key (ψ' : (P'.singularChainComplex (ModuleCat.of k k)).X p ⟶ ModuleCat.of k k) :
      (SSetPair.intCastChainMap k (toSSetPair.obj P)).f p ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((singularChainComplexMap f (ModuleCat.of k k)).f p ≫ ψ') ≫
            (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom =
      (singularChainComplexMap f (ModuleCat.of ℤ (ULift.{0} ℤ))).f p ≫
        (SSetPair.intCastChainMap k (toSSetPair.obj P')).f p ≫
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map ψ' ≫
            (ModuleCat.restrictScalarsAlgebraMapIso (R := ℤ) (S := k) k).hom := by
    rw [Functor.map_comp, SSetPair.chainComplexMap_f_intCastChainMap_assoc, Category.assoc]
  exact key ψ

/-- The comparison of relative cochains commutes with the maps to the cochains of the ambient
space, followed there by `TopCat.singularCochainComplexIntChainsIso`. -/
@[reassoc]
theorem singularCochainComplexIntChainsHom_comp_linearYonedaFunctor_map :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).map
        ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k k)).map
          (P.singularChainComplexπ (ModuleCat.of k k)).op) ≫
      (P.fst.singularCochainComplexIntChainsIso k).hom =
    P.singularCochainComplexIntChainsHom k ≫
      (ChainComplex.linearYonedaFunctor ℤ (ModuleCat.of ℤ k)).map
        (P.singularChainComplexπ (ModuleCat.of ℤ (ULift.{0} ℤ))).op := by
  ext p ψ : 3
  -- Both sides apply to `ψ` the comparisons and the maps to ambient cochains, which act on a
  -- cochain by precomposition; the restriction of scalars of a morphism is that morphism.
  exact (singularChainComplexπ_f_comp_singularCochainComplexIntChainsHom_f k P p ψ).symm

/-- The comparison of relative cochains is an isomorphism, by the four lemma applied to the
morphism of cochain sequences of the pair given by the comparisons of relative, ambient and
subspace cochains. -/
instance : IsIso (P.singularCochainComplexIntChainsHom k) := by
  let φ : (P.singularCochainComplexShortComplex (ModuleCat.of k k) k (ModuleCat.of k k)).map
        ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _) ⟶
      P.singularCochainComplexShortComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
        (ModuleCat.of ℤ k) :=
    { τ₁ := P.singularCochainComplexIntChainsHom k
      τ₂ := (P.fst.singularCochainComplexIntChainsIso k).hom
      τ₃ := (P.snd.singularCochainComplexIntChainsIso k).hom
      comm₁₂ := (P.singularCochainComplexIntChainsHom_comp_linearYonedaFunctor_map k).symm
      comm₂₃ := (TopCat.singularCochainComplexIntChainsIso_hom_naturality k P.map).symm }
  have hS₁ := (P.shortExact_singularCochainComplexShortComplex (ModuleCat.of k k) k
    (ModuleCat.of k k)).map_of_exact
      ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _)
  have hS₂ := P.shortExact_singularCochainComplexShortComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
    (ModuleCat.of ℤ k)
  have : Epi φ.τ₁ := ShortComplex.epi_of_mono_of_epi_of_mono φ hS₁.exact hS₂.mono_f
    (inferInstanceAs (Epi (P.fst.singularCochainComplexIntChainsIso k).hom))
    (inferInstanceAs (Mono (P.snd.singularCochainComplexIntChainsIso k).hom))
  have := hS₁.mono_f
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (P.fst.singularCochainComplexIntChainsIso k).hom)
  have : Mono φ.τ₁ := mono_of_mono_fac φ.comm₁₂
  exact isIso_of_mono_of_epi φ.τ₁

/-- The comparison of relative cochains is bijective in each degree. -/
theorem bijective_singularCochainComplexIntChainsHom_f (p : ℕ) :
    Function.Bijective ((P.singularCochainComplexIntChainsHom k).f p) :=
  ConcreteCategory.bijective_of_isIso ((P.singularCochainComplexIntChainsHom k).f p)

/-- **Relative cochains over `k` as integral relative cochains**: the `k`-linear relative cochains
`Hom_k(C(X, A; k), k)`, read as abelian groups, are the integral relative cochains
`Hom_ℤ(C(X, A; ℤ), k)`. A cochain `ψ` goes to `ψ` precomposed with the chain map
`SSetPair.intCastChainMap` casting integral coefficients to `k`
(`TopPair.singularCochainComplexIntChainsHom_f_apply`). -/
def singularCochainComplexIntChainsIso :
    ((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplex _).obj
        (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)) ≅
      P.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) :=
  asIso (P.singularCochainComplexIntChainsHom k)

@[simp]
theorem singularCochainComplexIntChainsIso_hom :
    (P.singularCochainComplexIntChainsIso k).hom = P.singularCochainComplexIntChainsHom k :=
  (rfl)

/-! ### Cohomology -/

/-- **Cohomology of a pair over `k` from integral chains**: the singular cohomology of the pair
`P = (X, A)` computed from chains with coefficients in `k`, read as an abelian group, is the
singular cohomology of `P` computed from integral chains with values in `k`. It is the
comparison of the homology of the restricted complex with the restricted homology, followed by
the map induced by the comparison of relative cochains. -/
def singularCohomologyIntChainsIso (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).obj
        (P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) p) ≅
      P.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) p :=
  (((ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).mapHomologicalComplexCompHomologyFunctorIso
      _ p).app (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k))).symm ≪≫
    HomologicalComplex.homologyMapIso (P.singularCochainComplexIntChainsIso k) p

/-- The comparison of cohomologies of a pair is the inverse of the comparison of the restricted
homology with the homology of the restricted complex, followed by the isomorphism induced by the
comparison of relative cochains. -/
theorem singularCohomologyIntChainsIso_def (p : ℕ) :
    P.singularCohomologyIntChainsIso k p =
      ((Functor.mapHomologicalComplexCompHomologyFunctorIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)) _ p).app
          (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k))).symm ≪≫
        HomologicalComplex.homologyMapIso (P.singularCochainComplexIntChainsIso k) p :=
  (rfl)

/-- The comparison of cohomologies of a pair is the comparison of the homology of the restricted
complex with the restricted homology, followed by the map induced by the comparison of relative
cochains. -/
theorem singularCohomologyIntChainsIso_hom (p : ℕ) :
    (P.singularCohomologyIntChainsIso k p).hom =
      (Functor.mapHomologicalComplexCompHomologyFunctorIso
          (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)) _ p).inv.app
          (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)) ≫
        HomologicalComplex.homologyMap (P.singularCochainComplexIntChainsHom k) p := by
  rw [singularCohomologyIntChainsIso_def, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    HomologicalComplex.homologyMapIso_hom, singularCochainComplexIntChainsIso_hom]

variable {P} in
/-- **Naturality**: the comparison of cohomologies of pairs commutes with the maps induced by a
map of pairs. -/
@[reassoc]
theorem singularCohomologyIntChainsIso_hom_naturality {P' : TopPair.{0}} (f : P ⟶ P') (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
        (TopPair.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k)
          f p) ≫
      (P.singularCohomologyIntChainsIso k p).hom =
    (P'.singularCohomologyIntChainsIso k p).hom ≫
      TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
        (M := ModuleCat.of ℤ k) f p := by
  rw [singularCohomologyIntChainsIso_hom, singularCohomologyIntChainsIso_hom, Category.assoc,
    TopPair.singularCohomologyMap, TopPair.singularCohomologyMap,
    ← HomologicalComplex.homologyMap_comp, ← singularCochainComplexIntChainsHom_naturality,
    HomologicalComplex.homologyMap_comp]
  exact (Functor.mapHomologicalComplexCompHomologyFunctorIso
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)) _ p).inv.naturality_assoc
      (singularCochainComplexMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k k) f) _

/-- The comparison of cohomologies of a pair commutes with the maps from relative to absolute
cohomology: sending a class to the cohomology of the ambient space and comparing there by
`TopCat.singularCohomologyIntChainsIso` is comparing first and then sending the class to the
ambient space. -/
@[reassoc]
theorem singularCohomologyπ_singularCohomologyIntChainsIso_hom (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
        (P.singularCohomologyπ (ModuleCat.of k k) k (ModuleCat.of k k) p) ≫
      (P.fst.singularCohomologyIntChainsIso k p).hom =
    (P.singularCohomologyIntChainsIso k p).hom ≫
      P.singularCohomologyπ (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ (ModuleCat.of ℤ k) p := by
  rw [TopCat.singularCohomologyIntChainsIso_hom, singularCohomologyIntChainsIso_hom,
    Category.assoc]
  -- The maps to absolute cohomology are written through the cochain sequence of the pair, whose
  -- terms agree with the cochain complexes only up to unfolding, so the steps are given as terms.
  refine ((Functor.mapHomologicalComplexCompHomologyFunctorIso
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)) _ p).inv.naturality_assoc
      ((ChainComplex.linearYonedaFunctor k (ModuleCat.of k k)).map
        (P.singularChainComplexπ (ModuleCat.of k k)).op) _).trans ?_
  exact congrArg (_ ≫ ·) ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans
    ((congrArg (HomologicalComplex.homologyMap · p)
      (singularCochainComplexIntChainsHom_comp_linearYonedaFunctor_map k P)).trans
        (HomologicalComplex.homologyMap_comp _ _ _)))


/-- The comparison of cohomologies of a pair on the class of a cocycle `ψ` is the class of the
integral cocycle that the comparison of relative cochains gives. -/
@[reassoc, elementwise nosimp]
theorem map_homologyπ_singularCohomologyIntChainsIso_hom (p : ℕ) :
    (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
        ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ p) ≫
      (P.singularCohomologyIntChainsIso k p).hom =
    (((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ≫
      HomologicalComplex.cyclesMap (P.singularCochainComplexIntChainsHom k) p ≫
        (P.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ k)).homologyπ p := by
  rw [singularCohomologyIntChainsIso_hom,
    Functor.map_homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_inv_app_assoc,
    HomologicalComplex.homologyπ_naturality]

/-- On relative cocycles, the comparison of cohomologies of a pair is the comparison of the
underlying relative cochains. -/
@[reassoc, elementwise nosimp]
theorem mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsHom_iCycles (p : ℕ) :
    (((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc p).mapCyclesIso
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ≫
      HomologicalComplex.cyclesMap (P.singularCochainComplexIntChainsHom k) p ≫
        (P.singularCochainComplex (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
          (ModuleCat.of ℤ k)).iCycles p =
      (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles p) ≫
        (P.singularCochainComplexIntChainsHom k).f p := by
  rw [HomologicalComplex.cyclesMap_i, Functor.mapCyclesIso_inv_comp_iCycles_assoc]

/-! ### Pairings with the class of a singular simplex -/

/-- **Integral and `k`-linear pairings on the class of a singular simplex.** For a class
`c ∈ Hᵖ⁺¹(X, A; k)` and a singular `(p + 1)`-simplex `s` of `X` whose faces lie in `A`, the
class `c` read through integral chains (`TopPair.singularCohomologyIntChainsIso`) evaluates on the
integral class of `s` to what `c` evaluates to on the class of `s` with coefficients in `k`. -/
theorem singularKronecker_singularCohomologyIntChainsIso_hom_relClass {p : ℕ}
    (c : P.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) (p + 1))
    (s : (TopCat.toSSet.obj P.fst) _⦋p + 1⦌)
    (h : ∀ i, Set.range (P.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj P.fst).δ i s)) ⊆
      Set.range P.map) :
    (P.singularKronecker ℤ (p + 1) ((P.singularCohomologyIntChainsIso k (p + 1)).hom c)).hom
        ((P.relClass (ModuleCat.of ℤ (ULift.{0} ℤ)) s h).hom 1) =
      (P.singularKronecker k (p + 1) c).hom ((P.relClass (ModuleCat.of k k) s h).hom 1) := by
  -- A cocycle `ψ` representing `c`, taken in the restricted cycles.
  obtain ⟨ψ, rfl⟩ : ∃ ψ, (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
      ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).homologyπ (p + 1)) ψ =
        c :=
    HomologicalComplex.moduleCat_homologyπ_surjective _ (p + 1) c
  rw [map_homologyπ_singularCohomologyIntChainsIso_hom_apply]
  -- Both pairings are cocycles evaluated on the relative chain of `s`.
  have hℤ := ConcreteCategory.congr_hom (P.relClass_comp_singularKronecker_homologyπ
    (ModuleCat.of ℤ (ULift.{0} ℤ)) s h ℤ (HomologicalComplex.cyclesMap
      (P.singularCochainComplexIntChainsHom k) (p + 1)
        ((((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).sc
          (p + 1)).mapCyclesIso (ModuleCat.restrictScalars.{0} (algebraMap ℤ k))).inv ψ))) 1
  have hk := ConcreteCategory.congr_hom
    (P.relClass_comp_singularKronecker_homologyπ (ModuleCat.of k k) s h k ψ) 1
  rw [ConcreteCategory.comp_apply] at hℤ hk
  rw [hℤ]
  refine Eq.trans ?_ hk.symm
  rw [mapCyclesIso_inv_cyclesMap_singularCochainComplexIntChainsHom_iCycles_apply]
  -- On ambient chains the comparison is that of `X`, which casts the coefficient `1` to `k`.
  have h₁ := ConcreteCategory.congr_hom
    (P.singularChainComplexπ_f_comp_singularCochainComplexIntChainsHom_f k (p + 1)
      ((P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles (p + 1) ψ))
    ((TopCat.toSSet.obj P.fst).ιChainComplex (R := ModuleCat.of ℤ (ULift.{0} ℤ)) s 1)
  have h₂ := TopCat.singularCochainComplexIntChainsIso_hom_f_apply_ιChainComplex k P.fst s
    ((P.singularChainComplexπ (ModuleCat.of k k)).f (p + 1) ≫
      (P.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k k)).iCycles (p + 1) ψ) 1
  rw [ULift.one_down, Int.cast_one, one_mul] at h₂
  exact h₁.trans h₂

end TopPair

end
