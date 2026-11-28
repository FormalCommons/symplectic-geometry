/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.RelativeClass
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Relative.RestrictScalars

/-!
# Relative classes of singular simplices

For a topological pair `P = (X, A)` and a singular `(n + 1)`-simplex `σ` of `X` each of whose
faces has its image in `A`, this file defines the class `TopPair.relClass R P σ hσ` of `σ` in the
relative singular homology `Hₙ₊₁(X, A; R)`: the class `SSetPair.relClass` of `σ` in the singular
pair of `P`, its faces lifted to singular simplices of `A` (`TopPair.liftSimplex`). For the pair
`TopPair.ofSubset Sᶜ` of a subset `S` of a space `M`, its target is `TauCeti.localHomology R S`.

## Main definitions and results

* `TopPair.relClass`: the class of a singular simplex whose faces lie in the subspace.
* `TopPair.relClass_eq`: the class is `SSetPair.relClass` for any lifts of the faces.
* `TopPair.range_toSSetObjEquiv_δ_subset_of_eq_toSSet_map_app`: lifts of the faces to the subspace
  give the face condition, and `TopPair.relClass_eq_of_eq_toSSet_map_app` is the class for them.
* `TopPair.relClass_singularHomologyMap`: naturality in maps of pairs; for the identity map
  `(X, B) ⟶ (X, B')` with `B ⊆ B'`, `TopPair.relClass_singularHomologyMap_ofSubsetMap_id`.
* `TopPair.relClass_restrictScalarsHomologyMap`: the change of coefficients
  `SSetPair.restrictScalarsHomologyMap` along `g : M ⟶ f^* N` sends the class with coefficients
  in `M` to the class with coefficients in `N`, through `g`; for the cast of integers into a
  ring `k`, `TopPair.relClass_intCastHomologyMap`.
* `TopPair.relClass_localHomologyRestriction`: compatibility with the restriction
  `Hₙ₊₁(M, M ∖ T) ⟶ Hₙ₊₁(M, M ∖ S)` for `S ⊆ T`.
* `TopPair.relClass_localHomologyMap`: naturality in continuous maps, on local homology.
* `TopPair.relClass_singularHomologyδ`: the connecting morphism of the pair sends the class to that
  of the cycle `∑ i, (-1) ^ i • t i` of `A`, where the `t i` lift the faces of `σ`; for a singular
  `2`-simplex, to that of `t 0 - t 1 + t 2` (`TopPair.relClass_singularHomologyδ_two`).
* `TopPair.relClass_comp_singularKronecker_homologyπ`: the Kronecker pairing of the class of a
  relative cocycle with the class of the simplex is the cocycle evaluated on the simplex.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, relative
  homology groups and the long exact sequence of a pair.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace TopPair

variable (P : TopPair.{w})

/-- A singular simplex of the ambient space of a pair whose image lies in the subspace, as a
singular simplex of the subspace. -/
def liftSimplex {m : ℕ} (x : (TopCat.toSSet.obj P.fst) _⦋m⦌)
    (hx : Set.range (P.fst.toSSetObjEquiv _ x) ⊆ Set.range P.map) :
    (TopCat.toSSet.obj P.snd) _⦋m⦌ :=
  ((P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ x).2 hx).choose

/-- The lift of a singular simplex to the subspace is carried back to it by the inclusion. -/
@[simp]
lemma toSSet_map_app_liftSimplex {m : ℕ} (x : (TopCat.toSSet.obj P.fst) _⦋m⦌)
    (hx : Set.range (P.fst.toSSetObjEquiv _ x) ⊆ Set.range P.map) :
    (TopCat.toSSet.map P.map).app _ (P.liftSimplex x hx) = x :=
  ((P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ x).2 hx).choose_spec

/-- The lift of a singular simplex to the subspace is the only singular simplex of the subspace
that the inclusion carries to it. -/
lemma liftSimplex_eq_iff {m : ℕ} (x : (TopCat.toSSet.obj P.fst) _⦋m⦌)
    (hx : Set.range (P.fst.toSSetObjEquiv _ x) ⊆ Set.range P.map)
    (y : (TopCat.toSSet.obj P.snd) _⦋m⦌) :
    P.liftSimplex x hx = y ↔ (TopCat.toSSet.map P.map).app _ y = x := by
  have hinj : Function.Injective ((TopCat.toSSet.map P.map).app (Opposite.op ⦋m⦌)) :=
    (mono_iff_injective _).1 inferInstance
  rw [← hinj.eq_iff, toSSet_map_app_liftSimplex, eq_comm]

/-- If the faces of a singular `(n + 1)`-simplex `σ` of the ambient space are the images of
singular simplices `t i` of the subspace, then each face of `σ` has its image in the subspace. -/
lemma range_toSSetObjEquiv_δ_subset_of_eq_toSSet_map_app {n : ℕ}
    (σ : (TopCat.toSSet.obj P.fst) _⦋n + 1⦌) (t : Fin (n + 2) → (TopCat.toSSet.obj P.snd) _⦋n⦌)
    (ht : ∀ i, (TopCat.toSSet.obj P.fst).δ i σ = (TopCat.toSSet.map P.map).app _ (t i))
    (i : Fin (n + 2)) :
    Set.range (P.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj P.fst).δ i σ)) ⊆ Set.range P.map :=
  (P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff _ _).1 ⟨t i, (ht i).symm⟩

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C) {n : ℕ} (σ : (TopCat.toSSet.obj P.fst) _⦋n + 1⦌)
  (hσ : ∀ i, Set.range (P.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj P.fst).δ i σ)) ⊆
    Set.range P.map)

/-- The class in `Hₙ₊₁(X, A; R)` of a singular `(n + 1)`-simplex `σ` of `X` whose faces have
their images in `A`. -/
def relClass : R ⟶ P.singularHomology R (n + 1) :=
  SSetPair.relClass (Q := toSSetPair.obj P) R σ (fun i ↦ P.liftSimplex _ (hσ i))
    (fun i ↦ (P.toSSet_map_app_liftSimplex _ (hσ i)).symm)

/-- The class of a singular simplex is `SSetPair.relClass` for the lifts of its faces. -/
lemma relClass_def :
    P.relClass R σ hσ =
      SSetPair.relClass (Q := toSSetPair.obj P) R σ (fun i ↦ P.liftSimplex _ (hσ i))
        (fun i ↦ (P.toSSet_map_app_liftSimplex _ (hσ i)).symm) :=
  (rfl)

/-- The class of a singular simplex is `SSetPair.relClass` for any singular simplices `t i` of
the subspace that the inclusion carries to the faces of `σ`. -/
lemma relClass_eq (t : Fin (n + 2) → (TopCat.toSSet.obj P.snd) _⦋n⦌)
    (ht : ∀ i, (TopCat.toSSet.obj P.fst).δ i σ = (TopCat.toSSet.map P.map).app _ (t i)) :
    P.relClass R σ hσ = SSetPair.relClass (Q := toSSetPair.obj P) R σ t ht := by
  obtain rfl : (fun i ↦ P.liftSimplex _ (hσ i)) = t :=
    funext fun i ↦ (P.liftSimplex_eq_iff _ (hσ i) (t i)).2 (ht i).symm
  rw [relClass_def]

/-- The class of a singular simplex `σ` whose faces are the images of singular simplices `t i` of
the subspace is `SSetPair.relClass` for these `t i`; the face condition that `relClass` asks for
is `range_toSSetObjEquiv_δ_subset_of_eq_toSSet_map_app`. -/
lemma relClass_eq_of_eq_toSSet_map_app (t : Fin (n + 2) → (TopCat.toSSet.obj P.snd) _⦋n⦌)
    (ht : ∀ i, (TopCat.toSSet.obj P.fst).δ i σ = (TopCat.toSSet.map P.map).app _ (t i)) :
    P.relClass R σ (P.range_toSSetObjEquiv_δ_subset_of_eq_toSSet_map_app σ t ht) =
      SSetPair.relClass (Q := toSSetPair.obj P) R σ t ht :=
  P.relClass_eq R σ _ t ht

variable {P}

include hσ in
/-- A map of pairs carries a singular simplex whose faces lie in the subspace to one whose faces
lie in the subspace. -/
lemma range_toSSetObjEquiv_δ_toSSet_map_app_subset {P' : TopPair.{w}} (f : P ⟶ P')
    (i : Fin (n + 2)) :
    Set.range (P'.fst.toSSetObjEquiv _
        ((TopCat.toSSet.obj P'.fst).δ i ((TopCat.toSSet.map (Hom.fst f)).app _ σ))) ⊆
      Set.range P'.map := by
  exact P'.range_toSSetObjEquiv_δ_subset_of_eq_toSSet_map_app _
    (fun j ↦ (TopCat.toSSet.map (Hom.snd f)).app _ (P.liftSimplex _ (hσ j)))
    (fun j ↦ SSetPair.δ_app_right_eq_hom_app (Q := toSSetPair.obj P) (toSSetPair.map f) σ j _
      (P.toSSet_map_app_liftSimplex _ (hσ j)).symm) i

/-- **Naturality of the class of a singular simplex** in maps of pairs. -/
@[reassoc (attr := simp)]
lemma relClass_singularHomologyMap {P' : TopPair.{w}} (f : P ⟶ P') :
    P.relClass R σ hσ ≫ TopPair.singularHomologyMap f R (n + 1) =
      P'.relClass R ((TopCat.toSSet.map (Hom.fst f)).app _ σ)
        (range_toSSetObjEquiv_δ_toSSet_map_app_subset σ hσ f) := by
  rw [relClass_def]
  -- `σ` is a simplex of `(toSSetPair.obj P).right`, which is `TopCat.toSSet.obj P.fst` only up to
  -- unfolding `toSSetPair`, so the naturality of `SSetPair.relClass` is applied as a term.
  exact (SSetPair.relClass_homologyMap (Q := toSSetPair.obj P) R σ _ _ (toSSetPair.map f)).trans
    (relClass_eq _ _ _ _ _ _).symm

/-- For `B ⊆ B'`, the identity map of pairs `(X, B) ⟶ (X, B')` carries the class in
`Hₙ₊₁(X, B)` of a singular simplex whose faces lie in `B` to its class in `Hₙ₊₁(X, B')`. -/
@[reassoc (attr := simp), elementwise]
lemma relClass_singularHomologyMap_ofSubsetMap_id {X : TopCat.{w}} {B B' : Set X}
    (h : Set.MapsTo (𝟙 X) B B') (σ : (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (hσ : ∀ i, Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)) ⊆
      Set.range (ofSubset B).map) :
    (ofSubset B).relClass R σ hσ ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) h) R (n + 1) =
      (ofSubset B').relClass R σ fun i ↦ (hσ i).trans <| (range_ofSubset_map (B := B)).trans_subset
        fun x hx ↦ (range_ofSubset_map (B := B')).symm ▸ h hx := by
  refine (relClass_singularHomologyMap (P := ofSubset B) R σ hσ (ofSubsetMap (𝟙 X) h)).trans ?_
  congr 1
  -- `ofSubsetMap_fst` cannot be rewritten in place: the `MapsTo` proof depends on the map.
  have e : TopCat.toSSet.map (Hom.fst (ofSubsetMap (𝟙 X) h)) = 𝟙 _ :=
    (congrArg TopCat.toSSet.map (ofSubsetMap_fst _ _)).trans (CategoryTheory.Functor.map_id _ _)
  rw [e, NatTrans.id_app]
  exact ConcreteCategory.id_apply _

/-- The change of coefficients `SSetPair.restrictScalarsHomologyMap` along `g : M ⟶ f^* N` sends
the class of a singular `(n + 1)`-simplex `σ` whose faces lie in the subspace, with coefficients
in `M`, to the class of `σ` with coefficients in `N`, through `g` on coefficients. -/
@[reassoc]
lemma relClass_restrictScalarsHomologyMap {R S : Type w} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{w} R} {N : ModuleCat.{w} S} (g : M ⟶ (ModuleCat.restrictScalars f).obj N) :
    P.relClass M σ hσ ≫ SSetPair.restrictScalarsHomologyMap f g (toSSetPair.obj P) (n + 1) =
      g ≫ (ModuleCat.restrictScalars f).map (P.relClass N σ hσ) := by
  rw [relClass_def, relClass_def]
  -- `σ` is a simplex of `(toSSetPair.obj P).right`, which is `TopCat.toSSet.obj P.fst` only up to
  -- unfolding `toSSetPair`, so the lemma for pairs of simplicial sets is applied as a term.
  exact SSetPair.relClass_restrictScalarsHomologyMap f g (P := toSSetPair.obj P) σ _ _

/-- Casting integral relative homology to `k` (`SSetPair.intCastHomologyMap`) sends the integral
class of a singular `(n + 1)`-simplex `σ` whose faces lie in the subspace to the class of `σ`
over `k`, through the cast of integers to `k` on coefficients. -/
@[reassoc]
lemma relClass_intCastHomologyMap {k : Type} [Ring k] {Q : TopPair.{0}} {m : ℕ}
    (s : (TopCat.toSSet.obj Q.fst) _⦋m + 1⦌)
    (hs : ∀ i, Set.range (Q.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj Q.fst).δ i s)) ⊆
      Set.range Q.map) :
    Q.relClass (ModuleCat.of ℤ (ULift.{0} ℤ)) s hs ≫
        SSetPair.intCastHomologyMap k (toSSetPair.obj Q) (m + 1) =
      ModuleCat.uliftUnitToRestrictScalars (algebraMap ℤ k) ≫
        (ModuleCat.restrictScalars.{0} (algebraMap ℤ k)).map
          (Q.relClass (ModuleCat.of k k) s hs) := by
  rw [SSetPair.intCastHomologyMap_def, relClass_restrictScalarsHomologyMap]

section Abelian

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A) {n : ℕ}

variable (P) (σ : (TopCat.toSSet.obj P.fst) _⦋n + 1⦌)
  (hσ : ∀ i, Set.range (P.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj P.fst).δ i σ)) ⊆
    Set.range P.map)
  (t : Fin (n + 2) → (TopCat.toSSet.obj P.snd) _⦋n⦌)
  (ht : ∀ i, (TopCat.toSSet.obj P.fst).δ i σ = (TopCat.toSSet.map P.map).app _ (t i))

/-- **The connecting morphism on the class of a singular simplex** is the class of the cycle
`∑ i, (-1) ^ i • t i` of the subspace, for singular simplices `t i` of the subspace that the
inclusion carries to the faces of `σ`. -/
@[reassoc]
lemma relClass_singularHomologyδ (k : ℕ) (hk : (ComplexShape.down ℕ).next n = k) :
    P.relClass R σ hσ ≫ P.singularHomologyδ R (n + 1) n =
      ((TopCat.toSSet.obj P.snd).chainComplex R).liftCycles
          (∑ i, (-1 : ℤ) ^ i.val • (TopCat.toSSet.obj P.snd).ιChainComplex (t i)) k hk
          (SSetPair.sum_ιChainComplex_comp_d (Q := toSSetPair.obj P) R σ t ht k) ≫
        ((TopCat.toSSet.obj P.snd).chainComplex R).homologyπ n := by
  rw [P.relClass_eq R σ hσ t ht]
  exact SSetPair.relClass_homologyδ (Q := toSSetPair.obj P) R σ t ht k hk

/-- **The connecting morphism on the class of a singular `2`-simplex** is the class of the cycle
`t 0 - t 1 + t 2` of the subspace, for singular `1`-simplices `t i` of the subspace that the
inclusion carries to the three edges of `σ`. -/
@[reassoc]
lemma relClass_singularHomologyδ_two (σ : (TopCat.toSSet.obj P.fst) _⦋2⦌)
    (hσ : ∀ i, Set.range (P.fst.toSSetObjEquiv _ ((TopCat.toSSet.obj P.fst).δ i σ)) ⊆
      Set.range P.map)
    (t : Fin 3 → (TopCat.toSSet.obj P.snd) _⦋1⦌)
    (ht : ∀ i, (TopCat.toSSet.obj P.fst).δ i σ = (TopCat.toSSet.map P.map).app _ (t i)) :
    P.relClass R σ hσ ≫ P.singularHomologyδ R 2 1 =
      ((TopCat.toSSet.obj P.snd).chainComplex R).liftCycles
          ((TopCat.toSSet.obj P.snd).ιChainComplex (R := R) (t 0) -
            (TopCat.toSSet.obj P.snd).ιChainComplex (R := R) (t 1) +
            (TopCat.toSSet.obj P.snd).ιChainComplex (R := R) (t 2))
          0 (by simp)
          (SSetPair.ιChainComplex_sub_add_comp_d (Q := toSSetPair.obj P) R σ t ht 0) ≫
        ((TopCat.toSSet.obj P.snd).chainComplex R).homologyπ 1 := by
  rw [P.relClass_eq R σ hσ t ht]
  exact SSetPair.relClass_homologyδ_two (Q := toSSetPair.obj P) R σ t ht

/-- **The Kronecker pairing on the class of a singular simplex**: a relative class represented by
a cocycle `φ` evaluates on the class of `σ` to `φ` evaluated on the relative chain of `σ`. -/
@[reassoc]
lemma relClass_comp_singularKronecker_homologyπ {M : A} (k : Type*) [Ring k] [Linear k A]
    (φ : (P.singularCochainComplex R k M).cycles (n + 1)) :
    P.relClass R σ hσ ≫
        P.singularKronecker k (n + 1) ((P.singularCochainComplex R k M).homologyπ (n + 1) φ) =
      (TopCat.toSSet.obj P.fst).ιChainComplex σ ≫ (P.singularChainComplexπ R).f (n + 1) ≫
        (P.singularCochainComplex R k M).iCycles (n + 1) φ := by
  rw [relClass_def]
  -- `σ` is a simplex of `(toSSetPair.obj P).right`, which is `TopCat.toSSet.obj P.fst` only up to
  -- unfolding `toSSetPair`, so `SSetPair.relClass_def` and `liftCycles_i` are applied as terms.
  refine (congrArg (· ≫ _) (SSetPair.relClass_def (Q := toSSetPair.obj P) R σ _ _)).trans ?_
  rw [Category.assoc, singularKronecker_homologyπ]
  exact (HomologicalComplex.liftCycles_i_assoc _ _ _ _ _ _).trans (Category.assoc _ _ _)

/-- For `S ⊆ T`, the complement of `T` lies in the complement of `S`, as ranges of the
inclusions of the pairs `(M, M ∖ T)` and `(M, M ∖ S)`. -/
lemma range_map_ofSubset_compl_subset {M : Type w} [TopologicalSpace M] {S T : Set M}
    (h : S ⊆ T) :
    Set.range (ofSubset (Tᶜ : Set (TopCat.of M))).map ⊆
      Set.range (ofSubset (Sᶜ : Set (TopCat.of M))).map := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.val, Set.compl_subset_compl.2 h x.prop⟩, rfl⟩

/-- **The class of a singular simplex in local homology** is compatible with the restriction
`Hₙ₊₁(M, M ∖ T) ⟶ Hₙ₊₁(M, M ∖ S)` for `S ⊆ T`: a simplex whose faces avoid `T` has faces
avoiding `S`. -/
@[reassoc (attr := simp)]
lemma relClass_localHomologyRestriction {M : Type w} [TopologicalSpace M] {S T : Set M}
    (h : S ⊆ T) (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋n + 1⦌)
    (hσ : ∀ i, Set.range ((TopCat.of M).toSSetObjEquiv _ ((TopCat.toSSet.obj _).δ i σ)) ⊆
      Set.range (ofSubset (Tᶜ : Set (TopCat.of M))).map) :
    (ofSubset (Tᶜ : Set (TopCat.of M))).relClass R σ hσ ≫
        TauCeti.localHomologyRestriction R h (n + 1) =
      (ofSubset (Sᶜ : Set (TopCat.of M))).relClass R σ fun i ↦
        (hσ i).trans (range_map_ofSubset_compl_subset h) := by
  rw [TauCeti.localHomologyRestriction_def]
  have := relClass_singularHomologyMap (P := ofSubset (Tᶜ : Set (TopCat.of M))) R σ hσ
    (ofSubsetMap (𝟙 (TopCat.of M)) (Set.compl_subset_compl.2 h))
  refine this.trans ?_
  congr 1
  -- `ofSubsetMap_fst` cannot be rewritten in place: the `MapsTo` proof depends on the map.
  have e : TopCat.toSSet.map (Hom.fst (ofSubsetMap (𝟙 (TopCat.of M))
      (Set.compl_subset_compl.2 h))) = 𝟙 _ :=
    (congrArg TopCat.toSSet.map (ofSubsetMap_fst _ _)).trans (CategoryTheory.Functor.map_id _ _)
  rw [e, NatTrans.id_app]
  exact ConcreteCategory.id_apply _

/-- For a continuous map `j : M → N` and `S ⊆ j ⁻¹' T`, a singular simplex of `M` whose image
under `j` has its faces in `N ∖ T` has its faces in `M ∖ S`. -/
lemma range_toSSetObjEquiv_δ_subset_of_toSSet_map_app {M N : Type w} [TopologicalSpace M]
    [TopologicalSpace N] (j : C(M, N)) {S : Set M} {T : Set N} (h : S ⊆ j ⁻¹' T)
    (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋n + 1⦌)
    (hσ : ∀ i, Set.range ((TopCat.of N).toSSetObjEquiv _
      ((TopCat.toSSet.obj _).δ i ((TopCat.toSSet.map (TopCat.ofHom j)).app _ σ))) ⊆
        Set.range (ofSubset (Tᶜ : Set (TopCat.of N))).map) (i : Fin (n + 2)) :
    Set.range ((TopCat.of M).toSSetObjEquiv _ ((TopCat.toSSet.obj _).δ i σ)) ⊆
      Set.range (ofSubset (Sᶜ : Set (TopCat.of M))).map := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨y, hy⟩, hyz⟩ := hσ i ⟨z, rfl⟩
  -- The inclusion of `N ∖ T` sends `⟨y, hy⟩` to `y`, so `hyz` says that `y` is `j` of the point.
  exact ⟨⟨_, fun hS ↦ hy ((show y = _ from hyz) ▸ h hS)⟩, rfl⟩

/-- **The class of a singular simplex in local homology is natural**: for a continuous map
`j : M → N` with `j ⁻¹' T ⊆ S`, the map `Hₙ₊₁(M, M ∖ S) ⟶ Hₙ₊₁(N, N ∖ T)` induced by `j` carries
the class of a simplex `σ` whose faces avoid `S` to the class of its image `τ`. -/
@[reassoc, elementwise]
lemma relClass_localHomologyMap {M N : Type w} [TopologicalSpace M] [TopologicalSpace N]
    (j : C(M, N)) {S : Set M} {T : Set N} (h : j ⁻¹' T ⊆ S)
    (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋n + 1⦌)
    (hσ : ∀ i, Set.range ((TopCat.of M).toSSetObjEquiv _ ((TopCat.toSSet.obj _).δ i σ)) ⊆
      Set.range (ofSubset (Sᶜ : Set (TopCat.of M))).map)
    {τ : (TopCat.toSSet.obj (TopCat.of N)) _⦋n + 1⦌}
    (hτ : ∀ i, Set.range ((TopCat.of N).toSSetObjEquiv _ ((TopCat.toSSet.obj _).δ i τ)) ⊆
      Set.range (ofSubset (Tᶜ : Set (TopCat.of N))).map)
    (hστ : (TopCat.toSSet.map (TopCat.ofHom j)).app _ σ = τ) :
    (ofSubset (Sᶜ : Set (TopCat.of M))).relClass R σ hσ ≫
        TauCeti.localHomologyMap R j h (n + 1) =
      (ofSubset (Tᶜ : Set (TopCat.of N))).relClass R τ hτ := by
  subst hστ
  rw [TauCeti.localHomologyMap_def]
  refine (relClass_singularHomologyMap (P := ofSubset (Sᶜ : Set (TopCat.of M))) R σ hσ _).trans ?_
  congr 1
  -- After the rewrite the two sides agree up to unfolding the source `(ofSubset Sᶜ).fst` of the
  -- map of pairs, which is `TopCat.of M`.
  rw [ofSubsetMap_fst]
  rfl

end Abelian

end TopPair

end
