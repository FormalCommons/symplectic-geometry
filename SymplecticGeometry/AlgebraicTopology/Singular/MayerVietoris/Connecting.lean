/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
public import SymplecticGeometry.AlgebraicTopology.Singular.PairMap

/-!
# The Mayer–Vietoris connecting morphism through the connecting morphism of a pair

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`. The Mayer–Vietoris connecting
morphism `TopCat.mayerVietorisδ : Hₙ(X) ⟶ Hₘ(U ∩ V)`, `m + 1 = n`, is the composite of the map
`Hₙ(X) ⟶ Hₙ(X, V)`, of the inverse of the excision isomorphism `Hₙ(U, U ∩ V) ≅ Hₙ(X, V)`, of the
connecting morphism of the pair `(U, U ∩ V)` and of the map induced by the homeomorphism
`TopPair.interPairSndHomeomorph U V` from the preimage of `V` in `U` onto `U ∩ V`
(`TopCat.mayerVietorisδ_eq_singularHomologyδ_left`). The same composite with the
roles of `U` and `V` exchanged is its negative
(`TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right`). The signs come from Tau Ceti's
convention that the first map of the sequence is `(i_U, -i_V)`: a cycle of `X` written as `x + y`,
with `x` a chain in `U` and `y` a chain in `V`, is sent to the class of `∂x = -∂y`, and the pairs
`(U, U ∩ V)` and `(V, U ∩ V)` send it to the classes of `∂x` and of `∂y`.

Both come from a statement about simplicial sets. For a pushout square of simplicial sets with
top map `t : X₁ ⟶ X₂`, a map of short exact sequences of chain complexes from the Mayer–Vietoris
sequence to the sequence of a pair, which is the projection to the chains of `X₂` (or `X₃`) in the
middle, commutes with the connecting morphisms (`SSet.mayerVietorisδ_comp_homologyMap_of_fst`,
`SSet.mayerVietorisδ_comp_homologyMap_of_snd`), by the naturality of connecting morphisms.

In positive degrees the same holds for the reduced connecting morphism
`TopCat.reducedMayerVietorisδ` (`TopCat.reducedMayerVietorisδ_succ_eq_singularHomologyδ_left`).

The two pieces fit together: the image of a class `c` of `Hₙ(X)` in `Hₙ(X, U ∩ V)` is the sum of
the images of the excision preimages `a ∈ Hₙ(U, U ∩ V)` of the image of `c` in `Hₙ(X, V)` and
`a' ∈ Hₙ(V, V ∩ U)` of its image in `Hₙ(X, U)` (`TopCat.singularHomologyπ_ofSubset_inter_eq_add`).
By Tau Ceti's `TopPair.singularHomology_inter_hom_ext`, it is enough to compare the images of
both sides in `Hₙ(X, U)` and in `Hₙ(X, V)`. There one summand gives back the excision map, which
cancels against its inverse (`TopPair.inv_singularHomologyMap_excisionMap_comp_ofSubsetMap_id`),
and the other vanishes, as `(U, U ∩ V) ⟶ (X, U)` factors through `(U, U)`
(`TopPair.singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset`). These lemmas on maps of
pairs, and `TopPair.interPairSndHomeomorph`, are in `Singular/PairMap.lean`.

## Main results

* `SSet.mayerVietorisδ_comp_homologyMap_of_fst`, `SSet.mayerVietorisδ_comp_homologyMap_of_snd`:
  the Mayer–Vietoris connecting morphism of a pushout square of simplicial sets and that of a pair.
* `TopCat.mayerVietorisδ_eq_singularHomologyδ_left`: the Mayer–Vietoris connecting morphism of an
  open cover through the pair `(U, U ∩ V)`.
* `TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right`: the same through the pair `(V, U ∩ V)`,
  with a sign.
* `TopCat.reducedMayerVietorisδ_succ_eq_singularHomologyδ_left`: the reduced form in positive
  degrees.
* `TopCat.singularHomologyπ_ofSubset_inter_eq_add`: the image of an absolute class relative to
  `U ∩ V`, as the sum of the images of its two excision preimages.
* `TopCat.chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ_eq` and its
  neighbour: the images of the chains of a member of the cover, as small chains, in relative
  chains; with `TopPair.homologyMap_eq_singularHomologyπ_comp_inv` they give the excision
  composite on homology.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2: the
  Mayer–Vietoris sequence, and its derivation from excision and the long exact sequence of a pair.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
  (sq : IsPushout t l r b) [Mono t] (P : SSetPair.{w})

/-- **The Mayer–Vietoris connecting morphism and the connecting morphism of a pair**, through the
first piece. Let `P` be a pair of simplicial sets, `φ : X₁ ⟶ P.left` and `ψ : X₂ ⟶ P.right` with
`φ ≫ P.hom = t ≫ ψ`, and `g` a chain map from `C(X₄)` to the relative chains of `P` that agrees
with `ψ` on `C(X₂)` and vanishes on `C(X₃)`. Then the Mayer–Vietoris connecting morphism followed
by `φ` is the map induced by `g` followed by the connecting morphism of `P`. -/
lemma mayerVietorisδ_comp_homologyMap_of_fst (φ : X₁ ⟶ P.left) (ψ : X₂ ⟶ P.right)
    (hφψ : φ ≫ P.hom = t ≫ ψ) (g : X₄.chainComplex R ⟶ P.chainComplex R)
    (hr : chainComplexMap r R ≫ g = chainComplexMap ψ R ≫ P.chainComplexπ R)
    (hb : chainComplexMap b R ≫ g = 0) (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ SSet.homologyMap φ R m =
      HomologicalComplex.homologyMap g n ≫ P.homologyδ R n m h := by
  rw [mayerVietorisδ_def R sq n m h, SSetPair.homologyδ]
  exact HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := (sq.map ((chainComplexFunctor C).obj R)).shortComplex)
    (S₂ := P.chainComplexShortComplex R)
    { τ₁ := chainComplexMap φ R
      τ₂ := biprod.fst ≫ chainComplexMap ψ R
      τ₃ := g
      comm₁₂ := by
        -- Unfold the `f` maps of both short complexes, to check the square through `biprod.lift`.
        change chainComplexMap φ R ≫ chainComplexMap P.hom R =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫ biprod.fst ≫
            chainComplexMap ψ R
        rw [biprod.lift_fst_assoc, ← Functor.map_comp, ← Functor.map_comp, hφψ]
      comm₂₃ := by
        -- Unfold the `g` maps of both short complexes, to check the square on both biproduct
        -- inclusions.
        change (biprod.fst ≫ chainComplexMap ψ R) ≫ P.chainComplexπ R =
          biprod.desc (chainComplexMap r R) (chainComplexMap b R) ≫ g
        apply biprod.hom_ext' <;> simp [hr, hb] }
    (shortExact_mayerVietorisShortComplex R sq) (P.shortExact_chainComplexShortComplex R) n m h

/-- **The Mayer–Vietoris connecting morphism and the connecting morphism of a pair**, through the
second piece. Let `P` be a pair of simplicial sets, `φ : X₁ ⟶ P.left` and `ψ : X₃ ⟶ P.right` with
`φ ≫ P.hom = l ≫ ψ`, and `g` a chain map from `C(X₄)` to the relative chains of `P` that vanishes
on `C(X₂)` and agrees with `ψ` on `C(X₃)`. Then the Mayer–Vietoris connecting morphism followed
by `φ` is the negative of the map induced by `g` followed by the connecting morphism of `P`. -/
lemma mayerVietorisδ_comp_homologyMap_of_snd (φ : X₁ ⟶ P.left) (ψ : X₃ ⟶ P.right)
    (hφψ : φ ≫ P.hom = l ≫ ψ) (g : X₄.chainComplex R ⟶ P.chainComplex R)
    (hr : chainComplexMap r R ≫ g = 0)
    (hb : chainComplexMap b R ≫ g = chainComplexMap ψ R ≫ P.chainComplexπ R)
    (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq n m h ≫ SSet.homologyMap φ R m =
      -(HomologicalComplex.homologyMap g n ≫ P.homologyδ R n m h) := by
  have := HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := (sq.map ((chainComplexFunctor C).obj R)).shortComplex)
    (S₂ := P.chainComplexShortComplex R)
    { τ₁ := -chainComplexMap φ R
      τ₂ := biprod.snd ≫ chainComplexMap ψ R
      τ₃ := g
      comm₁₂ := by
        -- Unfold the `f` maps of both short complexes, to check the square through `biprod.lift`.
        change (-chainComplexMap φ R) ≫ chainComplexMap P.hom R =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫ biprod.snd ≫
            chainComplexMap ψ R
        rw [biprod.lift_snd_assoc, Preadditive.neg_comp, Preadditive.neg_comp,
          ← Functor.map_comp, ← Functor.map_comp, hφψ]
      comm₂₃ := by
        -- Unfold the `g` maps of both short complexes, to check the square on both biproduct
        -- inclusions.
        change (biprod.snd ≫ chainComplexMap ψ R) ≫ P.chainComplexπ R =
          biprod.desc (chainComplexMap r R) (chainComplexMap b R) ≫ g
        apply biprod.hom_ext' <;> simp [hr, hb] }
    (shortExact_mayerVietorisShortComplex R sq) (P.shortExact_chainComplexShortComplex R) n m h
  rw [mayerVietorisδ_def R sq n m h, SSetPair.homologyδ, ← this, HomologicalComplex.homologyMap_neg,
    Preadditive.comp_neg, neg_neg]

end SSet

namespace TopCat

section Small

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {ι : Type*} (𝒰 : ι → Set X) {i : ι}

/-- The chains of a member `B` of the family `𝒰`, as small chains of `X`, vanish in the relative
chains of the pair `(X, B)`. -/
lemma chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ {B : Set X}
    (h : B ⊆ 𝒰 i) :
    SSet.chainComplexMap (toSmallSingularSubcomplex 𝒰 h) R ≫
      SSet.chainComplexMap (X.smallSingularSubcomplex 𝒰).ι R ≫
        (TopPair.ofSubset B).singularChainComplexπ R = 0 := by
  have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex 𝒰 h) R ≫
      SSet.chainComplexMap (X.smallSingularSubcomplex 𝒰).ι R =
        SSet.chainComplexMap (toSSet.map (TopPair.ofSubset B).map) R := by
    rw [← Functor.map_comp, toSmallSingularSubcomplex_ι, TopPair.ofSubset_map]
    -- `SSet.chainComplexMap` is the functor `(SSet.chainComplexFunctor C).obj R` on maps.
    rfl
  exact ((reassoc_of% h₁) _).trans (TopPair.chainComplexMap_comp_singularChainComplexπ _ R)

/-- For a member `A` of the family `𝒰` and a subset `B` of `X`, the chains of `A`, as small chains
of `X`, map to the relative chains of `(X, B)` as the relative chains of `(A, A ∩ B)` do under
the excision map. -/
lemma chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ_eq {A : Set X}
    (B : Set X) (h : A ⊆ 𝒰 i) :
    SSet.chainComplexMap (toSmallSingularSubcomplex 𝒰 h) R ≫
      SSet.chainComplexMap (X.smallSingularSubcomplex 𝒰).ι R ≫
        (TopPair.ofSubset B).singularChainComplexπ R =
      (TopPair.interPair A B).singularChainComplexπ R ≫
        TopPair.singularChainComplexMap (TopPair.excisionMap A B) R := by
  have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex 𝒰 h) R ≫
      SSet.chainComplexMap (X.smallSingularSubcomplex 𝒰).ι R =
        SSet.chainComplexMap (toSSet.map (TopPair.Hom.fst (TopPair.excisionMap A B))) R := by
    rw [← Functor.map_comp, toSmallSingularSubcomplex_ι, TopPair.excisionMap_fst]
    -- `SSet.chainComplexMap` is the functor `(SSet.chainComplexFunctor C).obj R` on maps.
    rfl
  exact ((reassoc_of% h₁) _).trans (TopPair.singularChainComplexπ_pair_naturality _ R)

end Small

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- **The Mayer–Vietoris connecting morphism through the pair `(U, U ∩ V)`.** For an open cover of
`X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)` is the map `Hₙ(X) ⟶ Hₙ(X, V)`,
followed by the inverse of the excision isomorphism `Hₙ(U, U ∩ V) ≅ Hₙ(X, V)`, by the connecting
morphism of the pair `(U, U ∩ V)`, and by the map induced by the homeomorphism
`TopPair.interPairSndHomeomorph U V` from the preimage of `V` in `U` onto `U ∩ V`. -/
theorem mayerVietorisδ_eq_singularHomologyδ_left (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h =
      (TopPair.ofSubset V).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R U V
          (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap U V) R n)) ≫
        (TopPair.interPair U V).singularHomologyδ R n m h ≫
        SSet.homologyMap (toSSet.map (TopPair.interPairSndIso U V).hom) R m := by
  have := TopPair.isIso_singularHomologyMap_excisionMap R U V
    (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
  have hc := (isPushout_toSSet_inter_smallSingularSubcomplex U V).map
    ((SSet.chainComplexFunctor C).obj R)
  have := TauCeti.isIso_homologyMap_smallSingularChainι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n
  have hφ := TopPair.interPairSndIso_inv_comp_map U V
  obtain ⟨g, hgr, hgb⟩ : ∃ g, ((SSet.chainComplexFunctor C).obj R).map
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset) ≫ g =
          (TopPair.interPair U V).singularChainComplexπ R ∧
      ((SSet.chainComplexFunctor C).obj R).map (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) ≫ g = 0 :=
    ⟨hc.desc _ 0 (by
      rw [comp_zero]
      exact TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac R (TopPair.interPair U V)
        _ _ hφ),
      hc.inl_desc _ _ _, hc.inr_desc _ _ _⟩
  have hg : g ≫ TopPair.singularChainComplexMap (TopPair.excisionMap U V) R =
      SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R ≫
        (TopPair.ofSubset V).singularChainComplexπ R := by
    apply hc.hom_ext
    · exact ((reassoc_of% hgr) _).trans
        (chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ_eq R _ V _).symm
    · exact ((reassoc_of% hgb) _).trans
        (zero_comp.trans
          (chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ R _ _).symm)
  have hφψ : toSSet.map (TopPair.interPairSndIso U V).inv ≫
      (TopPair.toSSetPair.obj (TopPair.interPair U V)).hom =
        toSSet.map (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) ≫
          𝟙 (TopPair.toSSetPair.obj (TopPair.interPair U V)).right := by
    -- `rw [Category.comp_id]` fails: the target of the inclusion is `of ↥U` on one side and
    -- `(TopPair.toSSetPair.obj (TopPair.interPair U V)).right` on the other.
    exact ((toSSet.map_comp _ _).symm.trans (congrArg toSSet.map hφ)).trans
      (Category.comp_id _).symm
  have key := SSet.mayerVietorisδ_comp_homologyMap_of_fst R
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (TopPair.toSSetPair.obj (TopPair.interPair U V))
    (toSSet.map (TopPair.interPairSndIso U V).inv) (𝟙 _)
    hφψ g
    (hgr.trans ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _).symm))) hgb n m h
  rw [TopPair.homologyMap_eq_singularHomologyπ_comp_inv R _ _ g hg,
    TopPair.singularHomologyπFst_eq] at key
  refine (cancel_epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n)).1 ?_
  rw [homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]
  have he : SSet.homologyMap (toSSet.map (TopPair.interPairSndIso U V).inv) R m ≫
      SSet.homologyMap (toSSet.map (TopPair.interPairSndIso U V).hom) R m = 𝟙 _ := by
    simp [← SSet.homologyMap_comp, ← Functor.map_comp]
  refine ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) he.symm)).trans ?_
  exact ((reassoc_of% key) _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

/-- **The Mayer–Vietoris connecting morphism through the pair `(V, U ∩ V)`.** For an open cover of
`X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)` is the negative of the map
`Hₙ(X) ⟶ Hₙ(X, U)`, followed by the inverse of the excision isomorphism
`Hₙ(V, U ∩ V) ≅ Hₙ(X, U)`, by the connecting morphism of the pair `(V, U ∩ V)`, and by the map
induced by the homeomorphism `TopPair.interPairSndHomeomorph V U` from the preimage of `U` in `V`
onto `V ∩ U`, followed by the identification of `V ∩ U` with `U ∩ V`. -/
theorem mayerVietorisδ_eq_neg_singularHomologyδ_right (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h =
      -((TopPair.ofSubset U).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R V U
          (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap V U) R n)) ≫
        (TopPair.interPair V U).singularHomologyδ R n m h ≫
        SSet.homologyMap (toSSet.map ((TopPair.interPairSndIso V U).hom ≫
          ofHom (Homeomorph.setCongr (Set.inter_comm V U)))) R m) := by
  have := TopPair.isIso_singularHomologyMap_excisionMap R V U
    (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
  have := TauCeti.isIso_homologyMap_smallSingularChainι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n
  have hc := (isPushout_toSSet_inter_smallSingularSubcomplex U V).map
    ((SSet.chainComplexFunctor C).obj R)
  let E : (TopPair.interPair V U).snd ≅ of ↥(U ∩ V) := TopPair.interPairSndIso V U ≪≫
    isoOfHomeo (X := of ↥(V ∩ U)) (Y := of ↥(U ∩ V)) (Homeomorph.setCongr (Set.inter_comm V U))
  have hφ : E.inv ≫ (TopPair.interPair V U).map =
      ofHom (ContinuousMap.inclusion Set.inter_subset_right) := by
    rw [Iso.trans_inv, Category.assoc, TopPair.interPairSndIso_inv_comp_map]
    -- Both sides send a point `y` of `U ∩ V` to the point `y` of `V`.
    ext
    rfl
  obtain ⟨g, hgr, hgb⟩ : ∃ g, ((SSet.chainComplexFunctor C).obj R).map
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset) ≫ g = 0 ∧
      ((SSet.chainComplexFunctor C).obj R).map (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) ≫ g =
          (TopPair.interPair V U).singularChainComplexπ R :=
    ⟨hc.desc 0 _ (by
      rw [comp_zero]
      exact (TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac R
        (TopPair.interPair V U) _ _ hφ).symm),
      hc.inl_desc _ _ _, hc.inr_desc _ _ _⟩
  have hg : g ≫ TopPair.singularChainComplexMap (TopPair.excisionMap V U) R =
      SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R ≫
        (TopPair.ofSubset U).singularChainComplexπ R := by
    apply hc.hom_ext
    · exact ((reassoc_of% hgr) _).trans (zero_comp.trans
        (chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ R _ _).symm)
    · exact ((reassoc_of% hgb) _).trans
        (chainComplexMap_toSmallSingularSubcomplex_comp_singularChainComplexπ_eq R _ U _).symm
  have hφψ : toSSet.map E.inv ≫ (TopPair.toSSetPair.obj (TopPair.interPair V U)).hom =
      toSSet.map (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) ≫
        𝟙 (TopPair.toSSetPair.obj (TopPair.interPair V U)).right :=
    -- See `TopCat.mayerVietorisδ_eq_singularHomologyδ_left` for why this is not a `rw`.
    ((toSSet.map_comp _ _).symm.trans (congrArg toSSet.map hφ)).trans (Category.comp_id _).symm
  have key := SSet.mayerVietorisδ_comp_homologyMap_of_snd R
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (TopPair.toSSetPair.obj (TopPair.interPair V U)) (toSSet.map E.inv) (𝟙 _) hφψ g hgr
    (hgb.trans ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _).symm))) n m h
  rw [TopPair.homologyMap_eq_singularHomologyπ_comp_inv R _ _ g hg,
    TopPair.singularHomologyπFst_eq] at key
  refine (cancel_epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n)).1 ?_
  rw [homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]
  have he : SSet.homologyMap (toSSet.map E.inv) R m ≫ SSet.homologyMap (toSSet.map E.hom) R m =
      𝟙 _ := by
    simp [← SSet.homologyMap_comp, ← Functor.map_comp]
  refine ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) he.symm)).trans ?_
  refine ((reassoc_of% key) _).trans ?_
  exact (Preadditive.neg_comp _ _).trans ((congrArg Neg.neg ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (Category.assoc _ _ _))))).trans
      (Preadditive.comp_neg _ _).symm)

/-- **The reduced Mayer–Vietoris connecting morphism through the pair `(U, U ∩ V)`**, in positive
degrees, where reduced and ordinary homology agree (`TauCeti.reducedSingularHomologySuccIso`): the
form of `TopCat.mayerVietorisδ_eq_singularHomologyδ_left` for `TopCat.reducedMayerVietorisδ`. -/
theorem reducedMayerVietorisδ_succ_eq_singularHomologyδ_left (k : ℕ) :
    reducedMayerVietorisδ R hU hV hUV (k + 1) =
      (TopPair.ofSubset V).singularHomologyπ R (k + 2) ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R U V
          (by rw [hU.interior_eq, hV.interior_eq, hUV]) (k + 2)
        inv (TopPair.singularHomologyMap (TopPair.excisionMap U V) R (k + 2))) ≫
        (TopPair.interPair U V).singularHomologyδ R (k + 2) (k + 1) ≫
        SSet.homologyMap (toSSet.map (TopPair.interPairSndIso U V).hom) R (k + 1) ≫
        (TauCeti.reducedSingularHomologySuccIso R k).inv.app (of ↥(U ∩ V)) := by
  have h₁ : reducedMayerVietorisδ R hU hV hUV (k + 1) =
      mayerVietorisδ R hU hV hUV (k + 2) (k + 1) ≫
        (TauCeti.reducedSingularHomologySuccIso R k).inv.app (of ↥(U ∩ V)) := by
    rw [← cancel_mono ((TauCeti.reducedSingularHomologyι R (k + 1)).app (of ↥(U ∩ V))),
      reducedMayerVietorisδ_comp_ι, ← TauCeti.reducedSingularHomologySuccIso_hom]
    -- `rw [Category.assoc]` fails here: the homology of `U ∩ V` appears both as
    -- `(toSSet.obj (of ↥(U ∩ V))).homology R (k + 1)` and through `singularHomologyFunctor`.
    exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (Iso.inv_hom_id_app (TauCeti.reducedSingularHomologySuccIso R k) (of ↥(U ∩ V)))).trans
        (Category.comp_id _))).symm
  rw [h₁, mayerVietorisδ_eq_singularHomologyδ_left R hU hV hUV (k + 2) (k + 1)]
  -- `simp only [Category.assoc]` fails here for the reason given above.
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

/-- **The image of an absolute class relative to `U ∩ V`, through excision.** For an open cover of
`X` by `U` and `V`, the map `Hₙ(X) ⟶ Hₙ(X, U ∩ V)` is the sum of two composites: the map
`Hₙ(X) ⟶ Hₙ(X, V)`, followed by the inverse of the excision isomorphism `Hₙ(U, U ∩ V) ≅ Hₙ(X, V)`
and by the inclusion `(U, U ∩ V) ⟶ (X, U ∩ V)`; and the map `Hₙ(X) ⟶ Hₙ(X, U)`, followed by the
inverse of the excision isomorphism `Hₙ(V, V ∩ U) ≅ Hₙ(X, U)` and by the inclusion
`(V, V ∩ U) ⟶ (X, U ∩ V)`. -/
theorem singularHomologyπ_ofSubset_inter_eq_add (n : ℕ) :
    (TopPair.ofSubset (U ∩ V)).singularHomologyπ R n =
      ((TopPair.ofSubset V).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R U V
          (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap U V) R n)) ≫
        TopPair.singularHomologyMap
          (TopPair.interPairMapOfSubset (subset_refl (U ∩ V))) R n :
        (toSSet.obj X).homology R n ⟶ _) +
      ((TopPair.ofSubset U).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R V U
          (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap V U) R n)) ≫
        TopPair.singularHomologyMap
          (TopPair.interPairMapOfSubset (Set.inter_comm V U).subset) R n :
        (toSSet.obj X).homology R n ⟶ _) := by
  have := TopPair.isIso_singularHomologyMap_excisionMap R U V
    (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
  have := TopPair.isIso_singularHomologyMap_excisionMap R V U
    (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
  have hU₁ : Set.MapsTo (𝟙 X) (U ∩ V) U := (Set.mapsTo_id _).mono_right Set.inter_subset_left
  have hV₁ : Set.MapsTo (𝟙 X) (U ∩ V) V := (Set.mapsTo_id _).mono_right Set.inter_subset_right
  -- An inclusion `(A, A ∩ B) ⟶ (X, U ∩ V)` followed by `(X, U ∩ V) ⟶ (X, A)` induces zero.
  have h₀ {A B : Set X} (h₁ : A ∩ B ⊆ U ∩ V) (h₂ : Set.MapsTo (𝟙 X) (U ∩ V) A) :
      TopPair.singularHomologyMap (TopPair.interPairMapOfSubset h₁) R n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) h₂) R n = 0 := by
    rw [← TopPair.singularHomologyMap_comp, TopPair.interPairMapOfSubset_comp_ofSubsetMap_id]
    -- `TopPair.interPairMapOfSubset` is the map of pairs `TopPair.ofSubsetMap` of the inclusion.
    refine (congrArg (TopPair.singularHomologyMap · R n) (TopPair.hom_ext_of_fst _
      ((TopPair.interPairMapOfSubset_fst _).trans (TopPair.ofSubsetMap_fst _
        (show Set.MapsTo (ofHom (ContinuousMap.subtypeVal A)) (Subtype.val ⁻¹' B) A from
          fun x _ ↦ x.property)).symm))).trans ?_
    exact TopPair.singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset R _ _
      (fun _ ⟨y, hy⟩ ↦ hy ▸ y.property) n
  -- The steps below are `Eq.trans` rather than `rw` or `simp`: the two summands have the
  -- homology of `X` as source under different names,
  -- `(TopPair.toSSetPair.obj (TopPair.ofSubset U)).right` and the same for `V`, so that
  -- rewriting inside the sum fails.
  refine TopPair.singularHomology_inter_hom_ext R (by rw [hU.interior_eq, hV.interior_eq, hUV])
    hU₁ hV₁ n ?_ ?_
  · refine (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id R hU₁ n).trans ?_
    refine ((zero_add _).symm.trans (congrArg₂ (· + ·) ?_ ?_)).trans
      (Preadditive.add_comp _ _ _ _ _ _).symm
    · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans comp_zero))
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h₀ _ _)).trans comp_zero)
    · refine Eq.symm ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)))
      exact (Category.assoc _ _ _).trans
        (TopPair.inv_singularHomologyMap_excisionMap_comp_ofSubsetMap_id R _ _ n)
  · refine (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id R hV₁ n).trans ?_
    refine ((add_zero _).symm.trans (congrArg₂ (· + ·) ?_ ?_)).trans
      (Preadditive.add_comp _ _ _ _ _ _).symm
    · refine Eq.symm ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)))
      exact (Category.assoc _ _ _).trans
        (TopPair.inv_singularHomologyMap_excisionMap_comp_ofSubsetMap_id R _ _ n)
    · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans comp_zero))
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h₀ _ _)).trans comp_zero)

end TopCat
