/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced

/-!
# The Mayer–Vietoris connecting morphism through the connecting morphism of a pair

Let `U` and `V` be open subsets of a space `X` with `U ∪ V = X`. The Mayer–Vietoris connecting
morphism `TopCat.mayerVietorisδ : Hₙ(X) ⟶ Hₘ(U ∩ V)`, `m + 1 = n`, is the composite of the map
`Hₙ(X) ⟶ Hₙ(X, V)`, of the inverse of the excision isomorphism `Hₙ(U, U ∩ V) ≅ Hₙ(X, V)`, of the
connecting morphism of the pair `(U, U ∩ V)` and of the identification of the preimage of `V` in
`U` with `U ∩ V` (`TopCat.mayerVietorisδ_eq_singularHomologyδ_left`). The same composite with the
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

## Main results

* `SSet.mayerVietorisδ_comp_homologyMap_of_fst`, `SSet.mayerVietorisδ_comp_homologyMap_of_snd`:
  the Mayer–Vietoris connecting morphism of a pushout square of simplicial sets and that of a pair.
* `TopCat.mayerVietorisδ_eq_singularHomologyδ_left`: the Mayer–Vietoris connecting morphism of an
  open cover through the pair `(U, U ∩ V)`.
* `TopCat.mayerVietorisδ_eq_neg_singularHomologyδ_right`: the same through the pair `(V, U ∩ V)`,
  with a sign.
* `TopCat.reducedMayerVietorisδ_succ_eq_singularHomologyδ_left`: the reduced form in positive
  degrees.

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
        change chainComplexMap φ R ≫ chainComplexMap P.hom R =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫ biprod.fst ≫
            chainComplexMap ψ R
        rw [biprod.lift_fst_assoc, ← Functor.map_comp, ← Functor.map_comp, hφψ]
      comm₂₃ := by
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
        change (-chainComplexMap φ R) ≫ chainComplexMap P.hom R =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫ biprod.snd ≫
            chainComplexMap ψ R
        rw [biprod.lift_snd_assoc, Preadditive.neg_comp, Preadditive.neg_comp,
          ← Functor.map_comp, ← Functor.map_comp, hφψ]
      comm₂₃ := by
        change (biprod.snd ≫ chainComplexMap ψ R) ≫ P.chainComplexπ R =
          biprod.desc (chainComplexMap r R) (chainComplexMap b R) ≫ g
        apply biprod.hom_ext' <;> simp [hr, hb] }
    (shortExact_mayerVietorisShortComplex R sq) (P.shortExact_chainComplexShortComplex R) n m h
  rw [mayerVietorisδ_def R sq n m h, SSetPair.homologyδ, ← this, HomologicalComplex.homologyMap_neg,
    Preadditive.comp_neg, neg_neg]

end SSet

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- **The Mayer–Vietoris connecting morphism through the pair `(U, U ∩ V)`.** For an open cover of
`X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)` is the map `Hₙ(X) ⟶ Hₙ(X, V)`,
followed by the inverse of the excision isomorphism `Hₙ(U, U ∩ V) ≅ Hₙ(X, V)`, by the connecting
morphism of the pair `(U, U ∩ V)`, and by the identification of the preimage of `V` in `U` with
`U ∩ V`. -/
theorem mayerVietorisδ_eq_singularHomologyδ_left (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h =
      (TopPair.ofSubset V).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R U V
          (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap U V) R n)) ≫
        (TopPair.interPair U V).singularHomologyδ R n m h ≫
        SSet.homologyMap (toSSet.map (ofHom ⟨fun x ↦
          ⟨x.val.val, Set.mem_inter x.val.property x.property⟩, by fun_prop⟩)) R m := by
  have := TopPair.isIso_singularHomologyMap_excisionMap R U V
    (by rw [hU.interior_eq, hV.interior_eq, hUV]) n
  have := TauCeti.isIso_homologyMap_smallSingularChainι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n
  obtain ⟨e, he, he'⟩ : ∃ e : of ↥(U ∩ V) ⟶ (TopPair.interPair U V).snd,
      e ≫ (TopPair.interPair U V).map = ofHom (ContinuousMap.inclusion Set.inter_subset_left) ∧
      SSet.homologyMap (toSSet.map e) R m ≫ SSet.homologyMap (toSSet.map
        (ofHom ⟨fun x ↦ ⟨x.val.val, Set.mem_inter x.val.property x.property⟩, by fun_prop⟩)) R m =
          𝟙 _ :=
    ⟨ofHom ⟨fun x ↦ ⟨⟨x.val, x.property.left⟩, x.property.right⟩, by fun_prop⟩, rfl,
      (SSet.homologyMap_comp ..).symm.trans (((congrArg (SSet.homologyMap · R m)
        ((toSSet.map_comp _ _).symm.trans (toSSet.map_id _)))).trans (SSet.homologyMap_id ..))⟩
  have hφ : toSSet.map e ≫ toSSet.map (TopPair.interPair U V).map =
      toSSet.map (ofHom (ContinuousMap.inclusion Set.inter_subset_left)) :=
    (toSSet.map_comp _ _).symm.trans (congrArg _ he)
  have hc := (isPushout_toSSet_inter_smallSingularSubcomplex U V).map
    ((SSet.chainComplexFunctor C).obj R)
  obtain ⟨g, hgr, hgb⟩ : ∃ g, ((SSet.chainComplexFunctor C).obj R).map
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset) ≫ g =
          (TopPair.interPair U V).singularChainComplexπ R ∧
      ((SSet.chainComplexFunctor C).obj R).map (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) ≫ g = 0 :=
    ⟨hc.desc _ 0 (by
      rw [comp_zero, ← hφ]
      exact (((SSet.chainComplexFunctor C).obj R).map_comp _ _ =≫ _).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
          (TopPair.chainComplexMap_comp_singularChainComplexπ _ R)).trans comp_zero))),
      hc.inl_desc _ _ _, hc.inr_desc _ _ _⟩
  have key := SSet.mayerVietorisδ_comp_homologyMap_of_fst R
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (TopPair.toSSetPair.obj (TopPair.interPair U V)) (toSSet.map e) (𝟙 _)
    (hφ.trans (Category.comp_id _).symm) g
    (hgr.trans ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _).symm))) hgb n m h
  have hg : g ≫ TopPair.singularChainComplexMap (TopPair.excisionMap U V) R =
      SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R ≫
        (TopPair.ofSubset V).singularChainComplexπ R := by
    apply hc.hom_ext
    · have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex ![U, V]
          (Matrix.cons_val_zero U ![V]).superset) R ≫
            SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R =
          SSet.chainComplexMap (toSSet.map (TopPair.Hom.fst (TopPair.excisionMap U V))) R := by
        rw [← Functor.map_comp, toSmallSingularSubcomplex_ι]
        congr 2
        ext x
        exact (TopPair.excisionMap_fst_apply U V x).symm
      exact ((reassoc_of% hgr) _).trans
        ((TopPair.singularChainComplexπ_pair_naturality _ R).symm.trans ((reassoc_of% h₁) _).symm)
    · have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex ![U, V]
          ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) R ≫
            SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R =
          ((SSet.chainComplexFunctor C).obj R).map (toSSet.map (TopPair.ofSubset V).map) := by
        rw [← Functor.map_comp, toSmallSingularSubcomplex_ι, TopPair.ofSubset_map]
        -- The two sides differ only in how the subspace is written as an object of `TopCat`.
        rfl
      rw [(reassoc_of% hgb) _, zero_comp]
      exact (TopPair.chainComplexMap_comp_singularChainComplexπ (TopPair.ofSubset V) R).symm.trans
        ((reassoc_of% h₁) ((TopPair.ofSubset V).singularChainComplexπ R)).symm
  have hH : HomologicalComplex.homologyMap g n =
      (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n ≫
        (TopPair.ofSubset V).singularHomologyπ R n) ≫
          inv (TopPair.singularHomologyMap (TopPair.excisionMap U V) R n) :=
    (IsIso.eq_comp_inv _).2 ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · n) hg).trans
        (HomologicalComplex.homologyMap_comp _ _ _)))
  refine (cancel_epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n)).1 ?_
  rw [homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]
  refine ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) he'.symm)).trans ?_
  exact ((reassoc_of% key) _).trans ((congrArg (· ≫ _) hH).trans
    ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))


/-- **The Mayer–Vietoris connecting morphism through the pair `(V, U ∩ V)`.** For an open cover of
`X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)` is the negative of the map
`Hₙ(X) ⟶ Hₙ(X, U)`, followed by the inverse of the excision isomorphism
`Hₙ(V, U ∩ V) ≅ Hₙ(X, U)`, by the connecting morphism of the pair `(V, U ∩ V)`, and by the
identification of the preimage of `U` in `V` with `U ∩ V`. -/
theorem mayerVietorisδ_eq_neg_singularHomologyδ_right (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h =
      -((TopPair.ofSubset U).singularHomologyπ R n ≫
        (haveI := TopPair.isIso_singularHomologyMap_excisionMap R V U
          (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
        inv (TopPair.singularHomologyMap (TopPair.excisionMap V U) R n)) ≫
        (TopPair.interPair V U).singularHomologyδ R n m h ≫
        SSet.homologyMap (toSSet.map (ofHom ⟨fun x ↦
          ⟨x.val.val, Set.mem_inter x.property x.val.property⟩, by fun_prop⟩)) R m) := by
  have := TopPair.isIso_singularHomologyMap_excisionMap R V U
    (by rw [hU.interior_eq, hV.interior_eq, Set.union_comm, hUV]) n
  have := TauCeti.isIso_homologyMap_smallSingularChainι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n
  obtain ⟨e, he, he'⟩ : ∃ e : of ↥(U ∩ V) ⟶ (TopPair.interPair V U).snd,
      e ≫ (TopPair.interPair V U).map = ofHom (ContinuousMap.inclusion Set.inter_subset_right) ∧
      SSet.homologyMap (toSSet.map e) R m ≫ SSet.homologyMap (toSSet.map
        (ofHom ⟨fun x ↦ ⟨x.val.val, Set.mem_inter x.property x.val.property⟩, by fun_prop⟩)) R m =
          𝟙 _ :=
    ⟨ofHom ⟨fun x ↦ ⟨⟨x.val, x.property.right⟩, x.property.left⟩, by fun_prop⟩, rfl,
      (SSet.homologyMap_comp ..).symm.trans (((congrArg (SSet.homologyMap · R m)
        ((toSSet.map_comp _ _).symm.trans (toSSet.map_id _)))).trans (SSet.homologyMap_id ..))⟩
  have hφ : toSSet.map e ≫ toSSet.map (TopPair.interPair V U).map =
      toSSet.map (ofHom (ContinuousMap.inclusion Set.inter_subset_right)) :=
    (toSSet.map_comp _ _).symm.trans (congrArg _ he)
  have hc := (isPushout_toSSet_inter_smallSingularSubcomplex U V).map
    ((SSet.chainComplexFunctor C).obj R)
  obtain ⟨g, hgr, hgb⟩ : ∃ g, ((SSet.chainComplexFunctor C).obj R).map
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset) ≫ g = 0 ∧
      ((SSet.chainComplexFunctor C).obj R).map (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) ≫ g =
          (TopPair.interPair V U).singularChainComplexπ R :=
    ⟨hc.desc 0 _ (by
      rw [comp_zero, ← hφ]
      exact ((((SSet.chainComplexFunctor C).obj R).map_comp _ _ =≫ _).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
          (TopPair.chainComplexMap_comp_singularChainComplexπ _ R)).trans comp_zero))).symm),
      hc.inl_desc _ _ _, hc.inr_desc _ _ _⟩
  have key := SSet.mayerVietorisδ_comp_homologyMap_of_snd R
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (TopPair.toSSetPair.obj (TopPair.interPair V U)) (toSSet.map e) (𝟙 _)
    (hφ.trans (Category.comp_id _).symm) g hgr
    (hgb.trans ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _).symm))) n m h
  have hg : g ≫ TopPair.singularChainComplexMap (TopPair.excisionMap V U) R =
      SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R ≫
        (TopPair.ofSubset U).singularChainComplexπ R := by
    apply hc.hom_ext
    · have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex ![U, V]
          (Matrix.cons_val_zero U ![V]).superset) R ≫
            SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R =
          ((SSet.chainComplexFunctor C).obj R).map (toSSet.map (TopPair.ofSubset U).map) := by
        rw [← Functor.map_comp, toSmallSingularSubcomplex_ι, TopPair.ofSubset_map]
        -- The two sides differ only in how the subspace is written as an object of `TopCat`.
        rfl
      rw [(reassoc_of% hgr) _, zero_comp]
      exact (TopPair.chainComplexMap_comp_singularChainComplexπ (TopPair.ofSubset U) R).symm.trans
        ((reassoc_of% h₁) ((TopPair.ofSubset U).singularChainComplexπ R)).symm
    · have h₁ : SSet.chainComplexMap (toSmallSingularSubcomplex ![U, V]
          ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) R ≫
            SSet.chainComplexMap (X.smallSingularSubcomplex ![U, V]).ι R =
          SSet.chainComplexMap (toSSet.map (TopPair.Hom.fst (TopPair.excisionMap V U))) R := by
        rw [← Functor.map_comp, toSmallSingularSubcomplex_ι]
        congr 2
        ext x
        exact (TopPair.excisionMap_fst_apply V U x).symm
      exact ((reassoc_of% hgb) _).trans
        ((TopPair.singularChainComplexπ_pair_naturality _ R).symm.trans ((reassoc_of% h₁) _).symm)
  have hH : HomologicalComplex.homologyMap g n =
      (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n ≫
        (TopPair.ofSubset U).singularHomologyπ R n) ≫
          inv (TopPair.singularHomologyMap (TopPair.excisionMap V U) R n) :=
    (IsIso.eq_comp_inv _).2 ((HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · n) hg).trans
        (HomologicalComplex.homologyMap_comp _ _ _)))
  refine (cancel_epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n)).1 ?_
  rw [homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]
  refine ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) he'.symm)).trans ?_
  exact ((reassoc_of% key) _).trans ((Preadditive.neg_comp _ _).trans
    ((congrArg Neg.neg (((Category.assoc _ _ _).trans
      (congrArg (· ≫ (TopPair.interPair V U).singularHomologyδ R n m h ≫ _) hH)).trans
        ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))).trans
          (Preadditive.comp_neg _ _).symm))


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
        SSet.homologyMap (toSSet.map (ofHom ⟨fun x ↦
          ⟨x.val.val, Set.mem_inter x.val.property x.property⟩, by fun_prop⟩)) R (k + 1) ≫
        (TauCeti.reducedSingularHomologySuccIso R k).inv.app (of ↥(U ∩ V)) := by
  have h₁ : reducedMayerVietorisδ R hU hV hUV (k + 1) =
      mayerVietorisδ R hU hV hUV (k + 2) (k + 1) ≫
        (TauCeti.reducedSingularHomologySuccIso R k).inv.app (of ↥(U ∩ V)) := by
    refine (cancel_mono ((TauCeti.reducedSingularHomologyι R (k + 1)).app (of ↥(U ∩ V)))).1 ?_
    rw [reducedMayerVietorisδ_comp_ι, ← TauCeti.reducedSingularHomologySuccIso_hom]
    exact ((Category.assoc _ _ _).trans ((congrArg (mayerVietorisδ R hU hV hUV (k + 2) (k + 1) ≫ ·)
      (Iso.inv_hom_id_app (TauCeti.reducedSingularHomologySuccIso R k) (of ↥(U ∩ V)))).trans
      (Category.comp_id _))).symm
  rw [h₁, mayerVietorisδ_eq_singularHomologyδ_left R hU hV hUV (k + 2) (k + 1)]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))

end TopCat
