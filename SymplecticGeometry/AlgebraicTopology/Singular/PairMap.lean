/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision

/-!
# Maps of topological pairs: excision maps and maps into a subspace

General facts about Tau Ceti's maps of topological pairs and the relative singular chains and
homology they induce.

For subsets `A` and `B` of a space `X`, the subspace of the pair `TopPair.interPair A B`, the
preimage of `B` in `A`, is homeomorphic to `A ∩ B` (`TopPair.interPairSndHomeomorph`,
`TopPair.interPairSndIso`), and the excision map `(A, A ∩ B) ⟶ (X, B)` is the map of pairs
`TopPair.ofSubsetMap` induced by the inclusion of `A` (`TopPair.excisionMap_eq_ofSubsetMap`).

A map into the ambient space of a pair that factors through the subspace vanishes on relative
chains (`TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac`), and a map of subspace pairs
whose ambient map lands in the subspace of the target vanishes on relative homology
(`TopPair.singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset`). The proof of
`TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac` adapts that of Tau Ceti's
`TopPair.singularChainComplexMap_eq_zero_of_fac`, in
`TauCeti/AlgebraicTopology/Singular/Relative.lean`, to a map into the ambient space that need not
come from a map of pairs.

## Main definitions

* `TopPair.interPairSndHomeomorph A B`: the homeomorphism from the subspace of
  `TopPair.interPair A B` onto `A ∩ B`, and `TopPair.interPairSndIso`, the same as an isomorphism
  of `TopCat`.

## Main results

* `TopPair.excisionMap_eq_ofSubsetMap`, `TopPair.excisionMap_fst`: the excision map through the
  inclusion of `A`.
* `TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac`: maps through the subspace vanish on
  relative chains.
* `TopPair.homologyMap_eq_singularHomologyπ_comp_inv`: a chain map into the relative chains of a
  pair, compatible with a map of pairs that is an isomorphism on homology, through the inverse of
  that isomorphism.
* `TopPair.singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset`: maps into the subspace vanish
  on relative homology.
* `TopPair.inv_singularHomologyMap_excisionMap_comp_ofSubsetMap_id`: the inverse of excision,
  followed by the inclusions `(A, A ∩ B) ⟶ (X, S) ⟶ (X, B)`, is the identity.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1: relative
  homology and excision.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

section Subsets

variable {X : TopCat.{w}} (A B : Set X)

/-- The subspace of the pair `TopPair.interPair A B = (A, A ∩ B)`, which is the preimage of `B` in
the subspace `A`, is homeomorphic to the subspace `A ∩ B` of `X`. -/
def interPairSndHomeomorph : (interPair A B).snd ≃ₜ ↥(A ∩ B) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
lemma coe_interPairSndHomeomorph_apply (x : (interPair A B).snd) :
    (interPairSndHomeomorph A B x : X) = x.val.val :=
  (rfl)

@[simp]
lemma interPairSndHomeomorph_symm_apply_coe (y : ↥(A ∩ B)) :
    ((interPairSndHomeomorph A B).symm y).val = ⟨y.val, y.property.1⟩ :=
  (rfl)

/-- `TopPair.interPairSndHomeomorph A B` as an isomorphism in `TopCat`. -/
def interPairSndIso : (interPair A B).snd ≅ TopCat.of ↥(A ∩ B) :=
  TopCat.isoOfHomeo (X := (interPair A B).snd) (Y := TopCat.of ↥(A ∩ B))
    (interPairSndHomeomorph A B)

@[simp]
lemma interPairSndIso_hom_apply (x : (interPair A B).snd) :
    (interPairSndIso A B).hom x = interPairSndHomeomorph A B x :=
  (rfl)

@[simp]
lemma interPairSndIso_inv_apply (y : ↥(A ∩ B)) :
    (interPairSndIso A B).inv y = (interPairSndHomeomorph A B).symm y :=
  (rfl)

/-- The inverse of `TopPair.interPairSndIso A B` followed by the embedding of the subspace of
`(A, A ∩ B)` is the inclusion of `A ∩ B` into `A`. -/
@[reassoc]
lemma interPairSndIso_inv_comp_map :
    (interPairSndIso A B).inv ≫ (interPair A B).map =
      TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left) := by
  ext y
  exact interPairSndHomeomorph_symm_apply_coe A B y

/-- The excision map `(A, A ∩ B) ⟶ (X, B)` is the map of pairs induced by the inclusion of `A`. -/
lemma excisionMap_eq_ofSubsetMap :
    excisionMap A B = ofSubsetMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) (fun _ hx ↦ hx) := by
  refine Eq.symm ?_
  ext x : 2
  · exact Subtype.ext ((ofSubsetMap_snd_apply _ _ x).trans (excisionMap_snd_apply A B x).symm)
  · exact (ofSubsetMap_fst_apply _ _ x).trans (excisionMap_fst_apply A B x).symm

/-- The ambient map of the excision map `(A, A ∩ B) ⟶ (X, B)` is the inclusion of `A`. -/
lemma excisionMap_fst : Hom.fst (excisionMap A B) = TopCat.ofHom (ContinuousMap.subtypeVal A) := by
  ext x
  exact excisionMap_fst_apply A B x

end Subsets

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- A map into the ambient space of a pair that factors through its subspace sends singular chains
to zero in the relative chains of the pair. -/
lemma chainComplexMap_comp_singularChainComplexπ_of_fac (P : TopPair.{w}) {Y : TopCat.{w}}
    (k : Y ⟶ P.fst) (g : Y ⟶ P.snd) (hg : g ≫ P.map = k) :
    SSet.chainComplexMap (TopCat.toSSet.map k) R ≫ P.singularChainComplexπ R = 0 := by
  subst hg
  rw [Functor.map_comp]
  -- `rw [Functor.map_comp, Category.assoc]` fails here: the chains of `P.fst` appear both as
  -- `(TopCat.toSSet.obj P.fst).chainComplex R` and as `(toSSetPair.obj P).right.chainComplex R`.
  exact (Functor.map_comp _ _ _ =≫ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (chainComplexMap_comp_singularChainComplexπ P R)).trans comp_zero))

/-- Let `e : P ⟶ Q` be a map of pairs that induces an isomorphism in degree `n`, and `g` a chain
map from the chains of `K` to the relative chains of `P` that `e` sends to the image of the chains
of `K` under `f : K ⟶ Q.fst` in the relative chains of `Q`. Then the map induced by `g` is the map
induced by `f`, followed by `Hₙ(Q.fst) ⟶ Hₙ(Q)` and by the inverse of the map induced by `e`. -/
lemma homologyMap_eq_singularHomologyπ_comp_inv {P Q : TopPair.{w}} (e : P ⟶ Q) {K : SSet.{w}}
    (f : K ⟶ TopCat.toSSet.obj Q.fst) (g : K.chainComplex R ⟶ P.singularChainComplex R)
    (hg : g ≫ singularChainComplexMap e R =
      SSet.chainComplexMap f R ≫ Q.singularChainComplexπ R) (n : ℕ)
    [IsIso (TopPair.singularHomologyMap e R n)] :
    HomologicalComplex.homologyMap g n =
      SSet.homologyMap f R n ≫ Q.singularHomologyπ R n ≫
        inv (TopPair.singularHomologyMap e R n) := by
  -- `rw [← Category.assoc]` fails here, for the reason given in
  -- `TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac`, with homology in place of chains.
  refine ((IsIso.eq_comp_inv _).2 ?_).trans (Category.assoc _ _ _)
  rw [← HomologicalComplex.homologyMap_comp, hg]
  exact HomologicalComplex.homologyMap_comp _ _ _

/-- A map of pairs `(Y, B) ⟶ (X, S)` induced by a map `f : Y ⟶ X` whose range lies in `S` induces
zero on relative singular homology. -/
lemma singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset {X Y : TopCat.{w}} {B : Set Y}
    {S : Set X} (f : Y ⟶ X) (h : Set.MapsTo f B S) (hf : Set.range f ⊆ S) (n : ℕ) :
    TopPair.singularHomologyMap (ofSubsetMap f h) R n = 0 :=
  singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (⟨fun y ↦ ⟨f y, hf ⟨y, rfl⟩⟩, by fun_prop⟩ : C(Y, S)) : Y ⟶ (ofSubset S).snd)
    (by ext y; exact (ofSubsetMap_fst_apply f h y).symm) n

/-- For a subset `S` of `X` with `A ∩ B ⊆ S ⊆ B`, the inverse of the excision isomorphism
`Hₙ(A, A ∩ B) ≅ Hₙ(X, B)`, followed by the maps induced by the inclusions of pairs
`(A, A ∩ B) ⟶ (X, S) ⟶ (X, B)`, is the identity of `Hₙ(X, B)`. -/
lemma inv_singularHomologyMap_excisionMap_comp_ofSubsetMap_id {X : TopCat.{w}} {A B S : Set X}
    (h₁ : Set.MapsTo (TopCat.ofHom (ContinuousMap.subtypeVal A)) (Subtype.val ⁻¹' B) S)
    (h₂ : Set.MapsTo (𝟙 X) S B) (n : ℕ)
    [IsIso (TopPair.singularHomologyMap (excisionMap A B) R n)] :
    inv (TopPair.singularHomologyMap (excisionMap A B) R n) ≫
      TopPair.singularHomologyMap
        (ofSubsetMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) h₁) R n ≫
        TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) h₂) R n = 𝟙 _ := by
  rw [← TopPair.singularHomologyMap_comp,
    ofSubsetMap_comp_ofSubsetMap_of_comp_eq h₁ h₂ (h₂.comp h₁) (Category.comp_id _),
    ← excisionMap_eq_ofSubsetMap, IsIso.inv_hom_id]

end TopPair

end
