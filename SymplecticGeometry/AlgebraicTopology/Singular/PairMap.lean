/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Topology.Category.TopCat.CodRestrict
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
chains (`TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac`); so does a map into `X` with
range in `A`, on the chains relative to `A`, since its corestriction `TopCat.codRestrict` to `A`
factors it through the subspace
(`TopPair.chainComplexMap_comp_singularChainComplexπ_eq_zero_of_range_subset`). A map of subspace
pairs whose ambient map lands in the subspace of the target vanishes on relative homology
(`TopPair.singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset`). The proof of
`TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac` adapts that of Tau Ceti's
`TopPair.singularChainComplexMap_eq_zero_of_fac`, in
`TauCeti/AlgebraicTopology/Singular/Relative.lean`, to a map into the ambient space that need not
come from a map of pairs.

Tau Ceti writes the source of the quotient map `TopPair.singularChainComplexπ` as the ambient
chains of `TopPair.toSSetPair.obj P`, which are the chains of `P.fst` only up to unfolding; so
`rw [Category.assoc]` and `reassoc` lemmas fail on its composites with chain maps into the chains
of `P.fst`. The abbreviations `TopPair.singularChainComplexπFst`,
`TopPair.singularHomologyπFst` and `TopPair.singularChainComplexπOfSubset` are the same maps
with their sources written as the chains (or homology) of the ambient space, and the lemmas
stated with them reassociate by `rw`.

## Main definitions

* `TopPair.singularChainComplexπFst`, `TopPair.singularHomologyπFst`: the maps from the singular
  chains and homology of `P.fst` to the relative ones of `P`.
* `TopPair.singularChainComplexπOfSubset`: the map from the singular chains of `X` to the
  relative ones of `(X, A)`.
* `TopPair.interPairSndHomeomorph A B`: the homeomorphism from the subspace of
  `TopPair.interPair A B` onto `A ∩ B`, and `TopPair.interPairSndIso`, the same as an isomorphism
  of `TopCat`.

## Main results

* `TopPair.chainComplexMap_comp_singularChainComplexπFst`,
  `TopPair.singularChainComplexπFst_naturality`, `TopPair.singularChainComplexπOfSubset_naturality`:
  the chains of the subspace vanish in the relative chains, and the quotient maps are natural.
* `TopPair.homologyMap_comp_singularHomologyπFst`, `TopPair.singularHomologyπFst_naturality`: the
  same on homology.
* `TopPair.excisionMap_eq_ofSubsetMap`, `TopPair.excisionMap_fst`: the excision map through the
  inclusion of `A`.
* `TopPair.codRestrict_comp_ofSubset_map`: the corestriction of a map to `A`, followed by the
  embedding of the subspace of `(X, A)`, is the map.
* `TopPair.chainComplexMap_comp_singularChainComplexπ_of_fac`: maps through the subspace vanish on
  relative chains.
* `TopPair.chainComplexMap_comp_singularChainComplexπ_eq_zero_of_range_subset`: maps with range in
  `A` vanish on the chains relative to `A`.
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

/-- The corestriction of a map `f : Z ⟶ X` to `A`, followed by the embedding of the subspace of
the pair `(X, A)`, is `f`. -/
@[reassoc]
lemma codRestrict_comp_ofSubset_map {Z : TopCat.{w}} (f : Z ⟶ X) (h : ∀ z, f z ∈ A) :
    TopCat.codRestrict f A h ≫ (ofSubset A).map = f :=
  (congrArg (TopCat.codRestrict f A h ≫ ·) (ofSubset_map A)).trans
    (TopCat.codRestrict_comp_ofHom_subtypeVal f A h)

end Subsets

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] (R : C)

section Preadditive

variable [Preadditive C]

section Fst

variable (P : TopPair.{w})

/-- The quotient map from the singular chains of the ambient space `P.fst` of a pair to the
relative singular chains of the pair.

This is `TopPair.singularChainComplexπ`, whose source is the ambient chains of
`TopPair.toSSetPair.obj P`; here the source is written as the chains of `P.fst`, the target of
`SSet.chainComplexMap (TopCat.toSSet.map k) R` for a map `k` into `P.fst`, so that composites
with such maps reassociate by `rw`. -/
noncomputable abbrev singularChainComplexπFst :
    (TopCat.toSSet.obj P.fst).chainComplex R ⟶ P.singularChainComplex R :=
  P.singularChainComplexπ R

lemma singularChainComplexπFst_eq : P.singularChainComplexπFst R = P.singularChainComplexπ R :=
  (rfl)

/-- The quotient map from the singular chains of `P.fst` to the relative singular chains of `P` is
an epimorphism. -/
instance epi_singularChainComplexπFst : Epi (P.singularChainComplexπFst R) :=
  inferInstanceAs (Epi (P.singularChainComplexπ R))

/-- The singular chains of the subspace of a pair vanish in its relative singular chains. -/
@[reassoc]
lemma chainComplexMap_comp_singularChainComplexπFst :
    SSet.chainComplexMap (TopCat.toSSet.map P.map) R ≫ P.singularChainComplexπFst R = 0 :=
  chainComplexMap_comp_singularChainComplexπ P R

variable {P} in
/-- The quotient map from the singular chains of the ambient space to the relative singular chains
is natural in maps of pairs. -/
@[reassoc]
lemma singularChainComplexπFst_naturality {Q : TopPair.{w}} (f : P ⟶ Q) :
    SSet.chainComplexMap (TopCat.toSSet.map (Hom.fst f)) R ≫ Q.singularChainComplexπFst R =
      P.singularChainComplexπFst R ≫ singularChainComplexMap f R :=
  singularChainComplexπ_pair_naturality f R

end Fst

section OfSubset

variable {X Y : TopCat.{w}}

/-- The quotient map from the singular chains of `X` to the relative singular chains of the pair
`(X, A)`: `TopPair.singularChainComplexπ` of `TopPair.ofSubset A`, with its source written as the
chains of `X` rather than as the ambient chains of the pair, as in
`TopPair.singularChainComplexπFst`. -/
noncomputable abbrev singularChainComplexπOfSubset (A : Set X) :
    (TopCat.toSSet.obj X).chainComplex R ⟶ (ofSubset A).singularChainComplex R :=
  (ofSubset A).singularChainComplexπ R

lemma singularChainComplexπOfSubset_eq (A : Set X) :
    singularChainComplexπOfSubset R A = (ofSubset A).singularChainComplexπ R :=
  (rfl)

/-- The quotient map from the singular chains of `X` to the relative singular chains of `(X, A)` is
an epimorphism. -/
instance epi_singularChainComplexπOfSubset (A : Set X) :
    Epi (singularChainComplexπOfSubset R A) :=
  inferInstanceAs (Epi ((ofSubset A).singularChainComplexπ R))

/-- The quotient map from the singular chains of `X` to the relative singular chains of `(X, A)`
is natural in the maps of pairs `TopPair.ofSubsetMap g hA : (X, A) ⟶ (Y, B)`. -/
@[reassoc]
lemma singularChainComplexπOfSubset_naturality (g : X ⟶ Y) {A : Set X} {B : Set Y}
    (hA : Set.MapsTo g A B) :
    SSet.chainComplexMap (TopCat.toSSet.map g) R ≫ singularChainComplexπOfSubset R B =
      singularChainComplexπOfSubset R A ≫ singularChainComplexMap (ofSubsetMap g hA) R := by
  have h := singularChainComplexπ_pair_naturality (ofSubsetMap g hA) R
  rwa [ofSubsetMap_fst] at h

end OfSubset

/-- A map into the ambient space of a pair that factors through its subspace sends singular chains
to zero in the relative chains of the pair. -/
lemma chainComplexMap_comp_singularChainComplexπ_of_fac (P : TopPair.{w}) {Y : TopCat.{w}}
    (k : Y ⟶ P.fst) (g : Y ⟶ P.snd) (hg : g ≫ P.map = k) :
    SSet.chainComplexMap (TopCat.toSSet.map k) R ≫ P.singularChainComplexπFst R = 0 := by
  subst hg
  simp

/-- A map into `X` with range in `A` sends singular chains to zero in the chains of `X` relative
to `A`. -/
lemma chainComplexMap_comp_singularChainComplexπ_eq_zero_of_range_subset {X Z : TopCat.{w}}
    {A : Set X} {f : Z ⟶ X} (hf : Set.range f ⊆ A) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ (ofSubset A).singularChainComplexπ R = 0 :=
  chainComplexMap_comp_singularChainComplexπ_of_fac R (ofSubset A) f
    (TopCat.codRestrict f A fun z ↦ hf ⟨z, rfl⟩) (codRestrict_comp_ofSubset_map A _ _)

end Preadditive

variable [Abelian C]

section Fst

variable (P : TopPair.{w})

/-- The map from the singular homology of the ambient space `P.fst` of a pair to the relative
singular homology of the pair: `TopPair.singularHomologyπ`, with its source written as the
homology of `P.fst`, as in `TopPair.singularChainComplexπFst`. -/
noncomputable abbrev singularHomologyπFst (n : ℕ) :
    (TopCat.toSSet.obj P.fst).homology R n ⟶ P.singularHomology R n :=
  P.singularHomologyπ R n

lemma singularHomologyπFst_eq (n : ℕ) :
    P.singularHomologyπFst R n = P.singularHomologyπ R n :=
  (rfl)

/-- The map from the zeroth singular homology of `P.fst` to the zeroth relative singular homology
of `P` is an epimorphism. -/
instance epi_singularHomologyπFst_zero : Epi (P.singularHomologyπFst R 0) :=
  inferInstanceAs (Epi (P.singularHomologyπ R 0))

/-- The singular homology of the subspace of a pair vanishes in its relative singular homology. -/
@[reassoc]
lemma homologyMap_comp_singularHomologyπFst (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map P.map) R n ≫ P.singularHomologyπFst R n = 0 :=
  homologyMap_comp_singularHomologyπ P R n

variable {P} in
/-- The map from the singular homology of the ambient space to the relative singular homology is
natural in maps of pairs. -/
@[reassoc]
lemma singularHomologyπFst_naturality {Q : TopPair.{w}} (f : P ⟶ Q) (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R n ≫ Q.singularHomologyπFst R n =
      P.singularHomologyπFst R n ≫ TopPair.singularHomologyMap f R n :=
  singularHomologyπ_naturality f R n

/-- The map induced on homology by `TopPair.singularChainComplexπFst` is
`TopPair.singularHomologyπFst`. -/
lemma homologyMap_singularChainComplexπFst (n : ℕ) :
    HomologicalComplex.homologyMap (P.singularChainComplexπFst R) n =
      P.singularHomologyπFst R n :=
  (rfl)

end Fst

/-- Let `e : P ⟶ Q` be a map of pairs that induces an isomorphism in degree `n`, and `g` a chain
map from the chains of `K` to the relative chains of `P` that `e` sends to the image of the chains
of `K` under `f : K ⟶ Q.fst` in the relative chains of `Q`. Then the map induced by `g` is the map
induced by `f`, followed by `Hₙ(Q.fst) ⟶ Hₙ(Q)` and by the inverse of the map induced by `e`. -/
lemma homologyMap_eq_singularHomologyπ_comp_inv {P Q : TopPair.{w}} (e : P ⟶ Q) {K : SSet.{w}}
    (f : K ⟶ TopCat.toSSet.obj Q.fst) (g : K.chainComplex R ⟶ P.singularChainComplex R)
    (hg : g ≫ singularChainComplexMap e R =
      SSet.chainComplexMap f R ≫ Q.singularChainComplexπFst R) (n : ℕ)
    [IsIso (TopPair.singularHomologyMap e R n)] :
    HomologicalComplex.homologyMap g n =
      SSet.homologyMap f R n ≫ Q.singularHomologyπFst R n ≫
        inv (TopPair.singularHomologyMap e R n) := by
  rw [← Category.assoc, IsIso.eq_comp_inv, ← HomologicalComplex.homologyMap_comp, hg,
    HomologicalComplex.homologyMap_comp, homologyMap_singularChainComplexπFst]

/-- A map of pairs `(Y, B) ⟶ (X, S)` induced by a map `f : Y ⟶ X` whose range lies in `S` induces
zero on relative singular homology. -/
lemma singularHomologyMap_ofSubsetMap_eq_zero_of_range_subset {X Y : TopCat.{w}} {B : Set Y}
    {S : Set X} (f : Y ⟶ X) (h : Set.MapsTo f B S) (hf : Set.range f ⊆ S) (n : ℕ) :
    TopPair.singularHomologyMap (ofSubsetMap f h) R n = 0 :=
  singularHomologyMap_eq_zero_of_fac _ R (TopCat.codRestrict f S fun y ↦ hf ⟨y, rfl⟩)
    (by rw [ofSubsetMap_fst]; exact codRestrict_comp_ofSubset_map S f _) n

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
