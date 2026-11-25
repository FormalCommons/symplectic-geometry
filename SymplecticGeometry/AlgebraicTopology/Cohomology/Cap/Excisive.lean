/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# The cap product of an excisive couple

For subsets `U` and `V` of a space `X`, open in `U ∪ V`, this file defines the cap product

`Hᵖ(X, U; R, M) ⟶ (Hₙ(X, U ∪ V; T) ⟶ H_q(X, V; N))`,  `p + q = n`,

as `TopCat.singularRelativeCap`. Write `C(X; U + V)` for the chains of `X` relative to its
singular simplices lying in `U` or in `V`. Capping along Tau Ceti's relative Alexander–Whitney
diagonal `TopCat.relativeAlexanderWhitneyDiagonal U V u : C(X; U + V; T) ⟶ C(X, U; R) ⊗ C(X, V; S)`
with the chain map `M ⊗ C(X, V; S) ⟶ C(X, V; N)` of the pairing `μ : M ⊗ S ⟶ N` gives a cap
product `Hᵖ(X, U) ⟶ (Hₙ(C(X; U + V)) ⟶ H_q(X, V))`. The small-chain theorem identifies
`Hₙ(C(X; U + V))` with `Hₙ(X, U ∪ V)`
(`TopCat.isIso_homologyMap_smallSingularSubcomplexPairToUnion`), and the cap product is
precomposed with the inverse of this isomorphism.

The construction is the homological counterpart of Tau Ceti's relative cup product
`TopCat.singularRelativeCup` (`TauCeti/AlgebraicTopology/Cohomology/Cup/Relative.lean`), and the
proof of its naturality, `TopCat.singularRelativeCap_naturality`, adapts that of
`TopCat.singularRelativeCup_naturality`. The proof of the compatibility with the cap product of a
pair, `TopCat.singularCap_comp_singularHomologyπ`, follows that of Tau Ceti's
`TopPair.singularHomologyπ_comp_absoluteSingularCap` (`Cohomology/Cap/AbsoluteRelative.lean`): both
are `TauCeti.ChainComplex.cap_naturality` along a descent of the Alexander–Whitney diagonal. Here
the descent is that of the quotient map onto `C(X; U + V)` to the relative chains of `(X, U)`.

## Main definitions and results

* `TopCat.singularRelativeCap`: the cap product of an excisive couple, characterized by
  `TopCat.homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap`.
* `TopCat.homologyπ_homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap`: its
  value on the class of a cocycle and a class of cycles of `C(X; U + V)`.
* `TopCat.singularRelativeCap_naturality`: naturality in maps `f : X ⟶ Y` carrying `U` into `U'`
  and `V` into `V'`, the projection formula `f_*(y ⌢ f^*a) = f_*y ⌢ a`.
* `TopCat.singularCap_comp_singularHomologyπ`: compatibility with Tau Ceti's relative cap product
  `TopPair.singularCap : Hᵖ(X, U) ⊗ Hₙ(X, U) ⟶ H_q(X)`, `j_*(y ⌢ a) = j_*y ⌢ a`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product `Hₙ(X, A ∪ B) × Hᵖ(X, A) ⟶ H_{n - p}(X, B)`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
  (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C] {X Y : TopCat.{w}}

/-- **The cap product of an excisive couple** `Hᵖ(X, U; R, M) ⟶ (Hₙ(X, U ∪ V; T) ⟶ H_q(X, V; N))`
for subsets `U` and `V` of `X` which are open in `U ∪ V`, and `p + q = n`: the cap product along
the relative Alexander–Whitney diagonal `TopCat.relativeAlexanderWhitneyDiagonal U V u` and the
chain map of the pairing `μ : M ⊗ S ⟶ N` on the relative chains of `(X, V)`, defined on the
homology of the chains of `X` relative to its singular simplices lying in `U` or in `V`, composed
with the inverse of the small-chain isomorphism from that homology to the homology of
`(X, U ∪ V)`. It is `k`-linear in the cohomology class. -/
def singularRelativeCap (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset U).singularCohomology R k M p →ₗ[k]
      ((TopPair.ofSubset (U ∪ V)).singularHomology T n ⟶
        (TopPair.ofSubset V).singularHomology N q) :=
  have := isIso_homologyMap_smallSingularSubcomplexPairToUnion U V T hU hV n
  (Linear.leftComp k _
    (inv (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n))).comp
    (TauCeti.ChainComplex.cap k (relativeAlexanderWhitneyDiagonal U V u)
      ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ) p q n h)

/-- The cap product of an excisive couple is characterized by its composite with the small-chain
isomorphism: the cap product along the relative Alexander–Whitney diagonal. -/
@[reassoc (attr := simp)]
lemma homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap (u : T ⟶ R ⊗ S)
    (μ : M ⊗ S ⟶ N) (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M p) :
    SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n ≫
        singularRelativeCap k u μ U V hU hV p q n h a =
      TauCeti.ChainComplex.cap k (relativeAlexanderWhitneyDiagonal U V u)
        ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ) p q n h a := by
  have := isIso_homologyMap_smallSingularSubcomplexPairToUnion U V T hU hV n
  simp [singularRelativeCap]

/-- The cap product of an excisive couple on the class of a cocycle `φ` of `(X, U)` and a class of
cycles of the chains of `X` relative to its singular simplices lying in `U` or in `V`, sent to
`Hₙ(X, U ∪ V)` by the small-chain isomorphism, is the class of their cap product. -/
@[reassoc]
lemma homologyπ_homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (φ : ((TopPair.ofSubset U).singularCochainComplex R k M).cycles p) :
    ((X.smallSingularSubcomplex ![U, V]).pair.chainComplex T).homologyπ n ≫
        SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n ≫
          singularRelativeCap k u μ U V hU hV p q n h
            (((TopPair.ofSubset U).singularCochainComplex R k M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles k (relativeAlexanderWhitneyDiagonal U V u)
          ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ) p q n h φ ≫
        ((TopPair.ofSubset V).singularChainComplex N).homologyπ q := by
  rw [homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap]
  exact TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **Naturality of the cap product of an excisive couple**, the projection formula
`f_*(y ⌢ f^*a) = f_*y ⌢ a`: for a map `f : X ⟶ Y` carrying `U` into `U'` and `V` into `V'`,
capping with the pull-back of a class `a` of `Hᵖ(Y, U')` and pushing forward to `H_q(Y, V')` is
pushing forward to `Hₙ(Y, U' ∪ V')` and capping with `a`. -/
theorem singularRelativeCap_naturality (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) {U V : Set X}
    {U' V' : Set Y} (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (hU' : IsOpen ((↑) ⁻¹' U' : Set ↥(U' ∪ V')))
    (hV' : IsOpen ((↑) ⁻¹' V' : Set ↥(U' ∪ V'))) (f : X ⟶ Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U').singularCohomology R k M p) :
    singularRelativeCap k u μ U V hU hV p q n h
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap f hfU) p a) ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) N q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) T n ≫
        singularRelativeCap k u μ U' V' hU' hV' p q n h a := by
  have := isIso_homologyMap_smallSingularSubcomplexPairToUnion U V T hU hV n
  -- The small-chain isomorphisms are natural in `f`.
  have hc : SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n ≫
      TopPair.singularHomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) T n =
      SSetPair.homologyMap (smallSingularSubcomplexPairMap f hfU hfV) T n ≫
        SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U' V') T n := by
    rw [TopPair.singularHomologyMap, ← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp,
      smallSingularSubcomplexPairToUnion_comp_ofSubsetMap]
  rw [← cancel_epi (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n),
    homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap_assoc, reassoc_of% hc,
    homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap]
  exact TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (relativeAlexanderWhitneyDiagonal_naturality f hfU hfV u)
    (SSetPair.chainComplexPairing_naturality
      (TopPair.toSSetPair.map (TopPair.ofSubsetMap f hfV)) μ).symm p q n h a

section Compatibility

/-- The quotient map from the chains of `X` to its chains relative to the singular simplices lying
in `U` or in `V`, descended to the relative chains of `(X, U)`. -/
private def singularChainComplexOfSubsetToSmall (U V : Set X) (R : C) :
    (TopPair.ofSubset U).singularChainComplex R ⟶
      (X.smallSingularSubcomplex ![U, V]).pair.chainComplex R :=
  (CokernelCofork.IsColimit.desc'
    ((TopPair.ofSubset U).isColimitCokernelCoforkSingularChainComplex R)
    (smallSingularSubcomplexπ ![U, V] R)
    (by
      rw [TopPair.toSSetPair_obj_hom]
      exact chainComplexMap_comp_smallSingularSubcomplexπ ![U, V] (i := 0)
        TopPair.range_ofSubset_map.subset R)).val

omit [MonoidalCategory C] [MonoidalPreadditive C] in
@[reassoc]
private lemma singularChainComplexπOfSubset_singularChainComplexOfSubsetToSmall (U V : Set X)
    (R : C) :
    TopPair.singularChainComplexπOfSubset R U ≫ singularChainComplexOfSubsetToSmall U V R =
      smallSingularSubcomplexπ ![U, V] R :=
  (CokernelCofork.IsColimit.desc'
    ((TopPair.ofSubset U).isColimitCokernelCoforkSingularChainComplex R) _ _).property

/-- **Compatibility with the relative cap product of a pair**, `j_*(y ⌢ a) = j_*y ⌢ a`: for a class
`a` of `Hᵖ(X, U)` and a class `y` of `Hₙ(X, U)`, the image in `H_q(X, V)` of the relative cap
product `y ⌢ a ∈ H_q(X)` (`TopPair.singularCap`) is the cap product of the excisive couple of `a`
with the image of `y` in `Hₙ(X, U ∪ V)`. -/
theorem singularCap_comp_singularHomologyπ (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n) (a : (TopPair.ofSubset U).singularCohomology R k M p) :
    (TopPair.ofSubset U).singularCap k u μ p q n h a ≫
        (TopPair.ofSubset V).singularHomologyπ N q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n ≫
        singularRelativeCap k u μ U V hU hV p q n h a := by
  -- The map `Hₙ(X, U) ⟶ Hₙ(X, U ∪ V)` factors through the small-chain quotient.
  have hj : singularChainComplexOfSubsetToSmall U V T ≫
      SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) T =
      TopPair.singularChainComplexMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T := by
    rw [← cancel_epi (TopPair.singularChainComplexπOfSubset T U),
      singularChainComplexπOfSubset_singularChainComplexOfSubsetToSmall_assoc,
      smallSingularSubcomplexπ_comp_chainComplexMap_smallSingularSubcomplexPairToUnion]
    refine Eq.trans ?_ (TopPair.singularChainComplexπOfSubset_naturality T (𝟙 X) _)
    simp
  have hD : singularChainComplexOfSubsetToSmall U V T ≫ relativeAlexanderWhitneyDiagonal U V u =
      (TopPair.ofSubset U).alexanderWhitneyDiagonal u ≫
        HomologicalComplex.tensorHom (𝟙 _) (TopPair.singularChainComplexπOfSubset S V) := by
    rw [← cancel_epi (TopPair.singularChainComplexπOfSubset T U),
      singularChainComplexπOfSubset_singularChainComplexOfSubsetToSmall_assoc,
      smallSingularSubcomplexπ_relativeAlexanderWhitneyDiagonal]
    refine Eq.trans ?_ (TopPair.singularChainComplexπ_alexanderWhitneyDiagonal_assoc
      (TopPair.ofSubset U) u _).symm
    have hπ := HomologicalComplex.mapBifunctorMap_comp (curriedTensor C) (ComplexShape.down ℕ)
      (TopPair.singularChainComplexπOfSubset R U) (𝟙 _) (𝟙 _)
      (TopPair.singularChainComplexπOfSubset S V)
    rw [Category.comp_id, Category.id_comp] at hπ
    -- The whiskering on the right is `HomologicalComplex.tensorHom f (𝟙 _)` by definition.
    exact (congrArg (X.alexanderWhitneyDiagonal u ≫ ·) hπ).trans (Category.assoc _ _ _).symm
  have := TauCeti.ChainComplex.cap_naturality (k := k) (relativeAlexanderWhitneyDiagonal U V u)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ)
    ((TopPair.ofSubset U).alexanderWhitneyDiagonal u) ((toSSet.obj X).chainComplexPairing μ)
    (singularChainComplexOfSubsetToSmall U V T) (𝟙 _) (TopPair.singularChainComplexπOfSubset S V)
    (TopPair.singularChainComplexπOfSubset N V) hD
    (SSetPair.chainComplexπ_chainComplexPairing
      (TopPair.toSSetPair.obj (TopPair.ofSubset V)) μ).symm p q n h a
  have hid : HomologicalComplex.homologyMap
      (K := ((TopPair.ofSubset U).singularChainComplex R).linearYonedaObj k M)
      (L := ((TopPair.ofSubset U).singularChainComplex R).linearYonedaObj k M)
      ((TauCeti.ChainComplex.linearYonedaFunctor k M).map (𝟙 _).op) p = 𝟙 _ := by
    rw [op_id, CategoryTheory.Functor.map_id]
    exact HomologicalComplex.homologyMap_id _ _
  rw [hid, ModuleCat.id_apply] at this
  have hH : homologyMap (singularChainComplexOfSubsetToSmall U V T) n ≫
      SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n :=
    (homologyMap_comp _ _ _).symm.trans (congrArg (homologyMap · n) hj)
  rw [← hH, Category.assoc, homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap,
    TopPair.singularCap_def]
  -- `TopPair.singularCap` and `TopPair.singularHomologyπ` are, by definition, the cap product
  -- and the map on homology that `this` states its identity with.
  exact this

end Compatibility

end TopCat
