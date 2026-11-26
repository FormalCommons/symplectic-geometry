/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing
import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing
import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing.FromTauCeti
import SymplecticGeometry.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup

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
pair, `TopCat.singularCap_comp_singularHomologyπ_eq_singularRelativeCap`, follows that of Tau
Ceti's `TopPair.singularHomologyπ_comp_absoluteSingularCap`
(`Cohomology/Cap/AbsoluteRelative.lean`): both are `TauCeti.ChainComplex.cap_naturality` along a
descent of the Alexander–Whitney diagonal. Here the descent is along the chain map of
`TopCat.toSmallSingularSubcomplexPair`, from the relative chains of `(X, U)` to `C(X; U + V)`.

## Main definitions and results

* `TopCat.singularRelativeCap`: the cap product of an excisive couple, characterized by
  `TopCat.homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap`.
* `TopCat.homologyπ_homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap`: its
  value on the class of a cocycle and a class of cycles of `C(X; U + V)`.
* `TopCat.singularRelativeCap_naturality`: naturality in maps `f : X ⟶ Y` carrying `U` into `U'`
  and `V` into `V'`, the projection formula `f_*(y ⌢ f^*a) = f_*y ⌢ a`.
* `TopCat.singularCap_comp_singularHomologyπ_eq_singularRelativeCap`: compatibility with Tau Ceti's
  relative cap product `TopPair.singularCap : Hᵖ(X, U) ⊗ Hₙ(X, U) ⟶ H_q(X)`,
  `j_*(y ⌢ a) = j_*y ⌢ a`.
* `TopCat.singularCap_comp_map_comp_singularHomologyπ`: the same after a push-forward along a map
  `f : X ⟶ Y` carrying `V` into `S' ⊆ Y`: the image in `H_q(Y, S')` of `f_*(y ⌢ a)` is
  `f_*(j_*y ⌢ a)`.
* `TopCat.singularRelativeCap_comp_singularKronecker`: the Kronecker pairing of the cap product,
  `⟨c, y ⌢ a⟩ = ⟨a ⌣ c, y⟩` for a class `a` with values in the tensor unit, with Tau Ceti's
  relative cup product `TopCat.singularRelativeCup`.
* `TopCat.singularRelativeCap_coefficient_naturality`: compatible changes of the coefficient objects
  `R`, `S`, `T`, `M` and `N` commute with the cap product.

The proof of the Kronecker pairing adapts that of Tau Ceti's
`TopPair.singularCap_comp_singularKronecker` (`Cohomology/Cap/Kronecker.lean`): after cancelling
the small-chain isomorphism, it is `TauCeti.ChainComplex.cap_comp_kronecker` on the chains
`C(X; U + V)`, with the relative form `SSetPair.chainComplexPairing_leftUnitor_hom_f` of the action
of the tensor unit on the chains of `(X, V)`.

The proof of the coefficient naturality adapts that of Tau Ceti's
`TopPair.singularCap_coefficient_naturality` (`Cohomology/Cap/Relative.lean`): it is
`TauCeti.ChainComplex.cap_coefficient_naturality` on the chains `C(X; U + V)`, after cancelling
the small-chain isomorphism, which commutes with the change of chain coefficients, and uses the
coefficient naturality of the pairing on relative chains
(`SimplicialSet/Homology/Relative/Pairing.lean`).

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

/-- **Compatibility with the relative cap product of a pair**, `j_*(y ⌢ a) = j_*y ⌢ a`: for a class
`a` of `Hᵖ(X, U)` and a class `y` of `Hₙ(X, U)`, the image in `H_q(X, V)` of the relative cap
product `y ⌢ a ∈ H_q(X)` (`TopPair.singularCap`) is the cap product of the excisive couple of `a`
with the image of `y` in `Hₙ(X, U ∪ V)`. -/
theorem singularCap_comp_singularHomologyπ_eq_singularRelativeCap (u : T ⟶ R ⊗ S)
    (μ : M ⊗ S ⟶ N) (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M p) :
    (TopPair.ofSubset U).singularCap k u μ p q n h a ≫
        (TopPair.ofSubset V).singularHomologyπ N q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n ≫
        singularRelativeCap k u μ U V hU hV p q n h a := by
  have := TauCeti.ChainComplex.cap_naturality (k := k) (relativeAlexanderWhitneyDiagonal U V u)
    ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ)
    ((TopPair.ofSubset U).alexanderWhitneyDiagonal u) ((toSSet.obj X).chainComplexPairing μ)
    (SSetPair.chainComplexMap
      (toSmallSingularSubcomplexPair ![U, V] (A := U) (i := 0) subset_rfl) T)
    (𝟙 _) (TopPair.singularChainComplexπOfSubset S V) (TopPair.singularChainComplexπOfSubset N V)
    (chainComplexMap_toSmallSingularSubcomplexPair_relativeAlexanderWhitneyDiagonal U V u)
    (SSetPair.chainComplexπ_chainComplexPairing
      (TopPair.toSSetPair.obj (TopPair.ofSubset V)) μ).symm p q n h a
  have hid : HomologicalComplex.homologyMap
      (K := ((TopPair.ofSubset U).singularChainComplex R).linearYonedaObj k M)
      (L := ((TopPair.ofSubset U).singularChainComplex R).linearYonedaObj k M)
      ((TauCeti.ChainComplex.linearYonedaFunctor k M).map (𝟙 _).op) p = 𝟙 _ := by
    rw [op_id, CategoryTheory.Functor.map_id]
    exact HomologicalComplex.homologyMap_id _ _
  rw [hid, ModuleCat.id_apply] at this
  -- The map `Hₙ(X, U) ⟶ Hₙ(X, U ∪ V)` factors through the small-chain quotient.
  have hH : SSetPair.homologyMap
      (toSmallSingularSubcomplexPair ![U, V] (A := U) (i := 0) subset_rfl) T n ≫
      SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n :=
    (homologyMap_comp _ _ _).symm.trans (congrArg (homologyMap · n)
      (chainComplexMap_toSmallSingularSubcomplexPair_comp_smallSingularSubcomplexPairToUnion U V T))
  rw [← hH, Category.assoc, homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap,
    TopPair.singularCap_def]
  -- `TopPair.singularCap` and `TopPair.singularHomologyπ` are, by definition, the cap product
  -- and the map on homology that `this` states its identity with.
  exact this

/-- **The push-forward of a relative cap product, read relative to a subset of the target.** For a
map `f : X ⟶ Y` carrying `V ⊆ X` into `S' ⊆ Y`, with `U` and `V` open in `U ∪ V`, a class
`a ∈ Hᵖ(X, U)` and `γ ∈ Hₙ(X, U)`, the image in `H_q(Y, S')` of `f_*(γ ⌢ a) ∈ H_q(Y)` is
`f_*(γ' ⌢ a)`, where `γ'` is the image of `γ` in `Hₙ(X, U ∪ V)` and the cap product is that of the
excisive couple `(U, V)`. -/
@[reassoc]
theorem singularCap_comp_map_comp_singularHomologyπ (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N) (f : X ⟶ Y)
    {U V : Set X} {S' : Set Y} (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (hfV : Set.MapsTo f V S') (p q n : ℕ)
    (h : p + q = n) (a : (TopPair.ofSubset U).singularCohomology R k M p) :
    (TopPair.ofSubset U).singularCap k u μ p q n h a ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj N).map f ≫
          (TopPair.ofSubset S').singularHomologyπ N q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n ≫
        singularRelativeCap k u μ U V hU hV p q n h a ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) N q := by
  -- Pushing forward along `f` and passing to `H_q(Y, S')` is passing to `H_q(X, V)` and pushing
  -- forward along the map of pairs.
  have hπ := TopPair.singularHomologyπ_naturality (TopPair.ofSubsetMap f hfV) N q
  rw [TopPair.ofSubsetMap_fst] at hπ
  have key : (TopPair.ofSubset U).singularCap k u μ p q n h a ≫
      (TopPair.ofSubset V).singularHomologyπ N q ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) N q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 X) fun _ hx ↦ Or.inl hx) T n ≫
        singularRelativeCap k u μ U V hU hV p q n h a ≫
          TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) N q :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap f hfV) N q)
        (singularCap_comp_singularHomologyπ_eq_singularRelativeCap k u μ U V hU hV p q n h a)).trans
        (Category.assoc _ _ _))
  exact (congrArg (fun g ↦ (TopPair.ofSubset U).singularCap k u μ p q n h a ≫ g ≫
    (TopPair.ofSubset S').singularHomologyπ N q)
      (TauCeti.singularHomologyFunctor_obj_map N q f)).trans
    ((congrArg ((TopPair.ofSubset U).singularCap k u μ p q n h a ≫ ·) hπ).trans key)

section Coefficients

variable {R' S' T' M' N' : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M')]

/-- **Coefficient naturality of the cap product of an excisive couple**: if
`c ≫ u = u' ≫ (a ⊗ b)` and `(v ▷ S') ≫ μ' = (M ◁ b) ≫ μ ≫ e`, then capping along `(u', μ')` with
the class obtained from `α ∈ Hᵖ(X, U; R, M)` by pulling relative cochains back along `a` and
pushing their values forward along `v` is changing the coefficients of `Hₙ(X, U ∪ V)` along `c`,
capping with `α` along `(u, μ)`, and changing the coefficients of `H_q(X, V)` along `e`. -/
theorem singularRelativeCap_coefficient_naturality (u : T ⟶ R ⊗ S) (u' : T' ⟶ R' ⊗ S')
    (μ : M ⊗ S ⟶ N) (μ' : M' ⊗ S' ⟶ N') (a : R' ⟶ R) (b : S' ⟶ S) (c : T' ⟶ T) (v : M ⟶ M')
    (e : N ⟶ N') (hu : c ≫ u = u' ≫ (a ⊗ₘ b)) (hμ : (v ▷ S') ≫ μ' = (M ◁ b) ≫ μ ≫ e)
    (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (α : (TopPair.ofSubset U).singularCohomology R k M p) :
    singularRelativeCap k u' μ' U V hU hV p q n h
        (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
          (((SSetPair.chainComplexFunctor C).map a).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset U))).op ≫
            ((TopPair.ofSubset U).singularChainComplex R').linearYonedaObjMap k v) p α) =
      homologyMap (((SSetPair.chainComplexFunctor C).map c).app
          (TopPair.toSSetPair.obj (TopPair.ofSubset (U ∪ V)))) n ≫
        singularRelativeCap k u μ U V hU hV p q n h α ≫
          homologyMap (((SSetPair.chainComplexFunctor C).map e).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset V))) q := by
  have := isIso_homologyMap_smallSingularSubcomplexPairToUnion U V T' hU hV n
  -- The small-chain isomorphisms commute with the change of chain coefficients along `c`.
  rw [← cancel_epi (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T' n),
    homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap,
    ← SSetPair.homologyMap_coefficient_naturality_assoc,
    homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap_assoc]
  -- The action square of the coefficient pairings on the relative chains of `(X, V)`.
  have ha : (NatTrans.mapHomologicalComplex ((tensoringLeft C).map v) _).app
        ((TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplex S') ≫
        (TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ' =
      ((tensorLeft M).mapHomologicalComplex _).map
          (((SSetPair.chainComplexFunctor C).map b).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset V))) ≫
        (TopPair.toSSetPair.obj (TopPair.ofSubset V)).chainComplexPairing μ ≫
          ((SSetPair.chainComplexFunctor C).map e).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset V)) := by
    rw [SSetPair.whiskerRight_comp_chainComplexPairing,
      SSetPair.chainComplexPairing_comp_chainComplexFunctor_map_app,
      SSetPair.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing, hμ]
  exact TauCeti.ChainComplex.cap_coefficient_naturality _ _ _ _ _ _ _ v _
    (relativeAlexanderWhitneyDiagonal_coefficient_naturality U V u u' a b c hu)
    (fun j ↦ congrArg (fun f ↦ f.f j) ha) p q n h α

end Coefficients

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))]
  (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X : TopCat.{w}}

/-- **The Kronecker pairing of the cap product of an excisive couple**, `⟨c, y ⌢ a⟩ = ⟨a ⌣ c, y⟩`:
for subsets `U` and `V` of `X`, open in `U ∪ V`, a class `a ∈ Hᵖ(X, U; R, 𝟙)` with values in the
tensor unit and a class `c ∈ H^q(X, V; S, N)`, capping a class `y ∈ Hₙ(X, U ∪ V; T)`, `n = p + q`,
with `a` along `u` and the left unitor of `S`, and then evaluating `c`, is evaluating on `y` the
relative cup product `a ⌣ c ∈ Hⁿ(X, U ∪ V; T, N)` along `u` and the left unitor of `N`. -/
theorem singularRelativeCap_comp_singularKronecker (u : T ⟶ R ⊗ S) (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n) (a : (TopPair.ofSubset U).singularCohomology R k (𝟙_ C) p)
    (c : (TopPair.ofSubset V).singularCohomology S k N q) :
    singularRelativeCap k u (λ_ S).hom U V hU hV p q n h a ≫
        (TopPair.ofSubset V).singularKronecker k q c =
      (TopPair.ofSubset (U ∪ V)).singularKronecker k n
        (singularRelativeCup k u (λ_ N).hom U V hU hV p q n h a c) := by
  have := isIso_homologyMap_smallSingularSubcomplexPairToUnion U V T hU hV n
  rw [← cancel_epi (SSetPair.homologyMap (smallSingularSubcomplexPairToUnion U V) T n),
    homologyMap_smallSingularSubcomplexPairToUnion_singularRelativeCap_assoc]
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q c
  rw [TopPair.singularKronecker_def, TopPair.singularKronecker_def, SSetPair.homologyMap,
    ← TauCeti.ChainComplex.kronecker_naturality, ← SSetPair.cochainComplexMap,
    homologyMap_cochainComplexMap_singularRelativeCup]
  refine TauCeti.ChainComplex.cap_comp_kronecker _ _ _ p q n h φ ψ ψ ?_
  rw [SSetPair.chainComplexPairing_leftUnitor_hom_f]
  exact (leftUnitor_naturality _).symm

end Kronecker

end TopCat
