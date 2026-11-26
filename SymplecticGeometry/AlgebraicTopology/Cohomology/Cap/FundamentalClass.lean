/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Cohomology.Cap.Excisive
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass

/-!
# Push-forwards of cap products that are fundamental classes

Let `p : E ⟶ Z` be a map, `U ⊆ E` open, `a ∈ Hʳ(E, U)` and `γ ∈ Hₙ(E, U)`, `r + q = n`. The
push-forward `p_*(γ ⌢ a) ∈ H_q(Z)` of the relative cap product (Tau Ceti's `TopPair.singularCap`)
can be read in the local homology `H_q(Z, Z ∖ {z})` through the cap product of the excisive couple
`(U, p⁻¹(Z ∖ {z}))` (`TopCat.singularRelativeCap`): the image of `p_*(γ ⌢ a)` there is
`p_*(γ_z ⌢ a)`, where `γ_z` is the image of `γ` in `Hₙ(E, U ∪ p⁻¹(Z ∖ {z}))`. So if `Z` is a
compact oriented manifold of dimension `q` and `p_*(γ_z ⌢ a)` is the local orientation at `z` for
every `z`, then `p_*(γ ⌢ a)` is the fundamental class of `Z`, by Tau Ceti's
`TauCeti.HomologicalOrientation.eq_fundamentalClass`. No bundle structure is needed. For a vector
bundle with `U` the complement of the zero section, `γ ↦ p_*(γ ⌢ a)` is, up to the change of
coefficients, Tau Ceti's homology Thom map `TauCeti.homologyThomMap`.

## Main results

* `TopCat.singularCap_comp_map_comp_singularHomologyπ`: for `V ⊆ E` carried by `p` into `S ⊆ Z`,
  the image of `p_*(γ ⌢ a)` in `H_q(Z, S)` is the push-forward of the cap product of the excisive
  couple `(U, V)` of `a` with the image of `γ` in `Hₙ(E, U ∪ V)`.
* `TauCeti.singularHomologyToLocalHomology_singularCap_comp_map`: its case `V = p⁻¹(Z ∖ {z})`,
  `S = Z ∖ {z}`, read in the local homology of `Z` at `z`.
* `TauCeti.HomologicalOrientation.singularCap_comp_map_apply_eq_fundamentalClass`: the pointwise
  criterion for `p_*(γ ⌢ a)` to be the fundamental class `o.fundamentalClass hm` of `Z`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product `Hₙ(X, A ∪ B) × Hᵖ(X, A) ⟶ H_{n - p}(X, B)` and
  Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
  (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C] {X Y : TopCat.{w}}

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

end TopCat

namespace TauCeti

section LocalHomology

variable {Λ : Type w} [CommRing Λ] {R S T M : ModuleCat.{w} Λ} {N : ModuleCat.{w} Λ}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{w} Λ)] [MonoidalLinear k (ModuleCat.{w} Λ)]
  {Z : Type w} [TopologicalSpace Z] [T1Space Z] {E : TopCat.{w}} (p : E ⟶ TopCat.of Z)
  {U : Set E}

/-- **The push-forward of a relative cap product in local homology.** For a map `p : E ⟶ Z` to a
`T₁` space, an open set `U ⊆ E`, a class `a ∈ Hʳ(E, U)`, `γ ∈ Hₙ(E, U)` and a point `z` of `Z`,
the image of `p_*(γ ⌢ a) ∈ H_q(Z)` in the local homology `H_q(Z, Z ∖ {z})` is `p_*(γ_z ⌢ a)`,
where `γ_z` is the image of `γ` in `Hₙ(E, U ∪ p⁻¹(Z ∖ {z}))` and the cap product is that of the
excisive couple `(U, p⁻¹(Z ∖ {z}))`, with values in `H_q(E, p⁻¹(Z ∖ {z}))`. -/
theorem singularHomologyToLocalHomology_singularCap_comp_map (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N)
    (hU : IsOpen U) (z : Z) (r q n : ℕ) (h : r + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M r)
    (γ : ((TopPair.ofSubset U).singularHomology T n : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N z q
        (((TopPair.ofSubset U).singularCap k u μ r q n h a ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) q).obj N).map p) γ) =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap p (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z)))) N q
        (TopCat.singularRelativeCap k u μ U (p ⁻¹' {z}ᶜ) (hU.preimage continuous_subtypeVal)
          ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
          r q n h a
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) fun _ hx ↦ Or.inl hx) T n
            γ)) := by
  have hc := TopCat.singularCap_comp_map_comp_singularHomologyπ k u μ p
    (hU.preimage continuous_subtypeVal)
    ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
    (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z))) r q n h a
  -- The map to local homology at `z` factors through the quotient map to `H_q(Z, Z ∖ {z})`.
  have hπ := TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id N
    (X := TopCat.of Z) (S := ({z}ᶜ : Set (TopCat.of Z))) (S' := Set.univᶜ)
    (Set.compl_subset_compl.2 (Set.subset_univ {z})) q
  have hmor : ((TopPair.ofSubset U).singularCap k u μ r q n h a ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) q).obj N).map p) ≫
        (TopPair.ofSubset (Set.univᶜ : Set (TopCat.of Z))).singularHomologyπ N q ≫
          localHomologyRestriction N (Set.subset_univ {z}) q =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) fun _ hx ↦ Or.inl hx) T n ≫
        TopCat.singularRelativeCap k u μ U (p ⁻¹' {z}ᶜ) (hU.preimage continuous_subtypeVal)
          ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
          r q n h a ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap p (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z)))) N q := by
    rw [localHomologyRestriction_def]
    exact (congrArg (_ ≫ ·) hπ).trans ((Category.assoc _ _ _).trans hc)
  exact (singularHomologyToLocalHomology_apply N z _).trans (ConcreteCategory.congr_hom hmor γ)

end LocalHomology

/-- **A push-forward of a cap product is the fundamental class if it is so locally.** Let `Z` be a
compact Hausdorff manifold of dimension `m` with a homological orientation `o`, `p : E ⟶ Z` a map,
`U ⊆ E` open, `a ∈ Hʳ(E, U)` and `γ ∈ Hₙ(E, U)`, `r + m = n`, with homology coefficients `ULift ℤ`.
If for every `z : Z` the push-forward of the cap product of the excisive couple
`(U, p⁻¹(Z ∖ {z}))` of `a` with the image of `γ` in `Hₙ(E, U ∪ p⁻¹(Z ∖ {z}))` is the local
orientation `o z`, then `p_*(γ ⌢ a) ∈ H_m(Z)` is the fundamental class of `o`. -/
theorem HomologicalOrientation.singularCap_comp_map_apply_eq_fundamentalClass
    {R S T M : ModuleCat.{0} ℤ}
    [∀ J : Type, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]
    (k : Type*) [Ring k] [Linear k (ModuleCat.{0} ℤ)] [MonoidalLinear k (ModuleCat.{0} ℤ)]
    {Z F : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ChartedSpace F Z] {m : ℕ}
    (o : HomologicalOrientation Z F m) (hm : Module.finrank ℝ F = m) {E : TopCat.{0}}
    (p : E ⟶ TopCat.of Z) (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ ModuleCat.of ℤ (ULift.{0} ℤ)) {U : Set E}
    (hU : IsOpen U) (r n : ℕ) (h : r + m = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M r)
    (γ : ((TopPair.ofSubset U).singularHomology T n : ModuleCat.{0} ℤ))
    (hγ : ∀ z : Z, TopPair.singularHomologyMap
        (TopPair.ofSubsetMap p (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z))))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) m
        (TopCat.singularRelativeCap k u μ U (p ⁻¹' {z}ᶜ) (hU.preimage continuous_subtypeVal)
          ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
          r m n h a
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) fun _ hx ↦ Or.inl hx) T n
            γ)) =
        (o z).val) :
    ((TopPair.ofSubset U).singularCap k u μ r m n h a ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
          (ModuleCat.of ℤ (ULift.{0} ℤ))).map p) γ = o.fundamentalClass hm :=
  o.eq_fundamentalClass hm fun z ↦
    (singularHomologyToLocalHomology_singularCap_comp_map k p u μ hU z r m n h a γ).trans (hγ z)

end TauCeti

end
