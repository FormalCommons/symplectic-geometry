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

* `TauCeti.singularHomologyToLocalHomology_map_singularCap`: the image of `p_*(γ ⌢ a)` in the
  local homology of `Z` at `z` is `p_*(γ_z ⌢ a)`. It is the case `V = p⁻¹(Z ∖ {z})`,
  `S' = Z ∖ {z}` of `TopCat.singularCap_comp_map_comp_singularHomologyπ`
  (`Cohomology/Cap/Excisive.lean`).
* `TauCeti.HomologicalOrientation.map_singularCap_eq_fundamentalClass`: the pointwise
  criterion for `p_*(γ ⌢ a)` to be the fundamental class `o.fundamentalClass hm` of `Z`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product `Hₙ(X, A ∪ B) × Hᵖ(X, A) ⟶ H_{n - p}(X, B)` and
  Lemma 3.27.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w

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
theorem singularHomologyToLocalHomology_map_singularCap (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N)
    (hU : IsOpen U) (z : Z) (r q n : ℕ) (h : r + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M r)
    (γ : ((TopPair.ofSubset U).singularHomology T n : ModuleCat.{w} Λ)) :
    singularHomologyToLocalHomology N z q
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} Λ) q).obj N).map p
          ((TopPair.ofSubset U).singularCap k u μ r q n h a γ)) =
      TopPair.singularHomologyMap
        (TopPair.ofSubsetMap p (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z)))) N q
        (TopCat.singularRelativeCap k u μ U (p ⁻¹' {z}ᶜ) (hU.preimage continuous_subtypeVal)
          ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
          r q n h a
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) fun _ hx ↦ Or.inl hx) T n
            γ)) := by
  have hc := ConcreteCategory.congr_hom (TopCat.singularCap_comp_map_comp_singularHomologyπ k u μ p
    (hU.preimage continuous_subtypeVal)
    ((isOpen_compl_singleton.preimage p.hom.continuous).preimage continuous_subtypeVal)
    (Set.mapsTo_preimage p ({z}ᶜ : Set (TopCat.of Z))) r q n h a) γ
  simp only [ConcreteCategory.comp_apply] at hc
  exact (singularHomologyToLocalHomology_eq_singularHomologyπ N z _).trans hc

end LocalHomology

/-- **A push-forward of a cap product is the fundamental class if it is so locally.** Let `Z` be a
compact Hausdorff manifold of dimension `m` with a homological orientation `o`, `p : E ⟶ Z` a map,
`U ⊆ E` open, `a ∈ Hʳ(E, U)` and `γ ∈ Hₙ(E, U)`, `r + m = n`, where `a` and `γ` have any
coefficients and the pairing `μ` takes values in `ULift ℤ`, so that `p_*(γ ⌢ a) ∈ H_m(Z; ULift ℤ)`.
If for every `z : Z` the push-forward of the cap product of the excisive couple
`(U, p⁻¹(Z ∖ {z}))` of `a` with the image of `γ` in `Hₙ(E, U ∪ p⁻¹(Z ∖ {z}))` is the local
orientation `o z`, then `p_*(γ ⌢ a)` is the fundamental class of `o`. -/
theorem HomologicalOrientation.map_singularCap_eq_fundamentalClass
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
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) m).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map p
      ((TopPair.ofSubset U).singularCap k u μ r m n h a γ) = o.fundamentalClass hm :=
  o.eq_fundamentalClass hm fun z ↦
    (singularHomologyToLocalHomology_map_singularCap k p u μ hU z r m n h a γ).trans (hγ z)

end TauCeti

end
