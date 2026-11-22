/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import SymplecticGeometry.AlgebraicTopology.Cohomology.EvenIntegralCohomology

/-!
# Cup products of classes vanishing on the sets of an open cover

Let `X = U ∪ V` with `U` and `V` open. If a class `a` restricts to zero on `U` and a class `b`
restricts to zero on `V`, then `a ⌣ b = 0`. By the long exact sequences of the pairs `(X, U)` and
`(X, V)`, the classes come from `H*(X, U)` and `H*(X, V)`; their relative cup product
(`TopCat.singularRelativeCup` of Tau Ceti) lies in `H*(X, U ∪ V) = H*(X, X)` and maps to `a ⌣ b`,
and the map `H*(X, X) → H*(X)` vanishes.

The argument is that of Tau Ceti's `IsPositiveDegreeCupProduct.exists_singularCohomologyπ_eq` and
`lsCupLength_add_one_le_lsCategoryCount_univ`, for two open sets on which the classes vanish
instead of open sets with nullhomotopic inclusions.

## Main results

* `TopCat.singularCup_eq_zero_of_union_eq_univ`: the statement for the singular cup product, with
  any coefficients.
* `TopCat.evenIntegralCohomology_mul_eq_zero_of_union_eq_univ`: the statement for the product of
  the even integral cohomology ring.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.2 (the relative cup
  product `Hᵏ(X, A) × Hˡ(X, B) → Hᵏ⁺ˡ(X, A ∪ B)` for open `A` and `B`).
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopCat

section Singular

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}
  (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X : TopCat.{w}}

/-- **The cup product of classes vanishing on an open cover vanishes.** If `X = U ∪ V` with `U`
and `V` open, `a` restricts to zero on `U` and `b` restricts to zero on `V`, then `a ⌣ b = 0`. -/
theorem singularCup_eq_zero_of_union_eq_univ (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) {p q n : ℕ} (h : p + q = n)
    {a : X.singularCohomology R k M p} {b : X.singularCohomology S k N q}
    (ha : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) p a = 0)
    (hb : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) q b = 0) :
    X.singularCup k u μ p q n h a b = 0 := by
  -- A class restricting to zero on `A` comes from the cohomology of `(X, A)`.
  have lift (A : Set X) {R' M' : C} {m : ℕ} (c : X.singularCohomology R' k M' m)
      (hc : TopCat.singularCohomologyMap (ofHom (ContinuousMap.subtypeVal A)) m c = 0) :
      ∃ z, (TopPair.ofSubset A).singularCohomologyπ R' k M' m z = c :=
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((TopPair.ofSubset A).singularCohomology_exact_space R' k M' m) c).1
      (by
        -- The second map of the exact sequence is the pull-back along `(ofSubset A).map`.
        change TopCat.singularCohomologyMap (TopPair.ofSubset A).map m c = 0
        rwa [TopPair.ofSubset_map])
  obtain ⟨a', rfl⟩ := lift U a ha
  obtain ⟨b', rfl⟩ := lift V b hb
  rw [← singularCohomologyπ_singularRelativeCup k u μ U V (hU.preimage continuous_subtypeVal)
    (hV.preimage continuous_subtypeVal) p q n h a' b']
  generalize singularRelativeCup k u μ U V _ _ p q n h a' b' = z
  revert z
  rw [hUV]
  intro z
  exact ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_ofSubset_univ X n) z

end Singular

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

/-- **The product of classes vanishing on an open cover vanishes**, in the even integral
cohomology ring: if `X = U ∪ V` with `U` and `V` open, `a` restricts to zero on `U` and `b`
restricts to zero on `V`, then `a * b = 0`. -/
theorem evenIntegralCohomology_mul_eq_zero_of_union_eq_univ {X : TopCat.{0}} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) {a b : X.EvenIntegralCohomology}
    (ha : evenIntegralCohomologyMap (ofHom (ContinuousMap.subtypeVal U)) a = 0)
    (hb : evenIntegralCohomologyMap (ofHom (ContinuousMap.subtypeVal V)) b = 0) :
    a * b = 0 := by
  classical
  rw [← DirectSum.sum_support_of a, ← DirectSum.sum_support_of b, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  have ha' := congrArg (· i) ha
  have hb' := congrArg (· j) hb
  simp only [evenIntegralCohomologyMap_apply, DirectSum.zero_apply] at ha' hb'
  rw [evenIntegralCohomologyOf_mul, integralCup_def,
    singularCup_eq_zero_of_union_eq_univ ℤ _ _ hU hV hUV _ ha' hb', map_zero]

end TopCat

end
