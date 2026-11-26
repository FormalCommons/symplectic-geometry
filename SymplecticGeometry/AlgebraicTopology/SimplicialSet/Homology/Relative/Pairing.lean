/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# Coefficient pairings on relative simplicial chains: change of coefficients

For a pair of simplicial sets `P`, this file shows that the chain map
`M ⊗ C(P; S) ⟶ C(P; N)` of a coefficient pairing `μ : M ⊗ S ⟶ N`, Tau Ceti's
`SSetPair.chainComplexPairing`, is natural in each of the coefficient objects `M`, `S` and `N`.

## Main results

* `SSetPair.chainComplexπ_coefficient_naturality`: the quotient map from the chains of the
  ambient simplicial set to the relative chains commutes with a change of coefficients.
* `SSetPair.chainComplexPairing_comp_chainComplexFunctor_map_app`: naturality in `N`.
* `SSetPair.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing`: naturality in `S`.
* `SSetPair.whiskerRight_comp_chainComplexPairing`: naturality in `M`.

The three naturality lemmas are the relative forms of Tau Ceti's
`SSet.chainComplexPairing_comp_chainComplexFunctor_map_app`,
`SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing` and
`SSet.whiskerRight_comp_chainComplexPairing`
(`TauCeti/AlgebraicTopology/SimplicialSet/Homology/Pairing.lean`), and their proofs descend
those lemmas along the quotient maps to relative chains, which are epimorphisms after tensoring
with `M`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace SSetPair

/-- The quotient map from the chains of the ambient simplicial set of a pair to its relative
chains commutes with the chain maps induced by a coefficient morphism `g : S ⟶ S'`. -/
@[reassoc]
lemma chainComplexπ_coefficient_naturality {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] (P : SSetPair.{w}) {S S' : C} (g : S ⟶ S') :
    ((SSet.chainComplexFunctor C).map g).app P.right ≫ P.chainComplexπ S' =
      P.chainComplexπ S ≫ ((chainComplexFunctor C).map g).app P :=
  congrArg (fun η ↦ η.app P) ((chainComplexFunctorπ C).naturality g)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {M S N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- Postcomposing the chain map induced on relative chains by a coefficient pairing `μ` with the
chain map induced by a coefficient morphism `g : N ⟶ N'` is the chain map induced by the pairing
`μ ≫ g`: the relative form of `SSet.chainComplexPairing_comp_chainComplexFunctor_map_app`. -/
@[reassoc (attr := simp)]
lemma chainComplexPairing_comp_chainComplexFunctor_map_app (P : SSetPair.{w}) (μ : M ⊗ S ⟶ N)
    {N' : C} (g : N ⟶ N') :
    P.chainComplexPairing μ ≫ ((chainComplexFunctor C).map g).app P =
      P.chainComplexPairing (μ ≫ g) := by
  ext n : 1
  have hg := congrArg (fun φ ↦ φ.f n) (P.chainComplexπ_coefficient_naturality g)
  have hN := congrArg (fun φ ↦ φ.f n)
    (P.right.chainComplexPairing_comp_chainComplexFunctor_map_app μ g)
  dsimp at hg hN ⊢
  rw [← cancel_epi (M ◁ (P.chainComplexπ S).f n), whiskerLeft_chainComplexπ_f_chainComplexPairing_f,
    whiskerLeft_chainComplexπ_f_chainComplexPairing_f_assoc, ← hg, ← hN, Category.assoc]

/-- Precomposing the chain map induced on relative chains by a coefficient pairing `μ'` with the
chain map induced by a coefficient morphism `g : S ⟶ S'` is the chain map induced by the pairing
`(M ◁ g) ≫ μ'`: the relative form of
`SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing (P : SSetPair.{w})
    {S' : C} (g : S ⟶ S') (μ' : M ⊗ S' ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex _).map (((chainComplexFunctor C).map g).app P) ≫
        P.chainComplexPairing μ' =
      P.chainComplexPairing ((M ◁ g) ≫ μ') := by
  ext n : 1
  have hg := congrArg (fun φ ↦ φ.f n) (P.chainComplexπ_coefficient_naturality g)
  have hS := congrArg (fun φ ↦ φ.f n)
    (SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing P.right g μ')
  dsimp at hg hS ⊢
  rw [← cancel_epi (M ◁ (P.chainComplexπ S).f n), whiskerLeft_chainComplexπ_f_chainComplexPairing_f,
    ← whiskerLeft_comp_assoc, ← hg, whiskerLeft_comp_assoc,
    whiskerLeft_chainComplexπ_f_chainComplexPairing_f, reassoc_of% hS]

/-- Precomposing the chain map induced on relative chains by a coefficient pairing `μ'` with the
action of a morphism `g : M ⟶ M'` on the first factor is the chain map induced by the pairing
`(g ▷ S) ≫ μ'`: the relative form of `SSet.whiskerRight_comp_chainComplexPairing`. -/
@[reassoc (attr := simp)]
lemma whiskerRight_comp_chainComplexPairing (P : SSetPair.{w}) {M' : C}
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M')] (g : M ⟶ M')
    (μ' : M' ⊗ S ⟶ N) :
    (NatTrans.mapHomologicalComplex ((tensoringLeft C).map g) _).app (P.chainComplex S) ≫
        P.chainComplexPairing μ' =
      P.chainComplexPairing ((g ▷ S) ≫ μ') := by
  ext n : 1
  have hS := congrArg (fun φ ↦ φ.f n) (SSet.whiskerRight_comp_chainComplexPairing P.right g μ')
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    curriedTensor_map_app] at hS ⊢
  rw [← cancel_epi (M ◁ (P.chainComplexπ S).f n), whisker_exchange_assoc,
    whiskerLeft_chainComplexπ_f_chainComplexPairing_f,
    whiskerLeft_chainComplexπ_f_chainComplexPairing_f, reassoc_of% hS]

end SSetPair

end
