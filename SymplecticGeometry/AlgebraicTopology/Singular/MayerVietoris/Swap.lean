/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-!
# The Mayer–Vietoris connecting morphism with the two pieces exchanged

Exchanging the two pieces of a Mayer–Vietoris square changes the sign of the connecting morphism.
For a pushout square of simplicial sets with monomorphisms `t : X₁ ⟶ X₂` and `l : X₁ ⟶ X₃`, the
connecting morphism of the transposed square `sq.flip` is the negative of that of `sq`
(`SSet.mayerVietorisδ_flip`). The sign comes from the convention that the first map of the
sequence is `(t_*, -l_*)`: the map of short exact sequences of chain complexes from the sequence
of `sq` to that of `sq.flip` that exchanges the two summands in the middle and is the identity on
`C(X₄)` is `-1` on `C(X₁)`.

For an open cover of a space `X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(V ∩ U)` of
the cover `(V, U)` is therefore the negative of that of `(U, V)` followed by the map induced by
the identification `U ∩ V = V ∩ U` (`TopCat.mayerVietorisδ_swap`). The proof compares the two
pushout squares of singular simplicial sets by `SSet.mayerVietorisδ_naturality`, as in Tau Ceti's
`TopCat.mayerVietorisδ_naturality`.

## Main results

* `SSet.mayerVietorisδ_flip`: the connecting morphism of the transposed pushout square.
* `TopCat.mayerVietorisδ_swap`: the connecting morphism of an open cover with the two pieces
  exchanged.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2: the
  Mayer–Vietoris sequence.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/-- **Exchanging the pieces of a Mayer–Vietoris square.** For a pushout square of simplicial sets
whose maps `t` and `l` out of `X₁` are monomorphisms, the Mayer–Vietoris connecting morphism
`Hₙ(X₄) ⟶ Hₘ(X₁)` of the transposed square is the negative of that of the square. -/
lemma mayerVietorisδ_flip (sq : IsPushout t l r b) [Mono t] [Mono l] (n m : ℕ)
    (h : m + 1 = n := by lia) :
    mayerVietorisδ R sq.flip n m h = -mayerVietorisδ R sq n m h := by
  have := HomologicalComplex.HomologySequence.δ_naturality
    (S₁ := (sq.map ((chainComplexFunctor C).obj R)).shortComplex)
    (S₂ := (sq.flip.map ((chainComplexFunctor C).obj R)).shortComplex)
    { τ₁ := -𝟙 _
      τ₂ := (biprod.braiding _ _).hom
      τ₃ := 𝟙 _
      comm₁₂ := by
        -- Expose the two `f` maps to check the square on both biproduct projections.
        change (-𝟙 _) ≫ biprod.lift (chainComplexMap l R) (-chainComplexMap t R) =
          biprod.lift (chainComplexMap t R) (-chainComplexMap l R) ≫
            (biprod.braiding _ _).hom
        apply biprod.hom_ext <;> simp
      comm₂₃ := by
        -- Expose the two `g` maps to check the square on both biproduct inclusions.
        change (biprod.braiding _ _).hom ≫
            biprod.desc (chainComplexMap b R) (chainComplexMap r R) =
          biprod.desc (chainComplexMap r R) (chainComplexMap b R) ≫ 𝟙 _
        apply biprod.hom_ext' <;> simp }
    (shortExact_mayerVietorisShortComplex R sq) (shortExact_mayerVietorisShortComplex R sq.flip)
    n m h
  rw [HomologicalComplex.homologyMap_neg, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_id, Category.id_comp, Preadditive.comp_neg,
    Category.comp_id] at this
  rw [mayerVietorisδ_def R sq.flip n m h, mayerVietorisδ_def R sq n m h, ← this]

end SSet

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {X : TopCat.{w}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- **The Mayer–Vietoris connecting morphism with the two pieces exchanged.** For an open cover of
`X` by `U` and `V`, the connecting morphism `Hₙ(X) ⟶ Hₘ(V ∩ U)` of the cover `(V, U)` is the
negative of the connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)` of the cover `(U, V)`, followed by the
map induced by the identification `U ∩ V = V ∩ U`. -/
theorem mayerVietorisδ_swap (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hV hU ((Set.union_comm V U).trans hUV) n m h =
      -(mayerVietorisδ R hU hV hUV n m h ≫
        SSet.homologyMap (toSSet.map (ofHom (ContinuousMap.inclusion
          (Set.inter_comm U V).subset))) R m) := by
  have hf : ∀ i, Set.MapsTo (𝟙 X) (![U, V] i) (![V, U] (Fin.rev i)) := by
    simp [Fin.forall_fin_two, Set.mapsTo_id]
  have := TauCeti.isIso_homologyMap_smallSingularChainι R ![U, V] (hU.vecCons hV)
    ((U.iUnion_vecCons_pair V).trans hUV) n
  have hsq := isPushout_toSSet_inter_smallSingularSubcomplex U V
  have hnat := SSet.mayerVietorisδ_naturality R
    (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_comm U V).subset))) (𝟙 _) (𝟙 _)
    (X.smallSingularSubcomplexMap ![U, V] ![V, U] (𝟙 X) Fin.rev hf) hsq.flip
    (isPushout_toSSet_inter_smallSingularSubcomplex V U) ?_ ?_ ?_ ?_ n m h
  · refine (cancel_epi (SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n)).1 ?_
    have hι : SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n =
        SSet.homologyMap (X.smallSingularSubcomplexMap ![U, V] ![V, U] (𝟙 X) Fin.rev hf) R n ≫
          SSet.homologyMap (X.smallSingularSubcomplex ![V, U]).ι R n := by
      rw [← SSet.homologyMap_comp, smallSingularSubcomplexMap_ι, toSSet.map_id,
        Category.comp_id]
    rw [Preadditive.comp_neg, homologyMap_ι_comp_mayerVietorisδ_assoc R hU hV hUV n m h,
      ← Preadditive.neg_comp, ← SSet.mayerVietorisδ_flip R hsq n m h, hnat, hι, Category.assoc,
      homologyMap_ι_comp_mayerVietorisδ R hV hU _ n m h]
  -- The four squares commute: the first two are squares of inclusions of subspaces, and the
  -- last two compare the inclusions of the pieces into the two small singular subcomplexes.
  · rw [Category.comp_id, ← Functor.map_comp, ofHom_inclusion_comp_ofHom_inclusion]
  · rw [Category.comp_id, ← Functor.map_comp, ofHom_inclusion_comp_ofHom_inclusion]
  · rw [← cancel_mono (X.smallSingularSubcomplex ![V, U]).ι, Category.assoc,
      smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc, toSSet.map_id,
      Category.comp_id, Category.id_comp, toSmallSingularSubcomplex_ι]
  · rw [← cancel_mono (X.smallSingularSubcomplex ![V, U]).ι, Category.assoc,
      smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc, toSSet.map_id,
      Category.comp_id, Category.id_comp, toSmallSingularSubcomplex_ι]

end TopCat

end
