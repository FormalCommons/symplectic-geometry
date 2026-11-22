/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
import all TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-!
# The shuffle map on a simplex and a vertex

This file is a part of Tau Ceti's file `TauCeti/AlgebraicTopology/SimplicialSet/Shuffle.lean`, as
of the commit `ef2c0780f7` of Tau Ceti's main branch, which the pinned release does not have yet.
It contains only the two declarations that this commit adds there:

* `SSet.shuffleChain_zero_right`: the shuffle chain of `Δ[p] ⊗ Δ[0]` is the single `p`-simplex
  whose first component is the top simplex of `Δ[p]` and whose second component is constant;
* `SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst`: in bidegree `(p, 0)`, the shuffle
  map followed by the projection `K × L ⟶ K` sends the summand of a `p`-simplex `x` of `K` and a
  vertex `y` of `L` to the summand of `x`.

They are stated under their Tau Ceti names and namespace, with Tau Ceti's statements, proofs and
docstrings unchanged, so that moving Tau Ceti past this commit deletes this file without
renames. The imports are replaced by the import of the pinned version of Tau Ceti's file, also
with `import all`: the proof of `SSet.shuffleChain_zero_right` unfolds `SSet.stdSimplex.prodCone`,
whose body the pinned version does not expose. The variables are those of the sections
`ShuffleChain` and `Shuffle` of that file.

## References

* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial HomologicalComplex

universe w v u

namespace SSet

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section ShuffleChain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (T : C)

open stdSimplex

/-- **The shuffle chain of a simplex and a vertex**: the shuffle chain of `Δ[p] ⊗ Δ[0]` is the
single `p`-simplex whose first component is the top simplex of `Δ[p]` and whose second component
is the constant simplex of `Δ[0]`. Here it is written as the simplex classified by the map
`(𝟙, f) : Δ[p] ⟶ Δ[p] ⊗ Δ[0]`, for the unique map `f : Δ[p] ⟶ Δ[0]`. -/
lemma shuffleChain_zero_right (p : ℕ) (h : p + 0 = p) (f : (Δ[p] : SSet.{w}) ⟶ Δ[0]) :
    shuffleChain T p 0 p h = ((Δ[p] : SSet.{w}) ⊗ Δ[0]).ιChainComplex
      (yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 _) f)) := by
  induction p with
  | zero => exact shuffleChain_zero_zero T h _
  | succ p ih =>
    rw [shuffleChain_succ_zero, ih _ (stdSimplex.δ 0 ≫ f), ι_chainComplexMap_f_assoc (Δ[p] ⊗ Δ[0]),
      stdSimplex.ιChainComplex_prodConeChain]
    -- the cone on the zeroth face of the top simplex is the top simplex, and the cone on the
    -- constant simplex is constant
    congr 1
    exact Prod.ext (stdSimplex.cone_δ_zero_yonedaEquiv_id p)
      (stdSimplex.ext _ _ fun _ ↦ Subsingleton.elim (α := Fin 1) _ _)

end ShuffleChain

section Shuffle

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  (K L : SSet.{w}) (R S : C)

/-- In bidegree `(p, 0)`, the shuffle map followed by the projection `K × L ⟶ K` sends the summand
of a `p`-simplex `x` of `K` and a vertex `y` of `L` to the summand of `x`: the shuffle product of a
simplex with a vertex projects onto that simplex. -/
@[reassoc]
lemma ιChainComplex_tensorHom_ιChainComplex_shuffle_f_fst {p : ℕ} (x : K _⦋p⦌) (y : L _⦋0⦌) :
    (K.ιChainComplex x ⊗ₘ L.ιChainComplex y) ≫
        ιTensorObj (K.chainComplex R) (L.chainComplex S) p 0 p (add_zero p) ≫
          (shuffle K L R S).f p ≫
            (chainComplexMap (CartesianMonoidalCategory.fst K L) (R ⊗ S)).f p =
      K.ιChainComplex x := by
  rw [ιChainComplex_tensorHom_ιChainComplex_shuffle_f_assoc,
    shuffleChain_zero_right _ p _ (yonedaEquiv.symm (stdSimplex.const 0 0 _)),
    chainComplexMap_f_comp, ι_chainComplexMap_f]
  exact congrArg _ (yonedaEquiv_symm_app_id x)

end Shuffle

end SSet
