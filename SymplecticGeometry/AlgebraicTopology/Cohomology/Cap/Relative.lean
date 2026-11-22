/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative

/-!
# Naturality of relative cap chains

For a map of topological pairs `f : P ⟶ P'`, capping the image under `f` of a relative chain of
`P` with a relative cochain `φ` of `P'` is the same as capping the chain with the pull-back of `φ`
along `f` and then pushing the result forward along the map of ambient spaces
(`TopPair.capChain_naturality`). This is the chain-level form of the projection formula
`f_*(c ⌢ f^* φ) = f_* c ⌢ φ`.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/Cap/Relative.lean`, same name), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; it is stated here under
its Tau Ceti name, so that moving Tau Ceti past it deletes this file without renames.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3, the relative
  cap product and its naturality.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TopPair

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- Relative cap chains commute with maps of pairs and the induced ambient chain maps. -/
lemma capChain_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (k : Type*)
    [Semiring k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ N)
    (p q n : ℕ) (h : p + q = n) (φ : (P'.singularChainComplex R).X p ⟶ M) :
    (TopPair.singularChainComplexMap f T).f n ≫
        TauCeti.ChainComplex.capChain k (P'.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P'.fst).chainComplexPairing μ) p q n h φ =
      TauCeti.ChainComplex.capChain k (P.alexanderWhitneyDiagonal u)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ) p q n h
          ((TopPair.singularChainComplexMap f R).f p ≫ φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopPair.Hom.fst f)) N).f q :=
  (TauCeti.ChainComplex.capChain_naturality _ _ _ _ _ _ _ _
    (TopPair.alexanderWhitneyDiagonal_naturality f u)
    (SSet.chainComplexPairing_naturality (TopCat.toSSet.map (TopPair.Hom.fst f)) μ).symm
    p q n h φ).symm


end TopPair

end
