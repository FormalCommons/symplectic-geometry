/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# Coefficient pairings on relative simplicial chains: the tensor unit

This file is a part of Tau Ceti's file
`TauCeti/AlgebraicTopology/SimplicialSet/Homology/Relative/Pairing.lean`, taken from Tau Ceti's
commit `b8021c6a5b88`, which the pinned version of Tau Ceti does not have yet. It holds the one
declaration of that commit to the file that the library needs:

* `SSetPair.chainComplexPairing_leftUnitor_hom_f`: the tensor unit acts on relative chains by the
  left unitor.

Changes: the module docstring is new, and the file imports Tau Ceti's file at the pinned version,
for the definition `SSetPair.chainComplexPairing`, instead of containing it, and its `variable`
line keeps only what the declaration uses, without Tau Ceti's `{M S N : C}` and the instance on
`tensorLeft M`. The declaration, its docstring and its proof are Tau Ceti's, unchanged.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- The chain map `𝟙 ⊗ C(Y, X; S) ⟶ C(Y, X; S)` induced by the left unitor of `S` is, in each
degree, the left unitor of the object of relative chains: the relative form of
`SSet.chainComplexPairing_leftUnitor_hom_f`. -/
@[simp]
lemma chainComplexPairing_leftUnitor_hom_f [∀ J : Type w,
      PreservesColimitsOfShape (Discrete J) (tensorLeft (𝟙_ C))] (P : SSetPair.{w}) (S : C)
    (n : ℕ) :
    (P.chainComplexPairing (λ_ S).hom).f n = (λ_ ((P.chainComplex S).X n)).hom := by
  rw [← cancel_epi (𝟙_ C ◁ (P.chainComplexπ S).f n),
    whiskerLeft_chainComplexπ_f_chainComplexPairing_f, SSet.chainComplexPairing_leftUnitor_hom_f,
    leftUnitor_naturality]

end SSetPair
