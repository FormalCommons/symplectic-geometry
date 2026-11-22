/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative

/-!
# Relative and ambient cochains of a pair of simplicial sets

For a pair of simplicial sets `P`, `SSetPair.cochainComplexπ` is the map from the cochains of
`P` relative to its subobject to the cochains of its ambient simplicial set, obtained by applying
`Hom(-, M)` to the quotient map from ambient to relative chains. It is natural in maps of pairs
(`SSetPair.cochainComplexπ_naturality`).

These two declarations are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/Relative.lean`, same names), as of the commit
`ee1e8aa575ea963edb293ab50d8dc372809e6abb`, not yet in the pinned release.
They are stated here under their Tau Ceti names and namespace, so that moving Tau Ceti past them
deletes this file without renames. This file is a part of that file, with only these two
declarations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* J. Riou and A. Yang, [relative homology of simplicial-set pairs in
  Mathlib](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace SSetPair

open TauCeti.ChainComplex

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C}

variable (R k M) in
/-- The map `Hom(C(P), M) ⟶ Hom(C(P.right), M)` from relative to ambient cochains of a pair of
simplicial sets: precomposition with the quotient map from ambient to relative chains. -/
abbrev cochainComplexπ (P : SSetPair.{w}) :
    (P.chainComplex R).linearYonedaObj k M ⟶ (P.right.chainComplex R).linearYonedaObj k M :=
  (linearYonedaFunctor k M).map (P.chainComplexπ R).op

variable (R k M) in
/-- The maps `cochainComplexπ` from relative to ambient cochains are natural in maps of pairs of
simplicial sets. -/
@[reassoc]
lemma cochainComplexπ_naturality {P Q : SSetPair.{w}} (f : P ⟶ Q) :
    cochainComplexπ R k M Q ≫ SSet.cochainComplexMap f.right =
      cochainComplexMap f ≫ cochainComplexπ R k M P := by
  have h := congrArg (fun φ ↦ (linearYonedaFunctor k M).map φ.op) (chainComplexπ_naturality R f)
  simp only [op_comp, Functor.map_comp] at h
  exact h

end SSetPair

end
