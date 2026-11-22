/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Simplicial chain maps: the identity, and vanishing on pushed-forward chains

* `SSet.chainComplexMap_id`: the chain map `SSet.chainComplexMap (𝟙 X) R` induced by the identity
  of a simplicial set `X` is the identity of its chain complex with coefficients in `R`.
* `SSet.chainComplexMap_f_comp_eq_zero_iff`: a morphism out of the `n`-chains of `Y` kills the
  image of `(SSet.chainComplexMap f R).f n` if and only if it kills the summand of `f x` for every
  `n`-simplex `x` of `X`.

These lemmas are from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/SimplicialSet/Homology/Basic.lean`, same names), as of the commit
`e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned release; they are stated here
under their Tau Ceti names, so that moving Tau Ceti past them deletes this file without renames.
The proofs are Tau Ceti's. One statement differs: `SSet.chainComplexMap_f_comp_eq_zero_iff` binds
`X` itself, which in Tau Ceti's file is a variable of its section.
-/

public section

open CategoryTheory Limits Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The identity of a simplicial set induces the identity chain map. -/
lemma chainComplexMap_id (X : SSet.{w}) (R : C) : chainComplexMap (𝟙 X) R = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- For a map `f : X ⟶ Y` of simplicial sets, a morphism `c` out of the `n`-chains of `Y`
is zero after `(chainComplexMap f R).f n` exactly when `Y.ιChainComplex (f x) ≫ c = 0` for every
`n`-simplex `x` of `X`. -/
lemma chainComplexMap_f_comp_eq_zero_iff {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) {n : ℕ} {T : C}
    (c : (Y.chainComplex R).X n ⟶ T) :
    (chainComplexMap f R).f n ≫ c = 0 ↔ ∀ x : X _⦋n⦌, Y.ιChainComplex (f.app _ x) ≫ c = 0 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ chainComplex_hom_ext fun x ↦ ?_⟩
  · rw [← ι_chainComplexMap_f_assoc, h, comp_zero]
  · rw [ι_chainComplexMap_f_assoc, h, comp_zero]

end SSet

end
