/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic

/-!
# The cochain Mayer–Vietoris connecting morphism depends only on the maps of the square

For a pushout square of simplicial sets, `SSet.mayerVietorisCochainδ_congr` says that the cochain
Mayer–Vietoris connecting morphism `SSet.mayerVietorisCochainδ` depends only on the four maps of
the square, and not on the proof that it is a pushout.

This lemma is from Tau Ceti's main branch
(`TauCeti/AlgebraicTopology/Cohomology/MayerVietoris/Basic.lean`, same name), as of the commit
`ee1e8aa575ea963edb293ab50d8dc372809e6abb`, not yet in the pinned release.
It is stated here under its Tau Ceti name and namespace, so that moving Tau Ceti past it deletes
this file without renames.
This file is a part of that file, with only these declarations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the Mayer–Vietoris sequences in cohomology.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TauCeti.ChainComplex

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X₁ X₂ X₃ X₄ : SSet.{w}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

variable (sq : IsPushout t l r b) [Mono t]

/-- The cochain Mayer–Vietoris connecting morphism of a pushout square of simplicial sets only
depends on its maps. -/
lemma mayerVietorisCochainδ_congr {t₀ : X₁ ⟶ X₂} {l₀ : X₁ ⟶ X₃} {r₀ : X₂ ⟶ X₄} {b₀ : X₃ ⟶ X₄}
    (sq₀ : IsPushout t₀ l₀ r₀ b₀) (ht : t = t₀) (hl : l = l₀) (hr : r = r₀) (hb : b = b₀)
    (n m : ℕ) (h : n + 1 = m := by lia) :
    mayerVietorisCochainδ R k M sq n m h =
      haveI : Mono t₀ := ht ▸ inferInstance
      mayerVietorisCochainδ R k M sq₀ n m h := by
  subst ht hl hr hb
  rfl

end SSet

end
