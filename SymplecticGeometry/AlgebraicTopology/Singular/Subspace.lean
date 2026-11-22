/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Faces of singular simplices with image in a set

If a singular simplex `σ : Δⁿ → X` has image in a set `A ⊆ X`, so has its image under any
simplicial operator `⦋m⦌ ⟶ ⦋n⦌`, a face or a degeneracy of `σ`
(`TopCat.range_toSSetObjEquiv_map_subset`): it is `σ` precomposed with a map `Δᵐ → Δⁿ`.

This lemma is from Tau Ceti's main branch (`TauCeti/AlgebraicTopology/Singular/Subspace.lean`,
same name), as of the commit `e48a7f81a81426270765022681d165be592a3231`, not yet in the pinned
release; it is stated here under its Tau Ceti name, so that moving Tau Ceti past it deletes this
file without renames.
-/

public section

open Simplicial CategoryTheory

universe u

namespace TopCat

variable {X : TopCat.{u}}

/-- A simplicial operator preserves containment of the image of a singular simplex. -/
lemma range_toSSetObjEquiv_map_subset (A : Set X) {m n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (hσ : Set.range (X.toSSetObjEquiv _ σ) ⊆ A)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Set.range (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).map f.op σ)) ⊆ A := by
  rintro _ ⟨z, rfl⟩
  rw [TopCat.toSSetObjEquiv_naturality_apply]
  exact hσ ⟨_, rfl⟩

end TopCat

end
