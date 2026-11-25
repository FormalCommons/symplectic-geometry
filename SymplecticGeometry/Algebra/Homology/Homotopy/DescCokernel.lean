/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy

/-!
# Descending a chain homotopy along two successive cokernels

Tau Ceti's `Homotopy.descCokernel` descends a chain homotopy `H` between maps `L ⟶ L'` along a
degreewise cokernel `p₁ : L ⟶ M` of `u₁ : K ⟶ L`, once `H` followed by a map `p' : L' ⟶ N'`
vanishes on the image of `u₁`. This file iterates it once: given a second degreewise cokernel
`p₂ : M ⟶ N` of `u₂ : K' ⟶ M`, the homotopy descends further to `N`
(`Homotopy.descCokernel₂`), provided that `H` followed by `p'` also vanishes on a map
`v : K'' ⟶ L` that lifts `u₂` along `p₁` up to a degreewise epimorphism `q : K'' ⟶ K'`, that is,
`q ≫ u₂ = v ≫ p₁`. Its components after `p₁` and `p₂` are those of `H` followed by `p'`
(`Homotopy.π_π_descCokernel₂_hom`).

The typical case is the tensor product of two relative chain complexes: `L = K₁ ⊗ K₂`,
`M = (K₁ ⧸ L₁) ⊗ K₂` and `N = (K₁ ⧸ L₁) ⊗ (K₂ ⧸ L₂)`, where `u₁` is the inclusion of `L₁ ⊗ K₂`,
`u₂` that of `(K₁ ⧸ L₁) ⊗ L₂`, `q` the projection `K₁ ⊗ L₂ ⟶ (K₁ ⧸ L₁) ⊗ L₂` and `v` the
inclusion of `K₁ ⊗ L₂`. Then the two conditions say that `H` vanishes on `L₁ ⊗ K₂` and on
`K₁ ⊗ L₂` after `p'`.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace Homotopy

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L M K' N K'' L' N' : HomologicalComplex C c}
  {fL gL : L ⟶ L'} {fN gN : N ⟶ N'}
  (HL : Homotopy fL gL) (p' : L' ⟶ N')
  (u₁ : K ⟶ L) (p₁ : L ⟶ M) (hw₁ : ∀ i, u₁.f i ≫ p₁.f i = 0)
  (hp₁ : ∀ i, IsColimit (CokernelCofork.ofπ (p₁.f i) (hw₁ i)))
  (hcomm₁ : ∀ i j, u₁.f i ≫ HL.hom i j ≫ p'.f j = 0)
  (u₂ : K' ⟶ M) (p₂ : M ⟶ N) (hw₂ : ∀ i, u₂.f i ≫ p₂.f i = 0)
  (hp₂ : ∀ i, IsColimit (CokernelCofork.ofπ (p₂.f i) (hw₂ i)))
  (q : K'' ⟶ K') (hq : ∀ i, Epi (q.f i)) (v : K'' ⟶ L) (hqv : q ≫ u₂ = v ≫ p₁)
  (hcomm₂ : ∀ i j, v.f i ≫ HL.hom i j ≫ p'.f j = 0)
  (hf : p₁ ≫ p₂ ≫ fN = fL ≫ p') (hg : p₁ ≫ p₂ ≫ gN = gL ≫ p')

/-- A chain homotopy `H` between maps `L ⟶ L'` descends along two successive degreewise
cokernels `p₁ : L ⟶ M` of `u₁` and `p₂ : M ⟶ N` of `u₂` to a chain homotopy between maps
`N ⟶ N'`, when `H` followed by `p' : L' ⟶ N'` vanishes on `u₁` and on a map `v` with
`q ≫ u₂ = v ≫ p₁` for a degreewise epimorphism `q`. -/
def descCokernel₂ : Homotopy fN gN :=
  descCokernel (descCokernel HL u₁ p₁ p' hw₁ hp₁ hcomm₁ hf hg) u₂ p₂ (𝟙 N') hw₂ hp₂
    (fun i j ↦ by
      have := hq i
      rw [id_f, Category.comp_id, ← cancel_epi (q.f i), comp_zero, ← Category.assoc, ← comp_f,
        hqv, comp_f, Category.assoc, π_descCokernel_hom, hcomm₂])
    (Category.comp_id _).symm (Category.comp_id _).symm

/-- After the two cokernel maps, the components of `Homotopy.descCokernel₂` are those of the
original homotopy followed by `p'`. -/
@[reassoc (attr := simp)]
theorem π_π_descCokernel₂_hom (i j : ι) :
    p₁.f i ≫ p₂.f i ≫
        (descCokernel₂ HL p' u₁ p₁ hw₁ hp₁ hcomm₁ u₂ p₂ hw₂ hp₂ q hq v hqv hcomm₂ hf hg).hom i j =
      HL.hom i j ≫ p'.f j := by
  rw [descCokernel₂, π_descCokernel_hom, id_f, Category.comp_id, π_descCokernel_hom]

end Homotopy

end
