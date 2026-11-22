/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Monoidal

/-!
# Fibre retractions of a product with a discrete factor in `TopCat`

For a discrete space `ι`, a space `X`, a point `x₀ : X` and `i : ι`, the map
`TopCat.prodFiberRetraction ι x₀ i : ι ⊗ X ⟶ X` is the identity on the fibre over `i` and sends
every other fibre to `x₀`. It is a left inverse of Tau Ceti's fibre inclusion
`TopCat.prodFiberInclusion ι X i` (`TopCat.prodFiberInclusion_comp_prodFiberRetraction`), and
composed with the inclusion of any other fibre it is the constant map at `x₀`
(`TopCat.prodFiberInclusion_comp_prodFiberRetraction_of_ne`).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe w

namespace TopCat

variable (ι : TopCat.{w}) [DiscreteTopology ι] {X : TopCat.{w}}

open Classical in
/-- For a discrete space `ι`, a point `x₀ : X` and `i : ι`, the retraction of `ι ⊗ X` onto the
fibre over `i`: it sends `(i, x)` to `x`, and `(j, x)` to `x₀` for `j ≠ i`. -/
def prodFiberRetraction (x₀ : X) (i : ι) : ι ⊗ X ⟶ X :=
  ofHom ⟨fun p ↦ if p.1 = i then p.2 else x₀,
    continuous_prod_of_discrete_left.2 fun j ↦ by
      by_cases h : j = i <;> simp only [h, ↓reduceIte] <;> fun_prop⟩

lemma prodFiberRetraction_apply [DecidableEq ι] (x₀ : X) (i : ι) (p : ↑(ι ⊗ X)) :
    prodFiberRetraction ι x₀ i p = if p.1 = i then p.2 else x₀ := by
  -- the definition uses the classical decidability instance, which may differ from the given one
  rw [show prodFiberRetraction ι x₀ i p = @ite _ (p.1 = i) (Classical.dec _) p.2 x₀ from rfl]
  congr

@[simp]
lemma prodFiberRetraction_apply_self (x₀ : X) (i : ι) (x : X) :
    prodFiberRetraction ι x₀ i ((i, x) : ↑(ι ⊗ X)) = x := by
  classical
  exact (prodFiberRetraction_apply ι x₀ i _).trans (by simp)

@[simp]
lemma prodFiberRetraction_apply_of_ne (x₀ : X) {i j : ι} (h : j ≠ i) (x : X) :
    prodFiberRetraction ι x₀ i ((j, x) : ↑(ι ⊗ X)) = x₀ := by
  classical
  exact (prodFiberRetraction_apply ι x₀ i _).trans (by simp [h])

/-- The retraction onto the fibre over `i` is a left inverse of the inclusion of that fibre. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_comp_prodFiberRetraction (x₀ : X) (i : ι) :
    prodFiberInclusion ι X i ≫ prodFiberRetraction ι x₀ i = 𝟙 X := by
  ext x
  simp

/-- The inclusion of the fibre over `j`, followed by the retraction onto another fibre, is the
constant map at the base point. -/
lemma prodFiberInclusion_comp_prodFiberRetraction_of_ne (x₀ : X) {i j : ι} (h : j ≠ i) :
    prodFiberInclusion ι X j ≫ prodFiberRetraction ι x₀ i = TopCat.const x₀ := by
  ext x
  simp [h]

end TopCat

end
