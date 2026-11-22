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

For spaces `X` and `Y`, `TopCat.prodHomeomorphTensorObj X Y` is the identity of `X × Y`, read as
a homeomorphism onto the carrier of `TopCat.of X ⊗ TopCat.of Y`. The two types agree only after
unfolding, so a map into `X × Y` composed with a morphism out of `TopCat.of X ⊗ TopCat.of Y`
goes through it, and `TopCat.prodFiberRetraction_prodHomeomorphTensorObj` evaluates the
retraction there.
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

/-! The two evaluation lemmas below write out the coercion to a function so that they can mark the
codomain `↑X` of the continuous map, and the point, with `no_index`. Before rewriting, `simp`
reduces a carrier `↑(TopCat.of Y)` to `Y`, while the index of a simp lemma keeps a carrier such as
`↑X` or `↑ι` as a projection, which does not match `Y`. Without `no_index`, these lemmas would
not fire when `ι` or `X` is of the form `TopCat.of _`, as it is in every use. -/

/-- The retraction onto the fibre over `i` is the identity on that fibre. -/
@[simp]
lemma prodFiberRetraction_apply_self (x₀ : X) (i : ι) (x : X) :
    DFunLike.coe (F := no_index C(↑(ι ⊗ X), X)) (α := ↑(ι ⊗ X))
      (ConcreteCategory.hom (prodFiberRetraction ι x₀ i)) (no_index ((i, x) : ↑(ι ⊗ X))) = x := by
  classical
  exact (prodFiberRetraction_apply ι x₀ i _).trans (by simp)

/-- The retraction onto the fibre over `i` sends every other fibre to the base point. -/
@[simp]
lemma prodFiberRetraction_apply_of_ne (x₀ : X) {i j : ι} (h : j ≠ i) (x : X) :
    DFunLike.coe (F := no_index C(↑(ι ⊗ X), X)) (α := ↑(ι ⊗ X))
      (ConcreteCategory.hom (prodFiberRetraction ι x₀ i)) (no_index ((j, x) : ↑(ι ⊗ X))) =
      x₀ := by
  classical
  exact (prodFiberRetraction_apply ι x₀ i _).trans (by simp [h])

example {α Y : Type w} [TopologicalSpace α] [DiscreteTopology α] [TopologicalSpace Y] (y₀ : Y)
    {i j : α} (h : j ≠ i) (y : Y) :
    prodFiberRetraction (of α) (X := of Y) y₀ i (i, y) = y ∧
      prodFiberRetraction (of α) (X := of Y) y₀ i (j, y) = y₀ := by
  simp [h]

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

/-- For spaces `X` and `Y`, the identity of `X × Y` as a homeomorphism onto the carrier of the
monoidal product `TopCat.of X ⊗ TopCat.of Y`. -/
def prodHomeomorphTensorObj (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y] :
    X × Y ≃ₜ ↑(TopCat.of X ⊗ TopCat.of Y) :=
  Homeomorph.refl _

@[simp]
lemma fst_prodHomeomorphTensorObj (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
    (p : X × Y) : (prodHomeomorphTensorObj X Y p).1 = p.1 :=
  (rfl)

@[simp]
lemma snd_prodHomeomorphTensorObj (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y]
    (p : X × Y) : (prodHomeomorphTensorObj X Y p).2 = p.2 :=
  (rfl)

@[simp]
lemma prodHomeomorphTensorObj_symm_apply (X Y : Type w) [TopologicalSpace X]
    [TopologicalSpace Y] (p : ↑(TopCat.of X ⊗ TopCat.of Y)) :
    (prodHomeomorphTensorObj X Y).symm p = (p.1, p.2) :=
  (rfl)

/-- The retraction onto the fibre over `i`, evaluated at a point of `ι × X`.

The retraction is read as a map in `C(↑(TopCat.of ι ⊗ TopCat.of X), X)`, with codomain `X` and not
`↑(TopCat.of X)`: this is how the coercion appears in goals, so `simp` can use the lemma there. -/
@[simp]
lemma prodFiberRetraction_prodHomeomorphTensorObj (ι : Type w) [TopologicalSpace ι]
    [DiscreteTopology ι] [DecidableEq ι] {X : Type w} [TopologicalSpace X] (x₀ : X) (i : ι)
    (p : ι × X) :
    DFunLike.coe (F := C(↑(TopCat.of ι ⊗ TopCat.of X), X))
        (prodFiberRetraction (TopCat.of ι) (X := TopCat.of X) x₀ i).hom
        (prodHomeomorphTensorObj ι X p) =
      if p.1 = i then p.2 else x₀ := by
  rw [prodFiberRetraction_apply, fst_prodHomeomorphTensorObj, snd_prodHomeomorphTensorObj]

end TopCat

end
