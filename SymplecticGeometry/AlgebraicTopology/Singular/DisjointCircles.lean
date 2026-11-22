/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.CircleMap
public import SymplecticGeometry.AlgebraicTopology.Singular.DiscreteProd

/-!
# First homology of a finite disjoint union of circles

For a finite discrete type `ι`, the space `ι × Circle` is a disjoint union of circles. This file
shows that its first singular homology, with coefficients `ModuleCat.of ℤ (ULift ℤ)`, is read off
from the circles one at a time.

Write `Circle.prodInclusion i : C(Circle, ι × Circle)` for the inclusion `z ↦ (i, z)` of the
`i`-th circle, and `Circle.prodRetraction i : C(ι × Circle, Circle)` for the map that is the
identity on the `i`-th circle and sends the others to `1`. The composite
`prodRetraction i ∘ prodInclusion j` is the identity for `j = i` and constant otherwise, so on
`H₁` it is the identity or zero. As morphisms of `TopCat`, `prodInclusion i` and
`prodRetraction i` are the fibre inclusion `TopCat.prodFiberInclusion` and the fibre retraction
`TopCat.prodFiberRetraction` with base point `1` (`Circle.ofHom_prodInclusion`,
`Circle.ofHom_prodRetraction`), so the general decomposition of the homology of a product with a
finite discrete factor, `TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp`, shows
that the composites `(prodRetraction i)_* ≫ (prodInclusion i)_*` add up to the identity of
`H₁(ι × Circle)`. Hence every class is the sum over `i` of `nᵢ` times the class of
the `i`-th circle, `nᵢ` being the integer that `Circle.singularHomologyOneIso` gives to its image
under `prodRetraction i`, and a class is determined by these images.

## Main results

* `Circle.singularHomologyFunctor_map_prodRetraction_comp_prodInclusion`: on `H₁`,
  `(prodInclusion j)_* ≫ (prodRetraction i)_*` is the identity if `j = i` and `0` otherwise.
* `Circle.sum_singularHomologyFunctor_map_prodRetraction_prodInclusion`: the composites
  `(prodRetraction i)_* ≫ (prodInclusion i)_*` add up to the identity of `H₁(ι × Circle)`.
* `Circle.eq_sum_zsmul_singularHomologyFunctor_map_prodInclusion`: every class of
  `H₁(ι × Circle)` is `∑ i, nᵢ • (prodInclusion i)_* g`, for `g` the generator of `H₁(Circle)`.
* `Circle.singularHomologyOne_prod_ext`: two classes with the same image under every
  `prodRetraction i` are equal.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Proposition 2.6
  (the homology of a disjoint union is the direct sum of the homologies of its components).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

namespace Circle

variable {ι : Type} [TopologicalSpace ι]

/-- The inclusion `z ↦ (i, z)` of the `i`-th circle into `ι × Circle`. -/
def prodInclusion (i : ι) : C(Circle, ι × Circle) :=
  (ContinuousMap.const Circle i).prodMk (ContinuousMap.id Circle)

@[simp]
theorem prodInclusion_apply (i : ι) (z : Circle) : prodInclusion i z = (i, z) :=
  (rfl)

/-- As a morphism of `TopCat`, `prodInclusion i` is Tau Ceti's fibre inclusion
`TopCat.prodFiberInclusion`. -/
theorem ofHom_prodInclusion (i : ι) :
    (TopCat.ofHom (prodInclusion i) : TopCat.of Circle ⟶ TopCat.of ι ⊗ TopCat.of Circle) =
      TopCat.prodFiberInclusion (TopCat.of ι) (TopCat.of Circle) i := by
  -- `TopCat.of ι ⊗ TopCat.of Circle` is `TopCat.of (ι × Circle)` only up to unfolding the
  -- monoidal structure, so the two sides are compared pointwise by `exact` rather than `rw`
  refine TopCat.ext fun z ↦ ?_
  exact (TopCat.prodFiberInclusion_apply (TopCat.of ι) (TopCat.of Circle) i z).symm

variable [DiscreteTopology ι] [DecidableEq ι]

/-- The map `ι × Circle → Circle` that is the identity on the `i`-th circle, `(i, z) ↦ z`, and
sends every other circle to `1`. It is continuous since `ι` is discrete. -/
def prodRetraction (i : ι) : C(ι × Circle, Circle) where
  toFun p := if p.1 = i then p.2 else 1
  continuous_toFun := continuous_prod_of_discrete_left.2 fun j ↦ by
    by_cases h : j = i
    · simpa [h] using continuous_id'
    · simpa [h] using continuous_const

theorem prodRetraction_apply (i : ι) (p : ι × Circle) :
    prodRetraction i p = if p.1 = i then p.2 else 1 :=
  (rfl)

@[simp]
theorem prodRetraction_apply_self (i : ι) (z : Circle) : prodRetraction i (i, z) = z := by
  simp [prodRetraction_apply]

@[simp]
theorem prodRetraction_apply_of_ne {i j : ι} (h : j ≠ i) (z : Circle) :
    prodRetraction i (j, z) = 1 := by
  simp [prodRetraction_apply, h]

/-- `prodRetraction i` is a retraction of the inclusion `prodInclusion i`. -/
@[simp]
theorem prodRetraction_comp_prodInclusion_self (i : ι) :
    (prodRetraction i).comp (prodInclusion i) = ContinuousMap.id Circle := by
  ext z
  simp

/-- `prodRetraction i` is constant on the `j`-th circle for `j ≠ i`. -/
theorem prodRetraction_comp_prodInclusion_of_ne {i j : ι} (h : j ≠ i) :
    (prodRetraction i).comp (prodInclusion j) = ContinuousMap.const Circle 1 := by
  ext z
  simp [prodRetraction_apply_of_ne h]

/-- As a morphism of `TopCat`, `prodRetraction i` is the fibre retraction
`TopCat.prodFiberRetraction` with base point `1`. -/
theorem ofHom_prodRetraction (i : ι) :
    (TopCat.ofHom (prodRetraction i) : TopCat.of ι ⊗ TopCat.of Circle ⟶ TopCat.of Circle) =
      TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i := by
  -- as in `ofHom_prodInclusion`, the two sources agree only up to unfolding
  refine TopCat.ext fun p ↦ ?_
  exact (TopCat.prodFiberRetraction_apply (TopCat.of ι) (1 : Circle) i p).symm

/-! ### First homology -/

/-- On `H₁`, the `j`-th circle followed by `prodRetraction i` is the identity if `j = i` and `0`
otherwise. -/
theorem singularHomologyFunctor_map_prodRetraction_comp_prodInclusion (i j : ι) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodInclusion j)) ≫
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodRetraction i)) =
      if j = i then 𝟙 _ else 0 := by
  rw [← Functor.map_comp, ← TopCat.ofHom_comp]
  split_ifs with h
  · subst h
    rw [prodRetraction_comp_prodInclusion_self, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  · rw [prodRetraction_comp_prodInclusion_of_ne h]
    -- `TopCat.ofHom (ContinuousMap.const _ 1)` is `TopCat.const 1` by definition, so the general
    -- vanishing of constant maps on positive-degree homology applies directly
    exact TopCat.singularHomologyFunctor_map_const_eq_zero (ModuleCat.of ℤ (ULift.{0} ℤ))
      (1 : TopCat.of Circle) (Y := TopCat.of Circle) one_ne_zero

/-- **The first homology of `ι × Circle` splits along the circles.** The composites of
`prodRetraction i` and `prodInclusion i` on `H₁` add up to the identity of `H₁(ι × Circle)`. -/
theorem sum_singularHomologyFunctor_map_prodRetraction_prodInclusion [Fintype ι] :
    ∑ i : ι, ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodRetraction i)) ≫
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodInclusion i)) = 𝟙 _ := by
  have h := TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp
    (ModuleCat.of ℤ (ULift.{0} ℤ)) (TopCat.of ι) (1 : TopCat.of Circle) one_ne_zero
  simp only [← ofHom_prodRetraction, ← ofHom_prodInclusion] at h
  -- `h` is the goal, with `TopCat.of ι ⊗ TopCat.of Circle` for `TopCat.of (ι × Circle)`
  exact h

/-- On the generator `g` of `H₁(Circle)`, the image under `prodRetraction i` of the class of the
`j`-th circle is `g` if `j = i` and `0` otherwise. -/
theorem singularHomologyFunctor_map_prodRetraction_map_prodInclusion (i j : ι) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodRetraction i))).hom
      ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodInclusion j))).hom
        ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1))) =
      if j = i then (singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)
      else 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    singularHomologyFunctor_map_prodRetraction_comp_prodInclusion]
  split_ifs <;> simp

/-- **Classes of `H₁(ι × Circle)` in terms of the circles.** Every class `y` is the sum over `i` of
`nᵢ` times the class of the `i`-th circle, the push-forward along `prodInclusion i` of the
generator of `H₁(Circle)`, where `nᵢ` is the integer that `Circle.singularHomologyOneIso` gives to
the image of `y` under `prodRetraction i`. -/
theorem eq_sum_zsmul_singularHomologyFunctor_map_prodInclusion [Fintype ι]
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of (ι × Circle))) :
    y = ∑ i, ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom (prodRetraction i))).hom y)).down •
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodInclusion i))).hom
        ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) := by
  have h := congrArg (fun f ↦ f.hom y)
    (sum_singularHomologyFunctor_map_prodRetraction_prodInclusion (ι := ι))
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← map_zsmul, ← eq_zsmul_singularHomologyOneIso_inv_one]

/-- **Classes of `H₁(ι × Circle)` are determined on the circles.** Two classes with the same image
under every `prodRetraction i` are equal. -/
theorem singularHomologyOne_prod_ext [Finite ι]
    {y y' : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of (ι × Circle))}
    (h : ∀ i, (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (prodRetraction i))).hom y =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (prodRetraction i))).hom y') :
    y = y' := by
  have := Fintype.ofFinite ι
  rw [eq_sum_zsmul_singularHomologyFunctor_map_prodInclusion y,
    eq_sum_zsmul_singularHomologyFunctor_map_prodInclusion y']
  simp only [h]

end Circle
