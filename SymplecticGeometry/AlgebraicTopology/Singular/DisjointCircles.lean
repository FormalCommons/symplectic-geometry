/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.Topology.Category.TopCat.Monoidal
public import SymplecticGeometry.AlgebraicTopology.Singular.CircleMap

/-!
# First homology of a finite disjoint union of circles

For a finite discrete type `ι`, the space `ι × Circle` is a disjoint union of circles. This file
shows that its first singular homology, with coefficients `ModuleCat.of ℤ (ULift ℤ)`, is read off
from the circles one at a time.

Write `Circle.prodInclusion i : C(Circle, ι × Circle)` for the inclusion `z ↦ (i, z)` of the
`i`-th circle, and `Circle.prodRetraction i : C(ι × Circle, Circle)` for the map that is the
identity on the `i`-th circle and sends the others to `1`. The composite
`prodRetraction i ∘ prodInclusion j` is the identity for `j = i` and constant otherwise, so on
`H₁` it is the identity or zero. The inclusions are the legs of a coproduct cofan in `TopCat`
(Mathlib's `TopCat.sigmaCofanIsColimit`, carried to `ι × Circle` by Tau Ceti's
`TopCat.sigmaConstIsoProd`), and singular homology preserves finite coproducts (Tau Ceti's
`TauCeti.isColimitCofanSingularHomology`, whose `PreservesColimitsOfShape` instance is used
here), so the composites `(prodRetraction i)_* ≫ (prodInclusion i)_*` add up to the identity of
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

open CategoryTheory Limits AlgebraicTopology

namespace Circle

variable {ι : Type} [TopologicalSpace ι]

/-- The inclusion `z ↦ (i, z)` of the `i`-th circle into `ι × Circle`. -/
def prodInclusion (i : ι) : C(Circle, ι × Circle) :=
  (ContinuousMap.const Circle i).prodMk (ContinuousMap.id Circle)

@[simp]
theorem prodInclusion_apply (i : ι) (z : Circle) : prodInclusion i z = (i, z) :=
  (rfl)

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

/-- For `ι` discrete, the inclusions `prodInclusion i` are the legs of a coproduct cofan in
`TopCat`. -/
private def isColimitCofanProdInclusion :
    IsColimit (Cofan.mk (TopCat.of (ι × Circle))
      (fun i ↦ TopCat.ofHom (prodInclusion i)) : Cofan fun _ : ι ↦ TopCat.of Circle) :=
  IsColimit.ofIsoColimit (TopCat.sigmaCofanIsColimit _)
    (Cofan.ext (TopCat.sigmaConstIsoProd (TopCat.of ι) (TopCat.of Circle) :
        TopCat.of (Σ _ : ι, Circle) ≅ TopCat.of (ι × Circle))
      fun i ↦ TopCat.ext fun z ↦ by
        simp only [Cofan.mk_pt, TopCat.hom_comp, ContinuousMap.comp_apply, cofan_mk_inj,
          ConcreteCategory.hom_ofHom, prodInclusion_apply]
        exact TopCat.sigmaConstIsoProd_hom_apply (TopCat.of ι) (TopCat.of Circle) ⟨i, z⟩)

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
  · rw [prodRetraction_comp_prodInclusion_of_ne h,
      ContinuousMap.singularHomologyFunctor_map_eq_circleDegree_smul,
      ContinuousMap.circleDegree_const, zero_smul]

/-- **The first homology of `ι × Circle` splits along the circles.** The composites of
`prodRetraction i` and `prodInclusion i` on `H₁` add up to the identity of `H₁(ι × Circle)`. -/
theorem sum_singularHomologyFunctor_map_prodRetraction_prodInclusion [Fintype ι] :
    ∑ i : ι, ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodRetraction i)) ≫
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom (prodInclusion i)) = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ)))
    _ _ (isColimitCofanProdInclusion (ι := ι))) _ _ fun j ↦ ?_
  simp [Preadditive.comp_sum, ← Category.assoc,
    singularHomologyFunctor_map_prodRetraction_comp_prodInclusion, ite_comp]

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
