/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.Topology.Category.TopCat.Monoidal
import SymplecticGeometry.AlgebraicTopology.Singular.CircleMap
import SymplecticGeometry.AlgebraicTopology.Singular.DiscreteProd

/-!
# First homology of a finite disjoint union of circles

For a finite discrete type `ι`, the space `ι ⊗ Circle` is a disjoint union of circles. This file
shows that its first singular homology, with coefficients `ModuleCat.of ℤ (ULift ℤ)`, is read off
from the circles one at a time.

The `i`-th circle is included by Tau Ceti's fibre inclusion
`TopCat.prodFiberInclusion (TopCat.of ι) (TopCat.of Circle) i`, and retracted onto by the fibre
retraction `TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i`, which sends the other circles
to `1`. On `H₁`, the inclusion of the `j`-th circle followed by the retraction onto the `i`-th is
the identity or zero
(`TopCat.singularHomologyFunctor_map_prodFiberInclusion_comp_prodFiberRetraction`), and the
composites of the retractions and the inclusions add up to the identity of
`H₁(ι ⊗ Circle)` (`TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp`). Hence every
class is the sum over `i` of `nᵢ` times the class of the `i`-th circle, `nᵢ` being the integer that
`Circle.singularHomologyOneIso` gives to its image under the `i`-th retraction, and a class is
determined by these images.

## Main results

* `Circle.eq_sum_zsmul_singularHomologyFunctor_map_prodFiberInclusion`: every class of
  `H₁(ι ⊗ Circle)` is `∑ i, nᵢ • (σᵢ)_* g`, for `σᵢ` the inclusion of the `i`-th circle and `g`
  the generator of `H₁(Circle)`.
* `Circle.singularHomologyOne_prod_ext`: two classes with the same image under every fibre
  retraction are equal.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §2.1, Proposition 2.6
  (the homology of a disjoint union is the direct sum of the homologies of its components).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory AlgebraicTopology

namespace Circle

variable {ι : Type} [TopologicalSpace ι] [DiscreteTopology ι]

/-- **Classes of `H₁(ι ⊗ Circle)` in terms of the circles.** Every class `y` is the sum over `i` of
`nᵢ` times the class of the `i`-th circle, the push-forward along the fibre inclusion of the
generator of `H₁(Circle)`, where `nᵢ` is the integer that `Circle.singularHomologyOneIso` gives to
the image of `y` under the retraction onto the `i`-th circle. -/
theorem eq_sum_zsmul_singularHomologyFunctor_map_prodFiberInclusion [Fintype ι]
    (y : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of ι ⊗ TopCat.of Circle)) :
    y = ∑ i, ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i)).hom y)).down •
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.prodFiberInclusion (TopCat.of ι) (TopCat.of Circle) i)).hom
        ((singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) := by
  have h := congrArg (fun f ↦ f.hom y)
    (TopCat.sum_singularHomologyFunctor_map_prodFiberRetraction_comp
      (ModuleCat.of ℤ (ULift.{0} ℤ)) (TopCat.of ι) (1 : Circle) one_ne_zero)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← map_zsmul, ← eq_zsmul_singularHomologyOneIso_inv_one]

/-- **Classes of `H₁(ι ⊗ Circle)` are determined on the circles.** Two classes with the same image
under the retraction onto every circle are equal. -/
theorem singularHomologyOne_prod_ext [Finite ι]
    {y y' : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of ι ⊗ TopCat.of Circle)}
    (h : ∀ i, (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i)).hom y =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.prodFiberRetraction (TopCat.of ι) (1 : Circle) i)).hom y') :
    y = y' := by
  have := Fintype.ofFinite ι
  rw [eq_sum_zsmul_singularHomologyFunctor_map_prodFiberInclusion y,
    eq_sum_zsmul_singularHomologyFunctor_map_prodFiberInclusion y']
  simp only [h]

end Circle

end
