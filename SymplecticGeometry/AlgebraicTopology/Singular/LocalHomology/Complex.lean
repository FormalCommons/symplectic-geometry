/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.OrientedChart
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import TauCeti.Geometry.Manifold.Complex.FundamentalClass

/-!
# The local homology of `ℂ` at the origin

Two facts about the local orientation of `ℂ` at `0`, a generator of `H₂(ℂ, ℂ ∖ {0}; ℤ)`.

As a complex manifold, `ℂ` carries the orientation `TauCeti.complexHomologicalOrientation`. The
identity chart lies in the maximal atlas, so the local orientation at `0` is the one of that
chart (`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`), which is the local
orientation that `Complex.orientation` selects
(`Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl`).

The connecting morphism of the pair `(ℂ, ℂ ∖ {0})` followed by radial projection
(`Circle.radialProjection`) sends the local orientation of the identity chart to the generator of
the homology of the unit circle that `Complex.orientation` selects
(`OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl`),
and this is the generator of `Circle.singularHomologyOneIso`
(`Circle.singularHomologyOneIso_inv_eq_complexOrientation`).

## Main results

* `TauCeti.complexHomologicalOrientation_apply_zero`: the local orientation of `ℂ` at the origin is
  the one selected by `Complex.orientation`.
* `SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation`:
  the connecting morphism of `(ℂ, ℂ ∖ {0})`, followed by radial projection onto `Circle`, sends the
  local orientation selected by `Complex.orientation` to `1` in `H₁(Circle; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: local
  orientations of a manifold.
-/

public section

noncomputable section

open CategoryTheory Metric TauCeti AlgebraicTopology

/-- The local orientation of `ℂ`, as a complex manifold, at the origin is the one selected by
`Complex.orientation`. -/
theorem TauCeti.complexHomologicalOrientation_apply_zero :
    complexHomologicalOrientation ℂ 0 =
      Complex.orientation.localOrientation Complex.finrank_real_complex := by
  have h0 : (0 : ℂ) ∈ (OpenPartialHomeomorph.refl ℂ).source := by simp
  -- The preferred chart of `ℂ` is the identity.
  have hrefl :
      OpenPartialHomeomorph.refl ℂ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 ℂ := by
    simpa using IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf ℂ ℂ) (n := 1) (0 : ℂ)
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas hrefl h0,
    Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl]

namespace SymplecticGeometry

/-- **The local orientation of `ℂ` generates `H₁(S¹)`.** The connecting morphism of the pair
`(ℂ, ℂ ∖ {0})`, followed by radial projection `z ↦ z / |z|` onto `Circle`
(`Circle.radialProjection`), sends the local orientation of `ℂ` at the origin selected by
`Complex.orientation` to the class that is `1` in `H₁(Circle; ℤ) ≅ ℤ`
(`Circle.singularHomologyOneIso`). -/
theorem singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom Circle.radialProjection)
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 1 rfl
          (Complex.orientation.localOrientation Complex.finrank_real_complex).val)) = 1 := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  set Q := TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))
  set H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set e := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  set c := TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : ℂ)).toFun
  set x := (Complex.orientation.localOrientation Complex.finrank_real_complex).val
  have key : H.map (c ≫ e) (Q.singularHomologyδ R 2 1 rfl x) =
      (Circle.singularHomologyOneIso R).inv 1 := calc
    _ = H.map e (H.map c ((reducedSingularHomologyι R 1).app _
          (Q.reducedSingularHomologyδ R 1 x))) :=
        (ConcreteCategory.congr_hom (H.map_comp c e) _).trans
          ((ConcreteCategory.comp_apply _ _ _).trans (congrArg _ (congrArg _
            (ConcreteCategory.congr_hom (TopPair.reducedSingularHomologyδ_comp_ι Q R 1) x).symm)))
    _ = H.map e ((reducedSingularHomologyι R 1).app _
          ((reducedSingularHomologyFunctor R 1).map c (Q.reducedSingularHomologyδ R 1 x))) :=
        congrArg _ (ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality c) _).symm
    _ = H.map e ((reducedSingularHomologyι R 1).app _
          ((reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
            Complex.finrank_real_complex).inv 1)) := by
        have h :=
          OpenPartialHomeomorph.map_reducedSingularHomologyδ_localOrientationOfOrientedChart_refl
            (p := (0 : ℂ)) (by simp) Complex.orientation Complex.finrank_real_complex
        rw [← Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl] at h
        exact congrArg _ (congrArg _ h)
    _ = (Circle.singularHomologyOneIso R).inv 1 := by
        rw [Circle.singularHomologyOneIso_inv_eq_complexOrientation, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply]
  rw [Circle.radialProjection_def, TopCat.ofHom_comp, key, Iso.inv_hom_id_apply]

end SymplecticGeometry
