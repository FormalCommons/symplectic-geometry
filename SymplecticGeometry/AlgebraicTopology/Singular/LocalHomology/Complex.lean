/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Plane
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
`Circle.singularHomologyOneIso`. This is the case `p = 0`, `φ = id` of the description of the
oriented local homology isomorphism of a plane through `Circle`
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection`).

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
  set e := singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl ℂ)
    (x := (0 : ℂ)) (by simp) (n := 1) Complex.orientation Complex.finrank_real_complex
  have he := singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection
    Complex.orientation Complex.finrank_real_complex 0 (LinearIsometryEquiv.refl ℝ ℂ)
    (by simp)
  -- With `p = 0` and `φ = id`, the map to `Circle` is radial projection.
  have hrad : Circle.radialProjection.comp
      ⟨fun y : ({0}ᶜ : Set ℂ) ↦ ⟨LinearIsometryEquiv.refl ℝ ℂ ((y : ℂ) - 0),
        fun h ↦ y.property (sub_eq_zero.1 ((map_eq_zero_iff _
          (LinearIsometryEquiv.refl ℝ ℂ).injective).1 h))⟩, by fun_prop⟩ =
      Circle.radialProjection := by
    ext y
    simp
  rw [hrad] at he
  have h1 := ConcreteCategory.congr_hom he (e.inv 1)
  rw [Iso.inv_hom_id_apply, ConcreteCategory.comp_apply] at h1
  rw [Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  -- The two sides differ in how the subspace of the pair is written, as `(ofSubset {0}ᶜ).snd`
  -- or as the source `{0}ᶜ` of radial projection, so `ConcreteCategory.comp_apply` cannot
  -- rewrite the last composite.
  exact h1.symm

end SymplecticGeometry
