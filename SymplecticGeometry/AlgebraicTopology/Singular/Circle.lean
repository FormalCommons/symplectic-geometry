/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.Analysis.Complex.Circle

/-!
# The generator of the first homology of the circle

Tau Ceti identifies `H₁(Circle; A)` with `A` (`Circle.singularHomologyOneIso`) through the
standard generator of the reduced homology of `TopCat.sphere 1`, which is defined from the
standard basis of the Euclidean model of the plane. This file reads that generator in `ℂ`: it is
the generator of the reduced homology of the unit circle of `ℂ` selected by the standard
orientation `Complex.orientation` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`),
carried to `Circle` (`Circle.singularHomologyOneIso_inv_eq`). The identification of
`TopCat.sphere 1` with `Circle` is induced by the linear isometry from the Euclidean model to `ℂ`
that sends the standard basis to `1, I`, which carries the standard orientation of the model to
`Complex.orientation`, and oriented sphere generators are natural under orientation-preserving
linear isometries (`TauCeti.reducedSingularHomologySphereIsoOfOrientation_hom_naturality`).

So local orientations of `ℂ` (`OpenPartialHomeomorph.localOrientationOfOrientedChart`), which are
read through the same oriented generator, can be compared with `Circle.singularHomologyOneIso`
without any sign.

## Main results

* `Circle.singularHomologyOneIso_inv_eq`: the inverse of `Circle.singularHomologyOneIso` is the
  generator of the unit circle of `ℂ` selected by `Complex.orientation`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the generators of the homology of spheres).
-/

public section

noncomputable section

open CategoryTheory Limits Metric TauCeti AlgebraicTopology

namespace Circle

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (A : C)

/-- The linear isometry from the Euclidean model of the plane to `ℂ`, sending the standard basis
to `1, I`. -/
private def modelEquiv : EuclideanSpace ℝ (ULift.{0} (Fin 2)) ≃ₗᵢ[ℝ] ℂ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ Equiv.ulift).trans
    Complex.orthonormalBasisOneI.repr.symm

/-- `modelEquiv` carries the standard basis of the model to the basis `1, I` of `ℂ`. -/
private lemma modelEquiv_basis :
    (((EuclideanSpace.basisFun (ULift.{0} (Fin 2)) ℝ).reindex Equiv.ulift).toBasis.map
      modelEquiv.toLinearEquiv) = Complex.basisOneI := by
  ext i
  fin_cases i <;> simp [modelEquiv]

/-- `modelEquiv` carries the standard orientation of the model to `Complex.orientation`. -/
private lemma map_orientation_modelEquiv :
    Orientation.map (Fin 2) modelEquiv.toLinearEquiv
      ((EuclideanSpace.basisFun (ULift.{0} (Fin 2)) ℝ).reindex Equiv.ulift).toBasis.orientation =
      Complex.orientation := by
  rw [← Module.Basis.orientation_map, modelEquiv_basis]
  -- `Complex.orientation` is by definition the orientation of `Complex.basisOneI`.
  rfl

/-- The map from `TopCat.sphere 1` to `Circle` of `sphereOneIsoCircleUnlifted` is the
homeomorphism `diskBoundaryHomeomorph` with the unit circle of the Euclidean model, followed by
`modelEquiv` and the identification of the unit circle of `ℂ` with `Circle`. -/
private lemma sphereOneIsoCircleUnlifted_hom_eq :
    sphereOneIsoCircleUnlifted.hom =
      TopCat.ofHom (diskBoundaryHomeomorph.{0} 2).toHomotopyEquiv.toFun ≫
        TopCat.ofHom ⟨modelEquiv.toLinearIsometry.unitSphereMap,
          modelEquiv.toLinearIsometry.continuous_unitSphereMap⟩ ≫
        TopCat.ofHom (homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)) := by
  ext x
  -- The right side is a composite of continuous maps evaluated at `x`.
  change _ = ((homeomorphSphere.symm
    (modelEquiv.toLinearIsometry.unitSphereMap (diskBoundaryHomeomorph.{0} 2 x)) : Circle) : ℂ)
  rw [sphereOneIsoCircleUnlifted_hom_apply, coe_homeomorphSphere_symm_apply,
    LinearIsometry.coe_unitSphereMap_apply, EuclideanSpace.coe_sphereHomeomorphCircle_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  -- `x` is a point of `TopCat.sphere 1`, which is `TopCat.diskBoundary 2` only after unfolding.
  erw [coe_diskBoundaryHomeomorph_apply]
  simp [modelEquiv]

/-- **The generator of `H₁(Circle)` is the oriented generator of the unit circle of `ℂ`.** The
inverse of `Circle.singularHomologyOneIso` is the generator of the reduced homology of the unit
circle of `ℂ` selected by the standard orientation `Complex.orientation`, read in unreduced
homology and carried to `Circle`. -/
theorem singularHomologyOneIso_inv_eq :
    (singularHomologyOneIso A).inv =
      (reducedSingularHomologySphereIsoOfOrientation A Complex.orientation
          Complex.finrank_real_complex).inv ≫
        (reducedSingularHomologyι A 1).app _ ≫
          ((singularHomologyFunctor C 1).obj A).map
            (TopCat.ofHom (homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))) := by
  have hφ := reducedSingularHomologySphereIsoOfOrientation_hom_naturality A _ Complex.orientation
    modelEquiv map_orientation_modelEquiv (finrank_euclideanSpace_ulift_fin 2)
  dsimp only at hφ
  rw [reducedSingularHomologySphereIsoOfOrientation_eq A _ (finrank_euclideanSpace_ulift_fin 2)
    _ rfl] at hφ
  have hsphere : (reducedSingularHomologyTopCatSphereIso A 1).inv ≫
      (reducedSingularHomologyFunctor A 1).map
        (TopCat.ofHom (diskBoundaryHomeomorph.{0} 2).toHomotopyEquiv.toFun) ≫
      (reducedSingularHomologyFunctor A 1).map
        (TopCat.ofHom ⟨modelEquiv.toLinearIsometry.unitSphereMap,
          modelEquiv.toLinearIsometry.continuous_unitSphereMap⟩) =
      (reducedSingularHomologySphereIsoOfOrientation A Complex.orientation
          Complex.finrank_real_complex).inv := by
    rw [← cancel_mono (reducedSingularHomologySphereIsoOfOrientation A Complex.orientation
      Complex.finrank_real_complex).hom, Iso.inv_hom_id, Category.assoc, Category.assoc, hφ]
    -- `reducedSingularHomologyTopCatSphereIso_hom` is stated on `TopCat.sphere 1`, whose maps out
    -- of it are written on `TopCat.diskBoundary 2` here, so it is applied by transport.
    exact (reducedSingularHomologyTopCatSphereIso_hom A 1 ▸
      (reducedSingularHomologyTopCatSphereIso A 1).inv_hom_id :)
  rw [singularHomologyOneIso_inv, sphereOneIsoCircleUnlifted_hom_eq, ← hsphere]
  -- The source of the composite is `TopCat.sphere 1` on one side and `TopCat.diskBoundary 2` on
  -- the other, which agree only after unfolding; hence `erw` and the closing `rfl`.
  erw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [(reducedSingularHomologyι A 1).naturality_assoc,
    (reducedSingularHomologyι A 1).naturality_assoc]
  rfl

end Circle
