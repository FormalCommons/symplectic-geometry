/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.Analysis.Complex.RadialProjection

/-!
# The local homology of an oriented plane, read in `Circle`

Let `E` be a real inner product space of dimension two, oriented by `o`, and `φ : E ≃ₗᵢ[ℝ] ℂ` a
linear isometry carrying `o` to `Complex.orientation`, and let `A` be an object of an abelian
category with coproducts. For a point `p` of `E`, Tau Ceti's oriented local homology isomorphism
`H₂(E, E ∖ {p}; A) ≅ A` of the identity chart
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation`) is the connecting morphism of the pair
`(E, E ∖ {p})`, followed by the map `Circle.radialProjectionAt φ p : E ∖ {p} → Circle`,
`y ↦ φ (y - p) / |φ (y - p)|`, and then by `Circle.singularHomologyOneIso`.

The proof combines the description of the isomorphism of the identity chart through radial
projection onto the unit sphere (`TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom`),
the naturality of the oriented generator of the sphere under linear isometries
(`TauCeti.reducedSingularHomologySphereIsoOfOrientation_hom_naturality`), and the identification
of the generator of `Circle.singularHomologyOneIso` with the one selected by `Complex.orientation`
(`Circle.singularHomologyOneIso_inv_eq_complexOrientation`).

## Main results

* `TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection`: the
  oriented local homology isomorphism of the identity chart of `E` at `p`, read through the
  connecting morphism and `Circle.radialProjectionAt φ p` in `H₁(Circle; A) ≅ A`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (the long exact
  sequence of a pair) and Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (A : C)
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The local homology of an oriented plane, read in `Circle`.** Let `E` be a real inner
product space of dimension two, oriented by `o`, and `φ : E ≃ₗᵢ[ℝ] ℂ` a linear isometry carrying
`o` to `Complex.orientation`, and `A` an object of an abelian category with coproducts. At a
point `p` of `E`, the oriented local homology isomorphism
`H₂(E, E ∖ {p}; A) ≅ A` of the identity chart is the connecting morphism of `(E, E ∖ {p})`,
followed by the map `Circle.radialProjectionAt φ p : E ∖ {p} → Circle`,
`y ↦ φ (y - p) / |φ (y - p)|`, and by `Circle.singularHomologyOneIso`. -/
theorem singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection
    (o : Orientation ℝ E (Fin 2)) (hE : finrank ℝ E = 2) (p : E) (φ : E ≃ₗᵢ[ℝ] ℂ)
    (hφ : o.map (Fin 2) φ.toLinearEquiv = Complex.orientation) :
    (singularHomologyComplSingletonIsoOfOrientation A
        (OpenPartialHomeomorph.refl E) (x := p) (by simp) (n := 1) o hE).hom =
      (TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).singularHomologyδ A 2 1 rfl ≫
        ((singularHomologyFunctor C 1).obj A).map
          (TopCat.ofHom (Circle.radialProjectionAt φ p)) ≫
        (Circle.singularHomologyOneIso A).hom := by
  set sC := reducedSingularHomologySphereIsoOfOrientation A Complex.orientation
    Complex.finrank_real_complex
  set h := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  -- The map to `Circle` is radial projection about `p`, then `φ` on unit spheres, then `h`.
  have hdir : TopCat.ofHom (Circle.radialProjectionAt φ p) =
      TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
        TopCat.ofHom ⟨φ.toLinearIsometry.unitSphereMap,
          φ.toLinearIsometry.continuous_unitSphereMap⟩ ≫ h := by
    ext y
    simp [h, map_smul, -map_sub]
  -- The oriented generator of the unit circle of `ℂ`, read in `Circle`.
  have hC : sC.hom = (reducedSingularHomologyι A 1).app _ ≫
      ((singularHomologyFunctor C 1).obj A).map h ≫
      (Circle.singularHomologyOneIso A).hom := by
    rw [← cancel_epi sC.inv, Iso.inv_hom_id, ← Category.assoc, ← Category.assoc,
      Category.assoc sC.inv, ← Circle.singularHomologyOneIso_inv_eq_complexOrientation,
      Iso.inv_hom_id]
  have hnat := reducedSingularHomologySphereIsoOfOrientation_hom_naturality A o
    Complex.orientation φ hφ hE
  dsimp only at hnat
  refine (singularHomologyComplSingletonIsoOfOrientation_refl_hom _ _ _ _).trans ?_
  rw [hdir]
  -- The subspace of the pair is `{p}ᶜ` only after unfolding `TopPair.ofSubset`.
  erw [Functor.map_comp, Functor.map_comp]
  rw [← hnat, hC, ← TopPair.reducedSingularHomologyδ_comp_ι]
  erw [(reducedSingularHomologyι A 1).naturality_assoc,
    (reducedSingularHomologyι A 1).naturality_assoc]
  erw [Category.assoc, Category.assoc, Category.assoc]
  -- The two sides now differ only in the implicit objects: the source of the radial projection
  -- is written `{p}ᶜ` on one side and as the subspace of the pair `TopPair.ofSubset {p}ᶜ` on the
  -- other, which agree after unfolding `TopPair.ofSubset`.
  rfl

end TauCeti

end
