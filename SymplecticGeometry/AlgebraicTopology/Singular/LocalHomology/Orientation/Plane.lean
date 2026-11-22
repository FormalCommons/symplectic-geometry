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
linear isometry carrying `o` to `Complex.orientation`. For a point `p` of `E`, Tau Ceti's oriented
local homology isomorphism `H₂(E, E ∖ {p}; ℤ) ≅ ℤ` of the identity chart
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation`) is the connecting morphism of the pair
`(E, E ∖ {p})`, followed by the map `y ↦ φ (y - p) / |φ (y - p)|` of `E ∖ {p}` to `Circle`, which is
radial projection (`Circle.radialProjection`) after translation by `-p` and `φ`, and then by
`Circle.singularHomologyOneIso`.

The proof combines the description of the isomorphism of the identity chart through radial
projection onto the unit sphere (`TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom`),
the naturality of the oriented generator of the sphere under linear isometries
(`TauCeti.reducedSingularHomologySphereIsoOfOrientation_hom_naturality`), and the identification
of the generator of `Circle.singularHomologyOneIso` with the one selected by `Complex.orientation`
(`Circle.singularHomologyOneIso_inv_eq_complexOrientation`).

## Main results

* `TauCeti.singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection`: the
  oriented local homology isomorphism of the identity chart of `E` at `p`, read through the
  connecting morphism, `φ` and radial projection in `H₁(Circle; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (the long exact
  sequence of a pair) and Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Metric Module

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The local homology of an oriented plane, read in `Circle`.** Let `E` be a real inner
product space of dimension two, oriented by `o`, and `φ : E ≃ₗᵢ[ℝ] ℂ` a linear isometry carrying
`o` to `Complex.orientation`. At a point `p` of `E`, the oriented local homology isomorphism
`H₂(E, E ∖ {p}; ℤ) ≅ ℤ` of the identity chart is the connecting morphism of `(E, E ∖ {p})`,
followed by the map `y ↦ φ (y - p) / |φ (y - p)|` of `E ∖ {p}` to `Circle` (radial projection
after translation by `-p` and `φ`) and by `Circle.singularHomologyOneIso`. -/
theorem singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq_radialProjection
    (o : Orientation ℝ E (Fin 2)) (hE : finrank ℝ E = 2) (p : E) (φ : E ≃ₗᵢ[ℝ] ℂ)
    (hφ : o.map (Fin 2) φ.toLinearEquiv = Complex.orientation) :
    (singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{0} ℤ))
        (OpenPartialHomeomorph.refl E) (x := p) (by simp) (n := 1) o hE).hom =
      (TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 1 rfl ≫
        ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom (Circle.radialProjection.comp
            ⟨fun y : ({p}ᶜ : Set E) ↦ ⟨φ ((y : E) - p),
              fun h ↦ y.property (sub_eq_zero.1 ((map_eq_zero_iff φ φ.injective).1 h))⟩,
              by fun_prop⟩)) ≫
        (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  set H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set sC := reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
    Complex.finrank_real_complex
  set h := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  -- The map to `Circle` is radial projection about `p`, then `φ` on unit spheres, then `h`.
  have hdir : TopCat.ofHom (Circle.radialProjection.comp
      ⟨fun y : ({p}ᶜ : Set E) ↦ ⟨φ ((y : E) - p),
        fun h ↦ y.property (sub_eq_zero.1 ((map_eq_zero_iff φ φ.injective).1 h))⟩,
        by fun_prop⟩) =
      TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
        TopCat.ofHom ⟨φ.toLinearIsometry.unitSphereMap,
          φ.toLinearIsometry.continuous_unitSphereMap⟩ ≫ h := by
    ext y
    simp [h, map_smul, -map_sub]
  -- The oriented generator of the unit circle of `ℂ`, read in `Circle`.
  have hC : sC.hom = (reducedSingularHomologyι R 1).app _ ≫ H.map h ≫
      (Circle.singularHomologyOneIso R).hom := by
    rw [← cancel_epi sC.inv, Iso.inv_hom_id, ← Category.assoc, ← Category.assoc,
      Category.assoc sC.inv, ← Circle.singularHomologyOneIso_inv_eq_complexOrientation,
      Iso.inv_hom_id]
  have hnat := reducedSingularHomologySphereIsoOfOrientation_hom_naturality R o
    Complex.orientation φ hφ hE
  dsimp only at hnat
  refine (singularHomologyComplSingletonIsoOfOrientation_refl_hom _ _ _ _).trans ?_
  rw [hdir]
  -- The subspace of the pair is `{p}ᶜ` only after unfolding `TopPair.ofSubset`.
  erw [Functor.map_comp, Functor.map_comp]
  rw [← hnat, hC, ← TopPair.reducedSingularHomologyδ_comp_ι]
  erw [(reducedSingularHomologyι R 1).naturality_assoc,
    (reducedSingularHomologyι R 1).naturality_assoc]
  -- The two sides differ by associativity, which `simp` cannot apply since the source of the
  -- radial projection is the subspace of the pair only after unfolding `TopPair.ofSubset`.
  rfl

end TauCeti

end
