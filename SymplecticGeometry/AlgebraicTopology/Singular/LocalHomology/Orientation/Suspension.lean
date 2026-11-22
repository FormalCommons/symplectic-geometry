/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import SymplecticGeometry.Topology.Homotopy.PuncturedStarConvex
public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# The sphere suspension read in local homology

Let `b` be an orthonormal basis of a real inner product space `E` of dimension `m + 2`, `p` its
last vector and `G = (ℝ ∙ p)ᗮ`. Cover `E ∖ {0}` by `TauCeti.complRay p` and
`TauCeti.complRay (-p)`, the points off the open rays `{t • p | t > 0}` and `{t • p | t < 0}`;
their intersection is the complement of the line through `p`, which contains `G ∖ {0}`. This file
shows that the Mayer–Vietoris connecting morphism `Hₘ₊₁(E ∖ {0}) ⟶ Hₘ(E ∖ ℝ p)` of this cover
sends the boundary of the local orientation of `E` at `0` selected by the orientation of `b` to
the image of the boundary of the local orientation of `G` at `0` selected by the orientation of
`b.orthogonalLast`, with sign `+1` in every dimension
(`TauCeti.mayerVietorisδ_singularHomologyδ_localOrientation`), and the same for the local
homology isomorphisms of the identity charts with any coefficients
(`TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ`).

There is no sign because Tau Ceti's sphere generators are built by the same suspension: the
generator of `H̃ₘ₊₁(S)` selected by `b` is the reduced Mayer–Vietoris morphism of the cover of the
unit sphere by the complements of `p` and `-p`, followed by `TauCeti.equatorHomotopyEquiv p` and
the generator of the equator selected by `b.orthogonalLast`
(`TauCeti.reducedSingularHomologySphereIsoOfOrientation_hom_eq_reducedMayerVietorisδ`). Radial
projection `E ∖ {0} ⟶ S` carries the cover by the ray complements into this cover of the sphere,
so the naturality of the reduced Mayer–Vietoris morphism moves the computation to the sphere. The
complement of the line through `p` is homotopy equivalent to the equator by radial projection
followed by `TauCeti.equatorHomotopyEquiv p` (`TauCeti.complRayInterHomotopyEquiv`, in
`SymplecticGeometry/Topology/Homotopy/PuncturedStarConvex.lean`, with the cover by the ray
complements). On `G ∖ {0}` it is radial projection in `G`, so both sides agree after this
isomorphism and the generator of the equator.

## Main results

* `TauCeti.singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ`:
  the suspension identity for the oriented local homology isomorphisms, any coefficients.
* `TauCeti.mayerVietorisδ_singularHomologyδ_localOrientation`: the same for the local
  orientations, with coefficients `ULift ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (Example 2.46: the homology of spheres by the Mayer–Vietoris sequence) and
  Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Metric Module
open scoped ContinuousMap

universe w v u

namespace TauCeti

section Suspension

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real vector space has unique division by nonzero natural numbers; this lets Tau Ceti's
cover of a sphere by the complements of two antipodal points apply. -/
local instance : HasUniqueDiv E := HasUniqueDiv.of_isTorsionFree ℝ E

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) {m : ℕ}
  (b : OrthonormalBasis (Fin (m + 2)) ℝ E)

/-- **The sphere generator through the suspension isomorphism.** For an orthonormal basis `b` of
a space of dimension `m + 2` and `p` its last vector, the generator of `H̃ₘ₊₁(S)` selected by the
orientation of `b` is the reduced Mayer–Vietoris morphism of the cover of `S` by the complements
of `p` and `-p`, followed by `TauCeti.equatorHomotopyEquiv p` and the generator of the equator
selected by the orientation of `b.orthogonalLast`. -/
theorem reducedSingularHomologySphereIsoOfOrientation_hom_eq_reducedMayerVietorisδ :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (reducedSingularHomologySphereIsoOfOrientation R b.toBasis.orientation
        ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).hom =
      (reducedSingularHomologyι R (m + 1)).app (TopCat.of (sphere (0 : E) 1)) ≫
        TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
          isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg one_ne_zero p) m ≫
        (reducedSingularHomologyFunctor R m).map (TopCat.ofHom (equatorHomotopyEquiv p).toFun) ≫
        (reducedSingularHomologySphereIsoOfOrientation R b.orthogonalLast.toBasis.orientation
          ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).hom := by
  intro p
  rw [reducedSingularHomologySphereIsoOfOrientation_eq R _ _ b rfl,
    reducedSingularHomologySphereIso_succ, Iso.trans_hom, reducedSingularHomologySphereSuccIso_hom,
    reducedSingularHomologySphereIsoOfOrientation_eq R _ _ b.orthogonalLast rfl]
  -- The equators of `p` and of `⟨b (Fin.last _), _⟩` agree only after unfolding `p`.
  erw [Category.assoc, Category.assoc]

/-- The local homology generator of `E` at `0` selected by the orientation of `b`, read through
the connecting morphism of `(E, E ∖ {0})`, the reduced Mayer–Vietoris morphism of the cover of
`E ∖ {0}` by `TauCeti.complRay p` and `TauCeti.complRay (-p)`, `p` the last vector of `b`,
`TauCeti.complRayInterHomotopyEquiv p` and the generator of the equator selected by the
orientation of `b.orthogonalLast`. -/
theorem singularHomologyδ_reducedMayerVietorisδ_complRayInterHomotopyEquiv :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      TopCat.reducedMayerVietorisδ R (X := TopCat.of ({0}ᶜ : Set E)) (isOpen_complRay p)
        (isOpen_complRay (-p)) (complRay_union_complRay_neg p) m ≫
      (reducedSingularHomologyFunctor R m).map
        (TopCat.ofHom (complRayInterHomotopyEquiv p).toFun) ≫
      (reducedSingularHomologySphereIsoOfOrientation R b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).hom =
    (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) (x := 0)
      (OpenPartialHomeomorph.mem_refl_source _) b.toBasis.orientation
      ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).hom := by
  intro p
  refine Eq.trans ?_ (singularHomologyComplSingletonIsoOfOrientation_refl_hom R _ _ _).symm
  rw [reducedSingularHomologySphereIsoOfOrientation_hom_eq_reducedMayerVietorisδ,
    complRayInterHomotopyEquiv_toFun, TopCat.ofHom_comp, Functor.map_comp, Category.assoc]
  -- Radial projection `E ∖ {0} ⟶ S` carries the cover by the two ray complements into the cover
  -- of `S` by the complements of `p` and `-p`.
  erw [TopCat.reducedMayerVietorisδ_naturality_assoc R _ _ _ _ _ _
      (TopCat.ofHom (complSingletonHomotopyEquivSphere (0 : E)).toFun) (mapsTo_complRay p)
      (mapsTo_complRay (-p)) m,
    (reducedSingularHomologyι R (m + 1)).naturality_assoc,
    TopPair.reducedSingularHomologyδ_comp_ι_assoc]
  -- The two sides differ in how the map of radial projection on homology is written: through the
  -- singular simplicial set, or through `singularHomologyFunctor`, which is defined from it.
  rfl

/-- The local homology generator of `(ℝ ∙ p)ᗮ` at `0` selected by the orientation of
`b.orthogonalLast`, `p` the last vector of `b`, read through the connecting morphism of
`((ℝ ∙ p)ᗮ, (ℝ ∙ p)ᗮ ∖ {0})`, the inclusion into the complement of the line through `p`,
`TauCeti.complRayInterHomotopyEquiv p`, and the generator of the equator. -/
theorem reducedSingularHomologyδ_complZeroOrthogonalInclusion_complRayInterHomotopyEquiv :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).reducedSingularHomologyδ R m ≫
      (reducedSingularHomologyFunctor R m).map (TopCat.ofHom (complZeroOrthogonalInclusion p)) ≫
      (reducedSingularHomologyFunctor R m).map
        (TopCat.ofHom (complRayInterHomotopyEquiv p).toFun) ≫
      (reducedSingularHomologySphereIsoOfOrientation R b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).hom =
    (singularHomologyComplSingletonIsoOfOrientation R
      (OpenPartialHomeomorph.refl (ℝ ∙ (p : E))ᗮ) (x := 0)
      (OpenPartialHomeomorph.mem_refl_source _) b.orthogonalLast.toBasis.orientation
      ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).hom := by
  intro p
  refine Eq.trans ?_ (singularHomologyComplSingletonIsoOfOrientation_refl_hom R _ _ _).symm
  -- The subspace of the pair is `TopCat.of {0}ᶜ` only after unfolding `TopPair.ofSubset`.
  erw [← Functor.map_comp_assoc, ← TopCat.ofHom_comp,
    complRayInterHomotopyEquiv_toFun_comp_complZeroOrthogonalInclusion]

/-- **The sphere suspension in local homology.** Let `b` be an orthonormal basis of a real inner
product space `E` of dimension `m + 2`, `p` its last vector and `G = (ℝ ∙ p)ᗮ`. Cover `E ∖ {0}`
by the complements `TauCeti.complRay p` and `TauCeti.complRay (-p)` of the open rays through `p`
and `-p`. Then the connecting morphism of `(E, E ∖ {0})`, followed by the Mayer–Vietoris
connecting morphism of this cover, agrees on the local homology generator selected by the
orientation of `b` with the connecting morphism of `(G, G ∖ {0})`, followed by the inclusion of
`G ∖ {0}` into the intersection of the cover, on the generator selected by the orientation of
`b.orthogonalLast`, with no sign. -/
theorem singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) b.toBasis.orientation
        ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      TopCat.mayerVietorisδ R (X := TopCat.of ({0}ᶜ : Set E)) (isOpen_complRay p)
        (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m =
    (singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (ℝ ∙ (p : E))ᗮ) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomologyδ R (m + 1) m ≫
      ((singularHomologyFunctor C m).obj R).map
        (TopCat.ofHom (complZeroOrthogonalInclusion p)) := by
  intro p
  -- Both sides agree in reduced homology, as they agree after the isomorphism to the equator
  -- given by `complRayInterHomotopyEquiv p` and the generator of the equator.
  have hred : (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E)
        (x := 0) (OpenPartialHomeomorph.mem_refl_source _) b.toBasis.orientation
        ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ R (m + 2) (m + 1) ≫
      TopCat.reducedMayerVietorisδ R (X := TopCat.of ({0}ᶜ : Set E)) (isOpen_complRay p)
        (isOpen_complRay (-p)) (complRay_union_complRay_neg p) m =
    (singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (ℝ ∙ (p : E))ᗮ) (x := 0)
        (OpenPartialHomeomorph.mem_refl_source _) b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).inv ≫
      (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).reducedSingularHomologyδ R m ≫
      (reducedSingularHomologyFunctor R m).map (TopCat.ofHom (complZeroOrthogonalInclusion p)) := by
    rw [← cancel_mono (((complRayInterHomotopyEquiv p).reducedSingularHomologyIso R m) ≪≫
      reducedSingularHomologySphereIsoOfOrientation R b.orthogonalLast.toBasis.orientation
        ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans (Fintype.card_fin _))).hom,
      Iso.trans_hom, ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom, Category.assoc]
    conv_rhs => rw [Category.assoc, Category.assoc,
      reducedSingularHomologyδ_complZeroOrthogonalInclusion_complRayInterHomotopyEquiv,
      Iso.inv_hom_id]
    -- The target of the connecting morphism of the pair is `{0}ᶜ` after unfolding
    -- `TopPair.ofSubset`.
    erw [Category.assoc, singularHomologyδ_reducedMayerVietorisδ_complRayInterHomotopyEquiv,
      Iso.inv_hom_id]
  -- Pass back to ordinary homology through the inclusion of reduced homology. The connecting
  -- morphisms target the subspaces of the pairs, which are `{0}ᶜ` after unfolding
  -- `TopPair.ofSubset`, so the rewrites go through `erw`.
  have h := hred =≫ (reducedSingularHomologyι R m).app (TopCat.of ↥(complRay p ∩ complRay (-p)))
  erw [Category.assoc, Category.assoc] at h
  rw [← TopCat.reducedMayerVietorisδ_comp_ι]
  erw [h, ← TopPair.reducedSingularHomologyδ_comp_ι_assoc,
    ← (reducedSingularHomologyι R m).naturality, Category.assoc, Category.assoc]

/-- **The sphere suspension for local orientations.** Let `b` be an orthonormal basis of a real
inner product space `E` of dimension `m + 2`, `p` its last vector and `G = (ℝ ∙ p)ᗮ`. Cover
`E ∖ {0}` by the complements `TauCeti.complRay p` and `TauCeti.complRay (-p)` of the open rays
through `p` and `-p`. The Mayer–Vietoris connecting morphism of this cover sends the boundary in
`E ∖ {0}` of the local orientation of `E` selected by the orientation of `b` to the image, under
the inclusion `G ∖ {0} ⊆ E ∖ ℝ p`, of the boundary in `G ∖ {0}` of the local orientation of `G`
selected by the orientation of `b.orthogonalLast`. -/
theorem mayerVietorisδ_singularHomologyδ_localOrientation :
    let p : sphere (0 : E) 1 := ⟨b (Fin.last _), by simp⟩
    TopCat.mayerVietorisδ (ModuleCat.of ℤ (ULift.{w} ℤ)) (X := TopCat.of ({0}ᶜ : Set E))
        (isOpen_complRay p) (isOpen_complRay (-p)) (complRay_union_complRay_neg p) (m + 1) m rfl
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of E))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 2) (m + 1) rfl
          (b.toBasis.orientation.localOrientation
            ((finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _))).val) =
      ((singularHomologyFunctor (ModuleCat.{w} ℤ) m).obj (ModuleCat.of ℤ (ULift.{w} ℤ))).map
        (TopCat.ofHom (complZeroOrthogonalInclusion p))
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (ℝ ∙ (p : E))ᗮ))).singularHomologyδ
          (ModuleCat.of ℤ (ULift.{w} ℤ)) (m + 1) m rfl
          (b.orthogonalLast.toBasis.orientation.localOrientation
            ((finrank_eq_card_basis b.orthogonalLast.toBasis).trans
              (Fintype.card_fin _))).val) := by
  intro p
  rw [Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    Orientation.localOrientation_eq_localOrientationOfOrientedChart_refl,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  -- Evaluate the identity of morphisms at `1`. A composite applied to an element is the
  -- composition of the applications by definition; `ConcreteCategory.comp_apply` does not
  -- rewrite here, as the middle objects of the composites agree only after unfolding
  -- `TopPair.ofSubset`.
  exact congrArg (fun f ↦ f 1)
    (singularHomologyComplSingletonIsoOfOrientation_inv_singularHomologyδ_mayerVietorisδ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) b)

end Suspension

end TauCeti
