/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
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
complement of the line through `p` is homotopy equivalent to the equator
(`TauCeti.complRayInterHomotopyEquiv`), by radial projection, which is a homotopy equivalence
from any punctured cone `ρ⁻¹ W` over a subset `W` of the sphere onto `W`
(`TauCeti.complZeroPreimageHomotopyEquiv`), followed by `TauCeti.equatorHomotopyEquiv p`. On
`G ∖ {0}` it is radial projection in `G`, so both sides agree after this isomorphism and the
generator of the equator.

## Main definitions

* `TauCeti.complRay p`: the points of `E ∖ {0}` off the open ray through `p`.
* `TauCeti.complZeroOrthogonalInclusion p`: the inclusion of `(ℝ ∙ p)ᗮ ∖ {0}` into
  `complRay p ∩ complRay (-p)`.
* `TauCeti.complZeroPreimageHomotopyEquiv W` and `TauCeti.complRayInterHomotopyEquiv p`: the
  homotopy equivalences above.

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

section Radial

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection sends a point `x ≠ 0` to the point `p` of the unit sphere exactly when `x`
lies on the open ray through `p`. -/
theorem complSingletonHomotopyEquivSphere_zero_apply_eq_iff (x : ({0}ᶜ : Set E))
    (p : sphere (0 : E) 1) :
    complSingletonHomotopyEquivSphere (0 : E) x = p ↔ ∃ t : ℝ, 0 < t ∧ t • (p : E) = x := by
  have hx : 0 < ‖(x : E)‖ := norm_pos_iff.2 x.property
  rw [Subtype.ext_iff, coe_complSingletonHomotopyEquivSphere_apply, sub_zero]
  constructor
  · intro h
    refine ⟨‖(x : E)‖, hx, ?_⟩
    rw [← h, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  · rintro ⟨t, ht, h⟩
    rw [← h, norm_smul, norm_eq_of_mem_sphere p, mul_one, Real.norm_of_nonneg ht.le, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul]

/-- Radial projection is unchanged when a point is scaled by a positive factor. -/
theorem complSingletonHomotopyEquivSphere_zero_smul (x : ({0}ᶜ : Set E)) {c : ℝ} (hc : 0 < c) :
    complSingletonHomotopyEquivSphere (0 : E)
        ⟨c • (x : E), smul_ne_zero hc.ne' x.property⟩ =
      complSingletonHomotopyEquivSphere (0 : E) x := by
  ext1
  simp only [coe_complSingletonHomotopyEquivSphere_apply, sub_zero]
  rw [norm_smul, Real.norm_of_nonneg hc.le, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hc.ne', mul_one]

/-- Radial projection fixes the points of the unit sphere. -/
theorem complSingletonHomotopyEquivSphere_zero_apply_of_mem_sphere (y : sphere (0 : E) 1) :
    complSingletonHomotopyEquivSphere (0 : E) ⟨y, ne_zero_of_mem_unit_sphere y⟩ = y := by
  ext1
  simp [norm_eq_of_mem_sphere y]

variable (W : Set (sphere (0 : E) 1))

/-- The punctured cone over a subset `W` of the unit sphere, the points `x ≠ 0` whose radial
projection lies in `W`, is homotopy equivalent to `W`: radial projection is a homotopy
equivalence, with the inclusion of `W` as homotopy inverse. -/
def complZeroPreimageHomotopyEquiv :
    ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W) ≃ₕ ↥W where
  toFun := ⟨(Set.mapsTo_preimage _ W).restrict, (map_continuous _).restrict _⟩
  invFun := ⟨fun y ↦ ⟨⟨y, ne_zero_of_mem_unit_sphere y.val⟩, by
      simpa only [Set.mem_preimage, complSingletonHomotopyEquivSphere_zero_apply_of_mem_sphere]
        using y.property⟩, by fun_prop⟩
  left_inv := by
    -- Each point moves along its ray, from its radial projection to itself.
    have hc (z : unitInterval × ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W)) :
        0 < (1 - (z.1 : ℝ)) * ‖((z.2 : ({0}ᶜ : Set E)) : E)‖⁻¹ + z.1 := by
      have h := norm_pos_iff.2 z.2.val.property
      rcases eq_or_lt_of_le z.1.property.2 with h1 | h1
      · rw [h1]; norm_num
      · nlinarith [z.1.property.1, inv_pos.2 h]
    refine ⟨{
      toFun := fun z ↦ ⟨⟨((1 - (z.1 : ℝ)) * ‖((z.2 : ({0}ᶜ : Set E)) : E)‖⁻¹ + z.1) •
          ((z.2 : ({0}ᶜ : Set E)) : E), smul_ne_zero (hc z).ne' z.2.val.property⟩, by
        simpa only [Set.mem_preimage, complSingletonHomotopyEquivSphere_zero_smul _ (hc z)]
          using z.2.property⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
        have hx : Continuous
            fun z : unitInterval × ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W) ↦
              ((z.2 : ({0}ᶜ : Set E)) : E) := by fun_prop
        exact (((continuous_const.sub (by fun_prop)).mul (hx.norm.inv₀ fun z ↦
          norm_ne_zero_iff.2 z.2.val.property)).add (by fun_prop)).smul hx
      map_zero_left := fun x ↦ by
        ext1; ext1
        simp
      map_one_left := fun x ↦ by
        ext1; ext1
        simp }⟩
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id ↥W)
    ext y
    exact congrArg Subtype.val (complSingletonHomotopyEquivSphere_zero_apply_of_mem_sphere y.val)

/-- The homotopy equivalence `TauCeti.complZeroPreimageHomotopyEquiv` is radial projection. -/
@[simp]
theorem coe_complZeroPreimageHomotopyEquiv_apply
    (x : ↥(complSingletonHomotopyEquivSphere (0 : E) ⁻¹' W)) :
    (complZeroPreimageHomotopyEquiv W x : sphere (0 : E) 1) =
      complSingletonHomotopyEquivSphere (0 : E) x :=
  (rfl)

/-- The homotopy inverse of `TauCeti.complZeroPreimageHomotopyEquiv` is the inclusion of `W`. -/
@[simp]
theorem coe_complZeroPreimageHomotopyEquiv_symm_apply (y : W) :
    (((complZeroPreimageHomotopyEquiv W).symm y : ({0}ᶜ : Set E)) : E) = y :=
  (rfl)

end Radial

section Suspension

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real vector space has unique division by nonzero natural numbers; this lets Tau Ceti's
cover of a sphere by the complements of two antipodal points apply. -/
local instance : HasUniqueDiv E := HasUniqueDiv.of_isTorsionFree ℝ E

/-- The points of `E ∖ {0}` off the open ray `{t • p | t > 0}` through a point `p` of the unit
sphere: those whose radial projection is not `p` (`TauCeti.mem_complRay_iff`). -/
def complRay (p : sphere (0 : E) 1) : Set ({0}ᶜ : Set E) :=
  complSingletonHomotopyEquivSphere (0 : E) ⁻¹' {p}ᶜ

theorem complRay_def (p : sphere (0 : E) 1) :
    complRay p = complSingletonHomotopyEquivSphere (0 : E) ⁻¹' {p}ᶜ :=
  (rfl)

/-- A point lies in `TauCeti.complRay p` exactly when it is not a positive multiple of `p`. -/
theorem mem_complRay_iff {p : sphere (0 : E) 1} {x : ({0}ᶜ : Set E)} :
    x ∈ complRay p ↔ ∀ t : ℝ, 0 < t → t • (p : E) ≠ x := by
  rw [complRay_def, Set.mem_preimage, Set.mem_compl_singleton_iff, Ne,
    complSingletonHomotopyEquivSphere_zero_apply_eq_iff]
  push Not
  rfl

theorem isOpen_complRay (p : sphere (0 : E) 1) : IsOpen (complRay p) :=
  isOpen_compl_singleton.preimage (map_continuous _)

/-- Radial projection carries `TauCeti.complRay p` into the complement of `p` in the sphere. -/
theorem mapsTo_complRay (p : sphere (0 : E) 1) :
    Set.MapsTo (complSingletonHomotopyEquivSphere (0 : E)) (complRay p) {p}ᶜ :=
  Set.mapsTo_preimage _ _

/-- The complements of the two rays through `p` and `-p` cover `E ∖ {0}`. -/
theorem complRay_union_complRay_neg (p : sphere (0 : E) 1) :
    complRay p ∪ complRay (-p) = Set.univ := by
  rw [complRay_def, complRay_def, ← Set.preimage_union,
    compl_singleton_union_compl_singleton_neg one_ne_zero p, Set.preimage_univ]

/-- The points `x ≠ 0` of the orthogonal complement of a unit vector `p` lie off the line through
`p`: they are in neither `TauCeti.complRay p` nor `TauCeti.complRay (-p)`. -/
theorem mem_complRay_inter_complRay_neg_of_mem_orthogonal (p : sphere (0 : E) 1)
    (x : ({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ)) :
    (⟨(x : (ℝ ∙ (p : E))ᗮ), fun h ↦ x.property (Subtype.ext h)⟩ : ({0}ᶜ : Set E)) ∈
      complRay p ∩ complRay (-p) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (x : (ℝ ∙ (p : E))ᗮ).property
  have hp : inner ℝ (p : E) (p : E) ≠ 0 := by simp
  refine ⟨mem_complRay_iff.2 fun t ht h ↦ ?_, mem_complRay_iff.2 fun t ht h ↦ ?_⟩
  · rw [← h, inner_smul_right] at hx
    exact hp ((mul_eq_zero.1 hx).resolve_left ht.ne')
  · rw [← h, coe_neg_sphere, smul_neg, inner_neg_right, inner_smul_right, neg_eq_zero] at hx
    exact hp ((mul_eq_zero.1 hx).resolve_left ht.ne')

/-- The inclusion of the punctured orthogonal complement `(ℝ ∙ p)ᗮ ∖ {0}` of a unit vector `p`
into the complement in `E ∖ {0}` of the line through `p`, the intersection of
`TauCeti.complRay p` and `TauCeti.complRay (-p)`. -/
def complZeroOrthogonalInclusion (p : sphere (0 : E) 1) :
    C(↥({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ), ↥(complRay p ∩ complRay (-p))) where
  toFun x := ⟨_, mem_complRay_inter_complRay_neg_of_mem_orthogonal p x⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_complZeroOrthogonalInclusion_apply (p : sphere (0 : E) 1)
    (x : ({0}ᶜ : Set (ℝ ∙ (p : E))ᗮ)) :
    ((complZeroOrthogonalInclusion p x : ({0}ᶜ : Set E)) : E) = (x : (ℝ ∙ (p : E))ᗮ) :=
  (rfl)

/-- **The complement of a line is homotopy equivalent to the equator.** For a point `p` of the
unit sphere, the points of `E ∖ {0}` off the line through `p`, the intersection of
`TauCeti.complRay p` and `TauCeti.complRay (-p)`, form a space homotopy equivalent to the unit
sphere of `(ℝ ∙ p)ᗮ`: radial projection onto the sphere minus `±p`, followed by
`TauCeti.equatorHomotopyEquiv p`. -/
def complRayInterHomotopyEquiv (p : sphere (0 : E) 1) :
    ↥(complRay p ∩ complRay (-p)) ≃ₕ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
  (complZeroPreimageHomotopyEquiv ({p}ᶜ ∩ {-p}ᶜ)).trans (equatorHomotopyEquiv p)

/-- `TauCeti.complRayInterHomotopyEquiv p` is the restriction of radial projection, followed by
`TauCeti.equatorHomotopyEquiv p`. -/
theorem complRayInterHomotopyEquiv_toFun (p : sphere (0 : E) 1) :
    (complRayInterHomotopyEquiv p).toFun = (equatorHomotopyEquiv p).toFun.comp
      ⟨((mapsTo_complRay p).inter_inter (mapsTo_complRay (-p))).restrict,
        (map_continuous _).restrict _⟩ :=
  (rfl)

/-- On the punctured orthogonal complement `(ℝ ∙ p)ᗮ ∖ {0}`, the homotopy equivalence
`TauCeti.complRayInterHomotopyEquiv p` is radial projection in `(ℝ ∙ p)ᗮ`. -/
theorem complRayInterHomotopyEquiv_toFun_comp_complZeroOrthogonalInclusion
    (p : sphere (0 : E) 1) :
    (complRayInterHomotopyEquiv p).toFun.comp (complZeroOrthogonalInclusion p) =
      (complSingletonHomotopyEquivSphere (0 : (ℝ ∙ (p : E))ᗮ)).toFun := by
  ext x
  have hpos : 0 < ‖(x : (ℝ ∙ (p : E))ᗮ)‖ := norm_pos_iff.2 x.property
  rw [complRayInterHomotopyEquiv_toFun, ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  -- Both maps are `HomotopyEquiv.toFun`s; this applies the evaluation lemmas, which are stated
  -- with the coercion of the homotopy equivalences.
  change ((equatorHomotopyEquiv p ⟨complSingletonHomotopyEquivSphere (0 : E)
      (complZeroOrthogonalInclusion p x).val, (complZeroOrthogonalInclusion p x).property⟩ :
        (ℝ ∙ (p : E))ᗮ) : E) =
    ((complSingletonHomotopyEquivSphere (0 : (ℝ ∙ (p : E))ᗮ) x : (ℝ ∙ (p : E))ᗮ) : E)
  rw [coe_equatorHomotopyEquiv_apply, coe_complSingletonHomotopyEquivSphere_apply,
    coe_complSingletonHomotopyEquivSphere_apply, coe_complZeroOrthogonalInclusion_apply]
  simp only [sub_zero, Submodule.coe_smul, Submodule.norm_coe]
  rw [Submodule.starProjection_eq_self_iff.2 (Submodule.smul_mem _ _ (x : (ℝ ∙ (p : E))ᗮ).property),
    NormedSpace.normalize_smul_of_pos (inv_pos.2 hpos), NormedSpace.normalize, Submodule.norm_coe]

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
