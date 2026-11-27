/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryClass
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.DiscBoundaryClass
public import SymplecticGeometry.Analysis.Complex.RadialProjection
public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.Circle.Degree
import SymplecticGeometry.AlgebraicTopology.Singular.CircleMap
import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Complex

/-!
# The boundary degree of a circle-valued map

We work in the setting of Tau Ceti's relative fundamental class
(`TauCeti.HomologicalOrientation.fundamentalClassRel`) for surfaces: `X` is compact
Hausdorff, `ι : M → X` is an open embedding of a surface oriented by `o`, and the complement
`∂X = X ∖ ι(M)` is the image of a collared map. Its boundary class `∂[X, ∂X] ∈ H₁(∂X; ℤ)`
(`TauCeti.HomologicalOrientation.boundaryClass`, in
`SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.BoundaryClass`) vanishes in the
homology of `X` and changes sign with the orientation.

A map `u : ∂X → S¹` sends the boundary class to `H₁(S¹; ℤ) ≅ ℤ`
(`Circle.singularHomologyOneIso`); the resulting integer is the *boundary degree* of `u`
(`TauCeti.HomologicalOrientation.boundaryDegree`). Tau Ceti fixes no sign convention for its
connecting morphisms, so we check the sign on the closed unit disc of `ℂ`: there the boundary
circle, which runs counterclockwise, has boundary degree `1`
(`SymplecticGeometry.boundaryDegree_closedBallComplToCircle`), so the boundary class is the
generator (`SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`). No sign has
to be inserted.

For `u = G / |G|` with `G : X → ℂ` nonzero on `∂X`, the map `G` is a map of pairs
`(X, ∂X) ⟶ (ℂ, ℂ ∖ {0})` that, followed by radial projection (`Circle.radialProjection`), is `u`
on `∂X`; by naturality of the connecting morphism, the boundary degree of `u` is read off from
`G_*[X, ∂X]`. This step follows Tau Ceti's
`TauCeti.localHomologyMap_translate_comp_reducedSingularHomologyδ` and
`TauCeti.snd_ofSubsetMap_translate_comp_complSingletonHomotopyEquivSphere`, which compare the
connecting morphisms and radial projections of the model at two points along a translation; here
the map is `G`. On the disc, `G` is the inclusion into `ℂ`, which sends the fundamental class to
the local orientation of `ℂ` at the origin
(`SymplecticGeometry.localHomologyMap_fundamentalClassRel_closedBall`).

## Main definitions

* `TauCeti.HomologicalOrientation.boundaryDegree`: the boundary degree of `u : ∂X → S¹`.

## Main results

* `TauCeti.HomologicalOrientation.boundaryDegree_mul`: pointwise products add boundary degrees,
  since circle-valued maps act additively on `H₁` (`ContinuousMap.singularHomologyFunctor_map_mul`).
* `TauCeti.HomologicalOrientation.boundaryDegree_one`,
  `TauCeti.HomologicalOrientation.boundaryDegree_inv`: the constant map `1` has boundary degree
  `0`, and inverting a map negates its boundary degree.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_of_homotopy`: homotopy invariance.
* `TauCeti.HomologicalOrientation.boundaryDegree_neg_orientation`: reversing the orientation
  negates the boundary degree.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_zero_of_extend`: a map that extends
  continuously over `X` has boundary degree `0`.
* `TauCeti.HomologicalOrientation.boundaryDegree_comp_homeomorph`: invariance under a homeomorphism
  `h : X ≃ₜ X'` that restricts to a homeomorphism `φ : M ≃ₜ M'`, for the pulled-back orientation
  `o'.comap φ`, from `TauCeti.HomologicalOrientation.map_boundaryClass_comap`.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_sum_degree`: if loops in `∂X` represent the
  boundary class, the boundary degree is the sum of the degrees (`Circle.degree`) of `u` along them.
* `TauCeti.HomologicalOrientation.boundaryDegree_eq_of_localHomologyMap`,
  `TauCeti.HomologicalOrientation.boundaryDegree_eq_of_localHomologyMap_eq_zsmul`: for
  `u = G / |G|` with `G : X → ℂ` nonzero on `∂X`, the boundary degree of `u` is read off from
  `G_*[X, ∂X] ∈ H₂(ℂ, ℂ ∖ {0})`, by naturality of the connecting morphism; it is `c` when
  `G_*[X, ∂X]` is `c` times the local orientation of `ℂ` at the origin.
* `SymplecticGeometry.boundaryDegree_closedBallComplToCircle`: the sign on the unit disc.
* `SymplecticGeometry.singularHomologyOneIso_map_boundaryClass_closedBall`: the boundary class of
  the closed unit disc is `1` in `H₁(Circle; ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3: the fundamental
  class of a compact manifold with boundary and its image in the homology of the boundary.
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: degrees
  of circle-valued maps on the boundary of a surface.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Set Topology Module Metric

namespace TauCeti.HomologicalOrientation

variable {X M : Type} {N : Type*} [TopologicalSpace X] [TopologicalSpace N] [TopologicalSpace M]
  [T2Space X] [CompactSpace X] [T2Space M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M] {ι : M → X} {f : N → X}

variable (o : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2) (hι : IsOpenEmbedding ι)
  (hιf : range ι = (range f)ᶜ) (hf : IsCollared f)

/-- **The boundary degree of a circle-valued map.** For a compact surface `X` with collared
boundary `∂X`, the complement of `ι(M)`, and `u : ∂X → S¹`: the image under `u` of the boundary
class `∂[X, ∂X] ∈ H₁(∂X; ℤ)`, read in `ℤ` through `Circle.singularHomologyOneIso`. With this
sign, the counterclockwise boundary of the closed unit disc of `ℂ` has boundary degree `1`
(`SymplecticGeometry.boundaryDegree_closedBallComplToCircle`). -/
def boundaryDegree (u : C(↥((range ι)ᶜ : Set X), Circle)) : ℤ :=
  ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
      (TopCat.ofHom u)).hom (o.boundaryClass hn hι hιf hf))).down

theorem boundaryDegree_def (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf u =
      ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom.hom
        ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom u)).hom (o.boundaryClass hn hι hιf hf))).down :=
  (rfl)

/-- The boundary degree of a pointwise product is the sum of the boundary degrees. -/
theorem boundaryDegree_mul (u v : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf (u * v) =
      o.boundaryDegree hn hι hιf hf u + o.boundaryDegree hn hι hιf hf v := by
  simp only [boundaryDegree_def, ContinuousMap.singularHomologyFunctor_map_mul, ModuleCat.hom_add,
    LinearMap.add_apply, map_add, ULift.add_down]

/-- Homotopic maps `∂X → S¹` have the same boundary degree. -/
theorem boundaryDegree_eq_of_homotopy {u v : C(↥((range ι)ᶜ : Set X), Circle)}
    (F : u.Homotopy v) :
    o.boundaryDegree hn hι hιf hf u = o.boundaryDegree hn hι hιf hf v := by
  have hF : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom u) =
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom v) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom u) (g := TopCat.ofHom v) F (ModuleCat.of ℤ (ULift.{0} ℤ)) 1
  rw [boundaryDegree_def, boundaryDegree_def, hF]

/-- Reversing the orientation negates the boundary degree. -/
@[simp]
theorem boundaryDegree_neg_orientation (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    (-o).boundaryDegree hn hι hιf hf u = -o.boundaryDegree hn hι hιf hf u := by
  simp only [boundaryDegree_def, boundaryClass_neg, map_neg, ULift.neg_down]

/-- A map `∂X → S¹` that extends continuously to `X` has boundary degree `0`, since the boundary
class vanishes in `H₁(X; ℤ)`. -/
theorem boundaryDegree_eq_zero_of_extend {u : C(↥((range ι)ᶜ : Set X), Circle)}
    (v : C(X, Circle)) (hv : ∀ z : ↥((range ι)ᶜ : Set X), v z = u z) :
    o.boundaryDegree hn hι hιf hf u = 0 := by
  have hu : TopCat.ofHom u =
      (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ :
        TopCat.of ↥((range ι)ᶜ : Set X) ⟶ TopCat.of X) ≫ TopCat.ofHom v := by
    ext z
    exact congrArg _ (hv z).symm
  rw [boundaryDegree_def, hu, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    map_subtypeVal_boundaryClass, map_zero, map_zero, ULift.zero_down]

/-- The constant map `1 : ∂X → S¹` has boundary degree `0`. -/
@[simp]
theorem boundaryDegree_one : o.boundaryDegree hn hι hιf hf 1 = 0 :=
  o.boundaryDegree_eq_zero_of_extend hn hι hιf hf 1 fun _ => rfl

/-- The boundary degree of the pointwise inverse is the negative of the boundary degree. -/
theorem boundaryDegree_inv (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf u⁻¹ = -o.boundaryDegree hn hι hιf hf u := by
  have h := o.boundaryDegree_mul hn hι hιf hf u⁻¹ u
  rw [inv_mul_cancel, boundaryDegree_one] at h
  lia

/-- **The boundary degree along loops.** Suppose that loops `γ i` in `∂X` represent the boundary
class: the sum of their classes in `H₁(∂X; ℤ)`, the push-forwards along `(γ i).toCircle` of the
generator of `Circle.singularHomologyOneIso`, is `∂[X, ∂X]`. Then the boundary degree of `u` is the
sum of the degrees of the loops `u ∘ γ i`. -/
theorem boundaryDegree_eq_sum_degree {κ : Type*} [Fintype κ] {x : κ → ↥((range ι)ᶜ : Set X)}
    (γ : ∀ i, Path (x i) (x i))
    (hγ : ∑ i, (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (γ i).toCircle)).hom
          ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).inv.hom (ULift.up 1)) =
      o.boundaryClass hn hι hιf hf)
    (u : C(↥((range ι)ᶜ : Set X), Circle)) :
    o.boundaryDegree hn hι hιf hf u = ∑ i, Circle.degree ((γ i).map u.continuous) := by
  rw [boundaryDegree_def, ← hγ, map_sum, map_sum]
  rw [Finset.sum_congr rfl fun i _ ↦
    ContinuousMap.singularHomologyOneIso_hom_map_map_inv_one (γ i).toCircle u]
  refine (map_sum (AddEquiv.ulift (α := ℤ)) _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact (u.comp (γ i).toCircle).circleDegree_eq_degree _ fun t ↦ by simp

/-- **The boundary degree through a map to `ℂ`.** Let `G : X → ℂ` have its zeros in `ι(M)`, and
let `u = G / |G|` on `∂X`. Then the boundary degree of `u` is the image of
`G_*[X, ∂X] ∈ H₂(ℂ, ℂ ∖ {0})` under the connecting morphism of `(ℂ, ℂ ∖ {0})`, radial projection
onto `Circle` and `H₁(Circle; ℤ) ≅ ℤ`. -/
theorem boundaryDegree_eq_of_localHomologyMap {G : C(X, ℂ)} (hG : G ⁻¹' {0} ⊆ range ι)
    {u : C(↥((range ι)ᶜ : Set X), Circle)} (hu : ∀ z, (u z : ℂ) = ‖G z‖⁻¹ • G z) :
    o.boundaryDegree hn hι hιf hf u =
      ((Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
        (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
          (TopCat.ofHom Circle.radialProjection)
          ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))).singularHomologyδ
            (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 1 rfl
            (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) G hG 2
              (o.fundamentalClassRel hn hι hιf hf))))).down := by
  set R := ModuleCat.of ℤ (ULift.{0} ℤ)
  set γ := o.fundamentalClassRel hn hι hιf hf
  set P := TopPair.ofSubset ((range ι)ᶜ : Set (TopCat.of X))
  set Q := TopPair.ofSubset ({0}ᶜ : Set (TopCat.of ℂ))
  set H := (singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set H' := reducedSingularHomologyFunctor R 1
  set r := TopCat.ofHom Circle.radialProjection
  -- On `∂X`, the map `G` followed by radial projection onto `Circle` is `u`.
  have hsnd : TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of X) (Y := TopCat.of ℂ)
      (B := (range ι)ᶜ) (B' := {0}ᶜ) (TopCat.ofHom G)
      ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 hG))) ≫ r =
      TopCat.ofHom u := by
    ext z
    -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
    erw [ConcreteCategory.comp_apply]
    refine (Circle.coe_radialProjection_apply _).trans ?_
    erw [TopPair.ofSubsetMap_snd_apply]
    exact (hu z).symm
  -- Naturality of the connecting morphism for `G : (X, ∂X) ⟶ (ℂ, ℂ ∖ {0})`.
  have hnat : P.reducedSingularHomologyδ R 1 ≫ H'.map (TopCat.ofHom u) =
      localHomologyMap R G hG 2 ≫ Q.reducedSingularHomologyδ R 1 ≫ H'.map r := by
    rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
    congr 1
    -- The composite is only type-correct after unfolding the subspace of the pair.
    erw [← Functor.map_comp, hsnd]
  rw [HomologicalOrientation.boundaryDegree_def, HomologicalOrientation.boundaryClass_def]
  refine congrArg (fun y ↦ ((Circle.singularHomologyOneIso R).hom.hom y).down) ?_
  exact calc
    _ = H.map (TopCat.ofHom u) ((reducedSingularHomologyι R 1).app _
          (P.reducedSingularHomologyδ R 1 γ)) :=
        congrArg _
          (ConcreteCategory.congr_hom (TopPair.reducedSingularHomologyδ_comp_ι P R 1) γ).symm
    _ = (reducedSingularHomologyι R 1).app _
          (H'.map (TopCat.ofHom u) (P.reducedSingularHomologyδ R 1 γ)) :=
        (ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality _) _).symm
    _ = (reducedSingularHomologyι R 1).app _
          (H'.map r (Q.reducedSingularHomologyδ R 1 (localHomologyMap R G hG 2 γ))) := by
        have h := ConcreteCategory.congr_hom hnat γ
        simp only [ConcreteCategory.comp_apply] at h
        exact congrArg _ h
    _ = H.map r ((reducedSingularHomologyι R 1).app _
          (Q.reducedSingularHomologyδ R 1 (localHomologyMap R G hG 2 γ))) :=
        ConcreteCategory.congr_hom ((reducedSingularHomologyι R 1).naturality _) _
    _ = _ := congrArg _
        (ConcreteCategory.congr_hom (TopPair.reducedSingularHomologyδ_comp_ι Q R 1) _)

/-- **The boundary degree is read off at the origin of `ℂ`.** Let `G : X → ℂ` have its zeros in
`ι(M)`, and let `u = G / |G|` on `∂X`. If `G` sends the relative fundamental class `[X, ∂X]` to
`c` times the local orientation of `ℂ` at the origin selected by `Complex.orientation`, then the
boundary degree of `u` is `c`. -/
theorem boundaryDegree_eq_of_localHomologyMap_eq_zsmul {G : C(X, ℂ)} (hG : G ⁻¹' {0} ⊆ range ι)
    {u : C(↥((range ι)ᶜ : Set X), Circle)} (hu : ∀ z, (u z : ℂ) = ‖G z‖⁻¹ • G z) {c : ℤ}
    (hc : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) G hG 2
        (o.fundamentalClassRel hn hι hιf hf) =
      c • (Complex.orientation.localOrientation Complex.finrank_real_complex).val) :
    o.boundaryDegree hn hι hιf hf u = c := by
  rw [boundaryDegree_eq_of_localHomologyMap o hn hι hιf hf hG hu, hc, map_zsmul]
  -- `map_zsmul` sees the connecting morphism and the map induced by radial projection as linear
  -- maps only after unfolding how `ConcreteCategory.hom` applies a morphism of `ModuleCat`.
  erw [map_zsmul, map_zsmul,
    SymplecticGeometry.singularHomologyOneIso_singularHomologyδ_localOrientation_complexOrientation]
  simp


section Homeomorph

variable {X' M' : Type} {N' : Type*} [TopologicalSpace X'] [TopologicalSpace N']
  [TopologicalSpace M'] [T2Space X'] [CompactSpace X'] [T2Space M'] [ChartedSpace E M']
  {ι' : M' → X'} {f' : N' → X'}

/-- **Boundary degrees under homeomorphisms.** Let `h : X ≃ₜ X'` and `φ : M ≃ₜ M'` be
homeomorphisms with `h ∘ ι = ι' ∘ φ`, for two instances of the setting of the boundary degree, and
let `g : ∂X → ∂X'` be the restriction of `h`. For an orientation `o'` of `M'` and every
`u : ∂X' → S¹`, the boundary degree of `u ∘ g` for the pull-back `o'.comap φ` is the boundary degree
of `u` for `o'`. -/
theorem boundaryDegree_comp_homeomorph (o' : HomologicalOrientation M' E 2)
    (hι' : IsOpenEmbedding ι') (hιf' : range ι' = (range f')ᶜ) (hf' : IsCollared f')
    (h : X ≃ₜ X') (φ : M ≃ₜ M') (hφ : h ∘ ι = ι' ∘ φ)
    (g : C(↥((range ι)ᶜ : Set X), ↥((range ι')ᶜ : Set X'))) (hg : ∀ z, (g z : X') = h z)
    (u : C(↥((range ι')ᶜ : Set X'), Circle)) :
    (o'.comap φ.isOpenEmbedding).boundaryDegree hn hι hιf hf (u.comp g) =
      o'.boundaryDegree hn hι' hιf' hf' u := by
  rw [boundaryDegree_def, boundaryDegree_def, TopCat.ofHom_comp, Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply,
    map_boundaryClass_comap hn hι hιf hf o' hι' hιf' hf' h φ hφ g hg]

end Homeomorph

end TauCeti.HomologicalOrientation

namespace SymplecticGeometry

open Metric TopologicalSpace

/-- **The sign of the boundary degree.** On the closed unit disc of `ℂ`, with the open disc
oriented as an open subset of `ℂ`, the boundary degree of the identification of the boundary with
`Circle` (`SymplecticGeometry.closedBallComplToCircle`), which runs once counterclockwise, is
`1`. -/
theorem boundaryDegree_closedBallComplToCircle :
    (TauCeti.complexHomologicalOrientation (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).boundaryDegree
      Complex.finrank_real_complex (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
      (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall
      closedBallComplToCircle = 1 := by
  have hG : (⟨Subtype.val, continuous_subtypeVal⟩ : C(closedBall (0 : ℂ) 1, ℂ)) ⁻¹' {0} ⊆
      range (inclusion (ball_subset_closedBall : ball (0 : ℂ) 1 ⊆ closedBall 0 1)) :=
    fun w hw ↦ ⟨⟨0, mem_ball_self one_pos⟩, Subtype.ext hw.symm⟩
  refine (TauCeti.complexHomologicalOrientation
    (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).boundaryDegree_eq_of_localHomologyMap_eq_zsmul
    _ _ _ _ hG (fun w ↦ ?_) ?_
  · -- The boundary circle has norm `1`, where radial projection is the identity.
    have h := Circle.norm_coe (closedBallComplToCircle w)
    rw [coe_closedBallComplToCircle_apply] at h
    simp only [ContinuousMap.coe_mk, h, inv_one, one_smul]
    exact coe_closedBallComplToCircle_apply w
  · rw [localHomologyMap_fundamentalClassRel_closedBall, one_smul]

/-- **The boundary class of the closed unit disc.** Orient the open unit disc as an open subset
of `ℂ` (`TauCeti.complexHomologicalOrientation`). The boundary class of the closed unit disc
relative to the unit circle (`TauCeti.HomologicalOrientation.boundaryClass`), the image of its
relative fundamental class under the connecting morphism, is the class of `H₁(S¹; ℤ)` that, read
in `Circle` and through `Circle.singularHomologyOneIso`, is `1`: the generator of `H₁(Circle)`
that Tau Ceti fixes. -/
theorem singularHomologyOneIso_map_boundaryClass_closedBall :
    (Circle.singularHomologyOneIso (ModuleCat.of ℤ (ULift.{0} ℤ))).hom
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom closedBallComplToCircle)
        ((TauCeti.complexHomologicalOrientation
            (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ)).boundaryClass
          Complex.finrank_real_complex
          (.inclusion _ (isOpen_ball.preimage continuous_subtypeVal))
          (range_inclusion_ball_eq_compl 0 1) isCollared_inclusion_sphere_closedBall)) = 1 := by
  have h := boundaryDegree_closedBallComplToCircle
  rw [TauCeti.HomologicalOrientation.boundaryDegree_def] at h
  exact ULift.ext h

end SymplecticGeometry

end
