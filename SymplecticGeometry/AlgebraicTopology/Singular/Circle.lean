/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import SymplecticGeometry.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Comparison
public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Chart
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.Circle.Degree

/-!
# The generator of the first homology of the circle

Tau Ceti identifies `H₁(Circle; A)` with `A` (`Circle.singularHomologyOneIso`) through the
standard generator of the reduced homology of `TopCat.sphere 1`, which is defined from the
standard basis of the Euclidean model of the plane. This file reads that generator in `ℂ`: it is
the generator of the reduced homology of the unit circle of `ℂ` selected by the standard
orientation `Complex.orientation` (`TauCeti.reducedSingularHomologySphereIsoOfOrientation`),
carried to `Circle` (`Circle.singularHomologyOneIso_inv_eq_complexOrientation`). The
identification of `TopCat.sphere 1` with `Circle` is induced by the linear isometry from the
Euclidean model to `ℂ` that sends the standard basis to `1, I`, which carries the standard
orientation of the model to `Complex.orientation`, and oriented sphere generators are natural
under orientation-preserving linear isometries
(`TauCeti.reducedSingularHomologySphereIsoOfOrientation_hom_naturality`).

So local orientations of `ℂ` (`OpenPartialHomeomorph.localOrientationOfOrientedChart`), which are
read through the same oriented generator, can be compared with `Circle.singularHomologyOneIso`
without any sign.

The file then compares that generator with the class of the counterclockwise loop
`Circle.expLoop`, `t ↦ exp(2πit)`, read as a singular `1`-simplex: the class is **minus** the
generator (`Circle.ιHomology₁_simplex₁_expLoop`). Equivalently, the Hurewicz class of the loop,
which Tau Ceti reads with the opposite sign (`GenLoop.hurewicz_eq_neg_ιHomology₁`), is the
generator (`Circle.hurewicz_genLoopEquivOfUnique_symm_expLoop`). The sign is computed, on the
unit circle `S` of `ℂ`, with the Mayer–Vietoris sequence of the cover of `S` by the complements
of `I` and `-I`, the one behind Tau Ceti's suspension isomorphism
`TauCeti.reducedSingularHomologySphereSuccIso` at the last vector `I` of the basis `1, I`. The
singular `2`-simplex `w ↦ exp(πi(w₁ + 2w₂))` has as faces the lower half-circle from `-1` to `1`,
the loop, and the upper half-circle from `1` to `-1`, so the loop is homologous to the sum of the
two half-circles, which lie in the two sets of the cover. The chain-level description of the
connecting morphism (`SSet.homologyπ_mayerVietorisδ_of_chain_lifts`) then sends the class of
the loop to `[1] - [-1]`. Radial projection to the equator carries this to `[b] - [-b]`, for `b`
the remaining basis vector `1`, while Tau Ceti's generator of the equator is `[-b] - [b]`
(`TauCeti.reducedSingularHomologySphereIso_inv_ι`).

## Main results

* `Circle.singularHomologyOneIso_inv_eq_complexOrientation`: the inverse of
  `Circle.singularHomologyOneIso` is the generator of the unit circle of `ℂ` selected by
  `Complex.orientation`.
* `Circle.ιHomology₁_simplex₁_expLoop`: the class of the singular `1`-simplex traced by
  `Circle.expLoop` is `-(Circle.singularHomologyOneIso A).inv`.
* `Circle.hurewicz_genLoopEquivOfUnique_symm_expLoop`: the Hurewicz class of `Circle.expLoop`
  is `(Circle.singularHomologyOneIso A).inv`.
* `SSet.ιHomology₁_homologyMap`: a map of simplicial sets carries the class of a closed
  `1`-simplex to the class of its image. Its proof follows Tau Ceti's
  `SSetPair.relClass₁_homologyMap`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (local
  orientations and the generators of the homology of spheres), and Section 2.2 (the
  Mayer–Vietoris sequence and its connecting morphism, Example 2.46 for spheres) and Section 2.A
  (`H₁` and loops).
-/

public section

noncomputable section

open CategoryTheory Limits Metric TauCeti AlgebraicTopology

namespace SSet

open Simplicial

universe w v' u'

variable {C' : Type u'} [Category.{v'} C'] [HasCoproducts.{w} C'] [Preadditive C']
  [CategoryWithHomology C'] (R : C')

/-- **Naturality of the class of a closed `1`-simplex**: a map of simplicial sets carries the class
of a `1`-simplex with equal faces to the class of its image. -/
@[reassoc (attr := simp)]
lemma ιHomology₁_homologyMap {X Y : SSet.{w}} (f : X ⟶ Y) (s : X _⦋1⦌) (h : X.δ 0 s = X.δ 1 s) :
    ιHomology₁ R X s h ≫ SSet.homologyMap f R 1 =
      ιHomology₁ R Y (f.app _ s) (by rw [← δ_naturality_apply, h, δ_naturality_apply]) := by
  rw [ιHomology₁_def, ιHomology₁_def, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2
  exact ι_chainComplexMap_f _ _ _ _ s

end SSet

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
theorem singularHomologyOneIso_inv_eq_complexOrientation :
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


/-! ### The class of the counterclockwise loop -/

section Loop

open Convexity Real Simplicial TopCat
open scoped unitInterval

/-- The unit circle of `ℂ`, as a topological space. -/
private abbrev Sph : TopCat := TopCat.of (sphere (0 : ℂ) 1)

/-- The point `exp(πiθ)` of the unit circle of `ℂ`. -/
private def halfTurn (θ : ℝ) : sphere (0 : ℂ) 1 := homeomorphSphere (Circle.exp (π * θ))

private lemma continuous_halfTurn : Continuous halfTurn :=
  homeomorphSphere.continuous.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))

private lemma coe_halfTurn (θ : ℝ) :
    (halfTurn θ : ℂ) = Complex.exp ((π * θ : ℝ) * Complex.I) := by
  simp [halfTurn, Circle.coe_exp]

private lemma im_halfTurn (θ : ℝ) : (halfTurn θ : ℂ).im = Real.sin (π * θ) := by
  rw [coe_halfTurn, Complex.exp_ofReal_mul_I_im]

private lemma halfTurn_zero : halfTurn 0 = ⟨1, by simp⟩ := Subtype.ext (by simp [coe_halfTurn])

private lemma halfTurn_one : halfTurn 1 = -halfTurn 0 :=
  Subtype.ext (by simp [coe_halfTurn, coe_neg_sphere, Complex.exp_pi_mul_I])

private lemma halfTurn_two : halfTurn 2 = halfTurn 0 :=
  Subtype.ext (by simp [coe_halfTurn, show (π * 2 : ℂ) * Complex.I = 2 * π * Complex.I by ring])

/-- The arc `t ↦ exp(πi(a + bt))` of the unit circle of `ℂ`. -/
private def arc (a b : ℝ) : C(I, sphere (0 : ℂ) 1) :=
  ⟨fun t ↦ halfTurn (a + b * t), continuous_halfTurn.comp (by fun_prop)⟩

private lemma arc_apply (a b : ℝ) (t : I) : arc a b t = halfTurn (a + b * t) := rfl

/-- The singular `2`-simplex `w ↦ exp(πi(w₁ + 2w₂))` of the unit circle of `ℂ`. Its faces are
the upper half-circle `δ₂`, the lower half-circle `δ₀` and the full counterclockwise loop `δ₁`. -/
private def tri : (toSSet.obj Sph) _⦋2⦌ :=
  (Sph.toSSetObjEquiv _).symm
    ⟨fun w ↦ halfTurn (w.weights 1 + 2 * w.weights 2), continuous_halfTurn.comp (by fun_prop)⟩

/-- A face of `tri` is the arc whose parameter is read off the face's barycentric coordinates. -/
private lemma δ_tri (i : Fin 3) (a b : ℝ)
    (h : ∀ w : StdSimplex ℝ (Fin 2),
      (w.weights.mapDomain i.succAbove) 1 + 2 * (w.weights.mapDomain i.succAbove) 2 =
        a + b * w.weights 1) :
    (toSSet.obj Sph).δ i tri = simplex₁ (arc a b) := by
  apply (Sph.toSSetObjEquiv _).injective
  ext w
  rw [toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplex₁]
  simpa [tri, arc, StdSimplex.homeomorphI_apply_coe] using
    congrArg (fun θ ↦ (halfTurn θ : ℂ)) (h w)

private lemma δ_zero_tri : (toSSet.obj Sph).δ 0 tri = simplex₁ (arc 1 1) := by
  refine δ_tri 0 1 1 fun w ↦ ?_
  rw [show (1 : Fin 3) = Fin.succAbove 0 0 from rfl, show (2 : Fin 3) = Fin.succAbove 0 1 from rfl,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
  linarith [w.total_fin_two]

private lemma δ_one_tri : (toSSet.obj Sph).δ 1 tri = simplex₁ (arc 0 2) := by
  refine δ_tri 1 0 2 fun w ↦ ?_
  rw [Finsupp.mapDomain_of_notMem_range _ (1 : Fin 3) (by simp),
    show (2 : Fin 3) = Fin.succAbove 1 1 from rfl,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]

private lemma δ_two_tri : (toSSet.obj Sph).δ 2 tri = simplex₁ (arc 0 1) := by
  refine δ_tri 2 0 1 fun w ↦ ?_
  rw [Finsupp.mapDomain_of_notMem_range _ (2 : Fin 3) (by simp),
    show (1 : Fin 3) = Fin.succAbove 2 1 from rfl,
    Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective]
  ring

/-- The loop `t ↦ exp(2πit)` of the unit circle of `ℂ` is a closed singular `1`-simplex. -/
private lemma δ_zero_simplex₁_arc_eq_δ_one :
    (toSSet.obj Sph).δ 0 (simplex₁ (arc 0 2)) = (toSSet.obj Sph).δ 1 (simplex₁ (arc 0 2)) := by
  rw [δ_zero_simplex₁, δ_one_simplex₁]
  simp [arc_apply, halfTurn_two]

/-! The Mayer–Vietoris sequence of the cover of the unit circle of `ℂ` by the complements of a
point `p` at `I` and of `-p`: the lower half-circle lies in the first set, the upper one in the
second, and both run between the points `1` and `-1` of the intersection. -/

variable (p : sphere (0 : ℂ) 1) (hp : (p : ℂ) = Complex.I)

include hp in
private lemma arc_one_one_mem (t : I) : arc 1 1 t ∈ ({p}ᶜ : Set (sphere (0 : ℂ) 1)) := by
  intro h
  have h' := congrArg (fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im) (Set.mem_singleton_iff.mp h)
  simp only [arc_apply, im_halfTurn, hp, Complex.I_im] at h'
  have : 0 ≤ Real.sin (π * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by have := unitInterval.nonneg t; positivity)
      (by nlinarith [unitInterval.le_one t, Real.pi_pos])
  rw [show π * (1 + 1 * (t : ℝ)) = π * t + π by ring, Real.sin_add_pi] at h'
  linarith

include hp in
private lemma arc_zero_one_mem (t : I) : arc 0 1 t ∈ ({-p}ᶜ : Set (sphere (0 : ℂ) 1)) := by
  intro h
  have h' := congrArg (fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im) (Set.mem_singleton_iff.mp h)
  simp only [arc_apply, im_halfTurn, hp, Complex.I_im, coe_neg_sphere, Complex.neg_im] at h'
  have : 0 ≤ Real.sin (π * t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by have := unitInterval.nonneg t; positivity)
      (by nlinarith [unitInterval.le_one t, Real.pi_pos])
  rw [zero_add, one_mul] at h'
  linarith

include hp in
private lemma halfTurn_zero_mem : halfTurn 0 ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : ℂ) 1)) := by
  constructor <;> intro h <;>
  · have h' := congrArg (fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ).im) (Set.mem_singleton_iff.mp h)
    simp [halfTurn_zero, hp, coe_neg_sphere] at h'

/-- The lower half-circle, a singular `1`-simplex of the complement of `p`. -/
private def lowerArc : (toSSet.obj (of ↥({p}ᶜ : Set (sphere (0 : ℂ) 1)))) _⦋1⦌ :=
  simplex₁ ⟨Set.codRestrict (arc 1 1) _ (arc_one_one_mem p hp), (arc 1 1).continuous.codRestrict _⟩

/-- The upper half-circle, a singular `1`-simplex of the complement of `-p`. -/
private def upperArc : (toSSet.obj (of ↥({-p}ᶜ : Set (sphere (0 : ℂ) 1)))) _⦋1⦌ :=
  simplex₁ ⟨Set.codRestrict (arc 0 1) _ (arc_zero_one_mem p hp), (arc 0 1).continuous.codRestrict _⟩

/-- The point `1` of `S ∖ {p, -p}`. -/
private abbrev pointOne : ↥({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : ℂ) 1)) :=
  ⟨halfTurn 0, halfTurn_zero_mem p hp⟩

/-- The point `-1` of `S ∖ {p, -p}`. -/
private abbrev pointNegOne : ↥({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : ℂ) 1)) :=
  ⟨-halfTurn 0, neg_mem_compl_singleton_inter_compl_singleton_neg (halfTurn_zero_mem p hp)⟩

/-- The cycle `[1] - [-1]` of `S ∖ {p, -p}`. -/
private def vertexCycle :
    A ⟶ ((toSSet.obj (of ↥({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : ℂ) 1)))).chainComplex A).cycles 0 :=
  HomologicalComplex.liftCycles _
    ((toSSet.obj _).ιChainComplex (toSSetObj₀Equiv.symm (pointOne p hp)) -
      (toSSet.obj _).ιChainComplex (toSSetObj₀Equiv.symm (pointNegOne p hp))) 0 (by simp) (by simp)

/-- The class of `vertexCycle` is `[1] - [-1]`. -/
private lemma vertexCycle_homologyπ :
    vertexCycle A p hp ≫ HomologicalComplex.homologyπ _ 0 =
      singularHomology₀Section A (pointOne p hp) -
        singularHomology₀Section A (pointNegOne p hp) := by
  rw [singularHomology₀Section_def, singularHomology₀Section_def, SSet.ιHomology₀_def,
    SSet.ιHomology₀_def]
  have : vertexCycle A p hp =
      HomologicalComplex.liftCycles _ ((toSSet.obj _).ιChainComplex
          (toSSetObj₀Equiv.symm (pointOne p hp))) 0 (by simp) (by simp) -
        HomologicalComplex.liftCycles _ ((toSSet.obj _).ιChainComplex
          (toSSetObj₀Equiv.symm (pointNegOne p hp))) 0 (by simp) (by simp) := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
    simp [vertexCycle]
  rw [this, Preadditive.sub_comp]
  -- The two sides differ only in how degree-zero singular homology is written: through
  -- `singularHomologyFunctor` or as the homology of the singular simplicial set.
  rfl

/-- The boundary of the lower half-circle is `[1] - [-1]`. -/
private lemma lowerArc_d :
    (toSSet.obj _).ιChainComplex (lowerArc p hp) ≫ ((toSSet.obj _).chainComplex A).d 1 0 =
      vertexCycle A p hp ≫ HomologicalComplex.iCycles _ 0 ≫ (SSet.chainComplexMap (toSSet.map
        (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := {-p}ᶜ))))) A).f 0 := by
  have e₁ : Set.codRestrict (arc 1 1) _ (arc_one_one_mem p hp) 1 =
      Set.inclusion Set.inter_subset_left (pointOne p hp) :=
    Subtype.ext (by norm_num [arc_apply, halfTurn_two])
  have e₀ : Set.codRestrict (arc 1 1) _ (arc_one_one_mem p hp) 0 =
      Set.inclusion Set.inter_subset_left (pointNegOne p hp) :=
    Subtype.ext (by norm_num [arc_apply, halfTurn_one])
  simp only [vertexCycle, HomologicalComplex.liftCycles_i_assoc, SSet.ιChainComplex_d,
    Preadditive.sub_comp, SSet.ι_chainComplexMap_f]
  rw [Fin.sum_univ_two]
  simp only [lowerArc, Int.reduceNeg, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul, δ_zero_simplex₁,
    δ_one_simplex₁, ContinuousMap.coe_mk]
  rw [e₁, e₀, sub_eq_add_neg]
  -- The vertices on the right are images of vertices, which are the vertices of the images by
  -- `toSSet_map_app_toSSetObj₀Equiv_symm`, a definitional equality.
  rfl

/-- The boundary of minus the upper half-circle is `[1] - [-1]`. -/
private lemma upperArc_d :
    (-(toSSet.obj _).ιChainComplex (upperArc p hp)) ≫ ((toSSet.obj _).chainComplex A).d 1 0 =
      vertexCycle A p hp ≫ HomologicalComplex.iCycles _ 0 ≫ (SSet.chainComplexMap (toSSet.map
        (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := {p}ᶜ))))) A).f 0 := by
  have e₁ : Set.codRestrict (arc 0 1) _ (arc_zero_one_mem p hp) 1 =
      Set.inclusion Set.inter_subset_right (pointNegOne p hp) :=
    Subtype.ext (by norm_num [arc_apply, halfTurn_one])
  have e₀ : Set.codRestrict (arc 0 1) _ (arc_zero_one_mem p hp) 0 =
      Set.inclusion Set.inter_subset_right (pointOne p hp) :=
    Subtype.ext (by norm_num [arc_apply])
  simp only [vertexCycle, HomologicalComplex.liftCycles_i_assoc, SSet.ιChainComplex_d,
    Preadditive.sub_comp, SSet.ι_chainComplexMap_f, Preadditive.neg_comp]
  rw [Fin.sum_univ_two]
  simp only [upperArc, Int.reduceNeg, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, one_smul, Nat.mod_succ, pow_one, neg_smul, neg_add_rev, neg_neg,
    δ_zero_simplex₁, δ_one_simplex₁, ContinuousMap.coe_mk]
  rw [e₁, e₀, sub_eq_add_neg]
  -- As in `lowerArc_d`, by `toSSet_map_app_toSSetObj₀Equiv_symm`.
  rfl

/-- A cycle of the simplices small for the cover, given by the two half-circles, has the class of
the full loop. -/
private lemma ιHomology₁_arc_eq
    (z : A ⟶ ((Sph.smallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]).toSSet.chainComplex
      A).cycles 1)
    (hz : (toSSet.obj _).ιChainComplex (lowerArc p hp) ≫ (SSet.chainComplexMap
          (toSmallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]
            (Matrix.cons_val_zero _ _).superset) A).f 1 -
        (-(toSSet.obj _).ιChainComplex (upperArc p hp)) ≫ (SSet.chainComplexMap
          (toSmallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]
            ((Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)).superset) A).f 1 =
      z ≫ HomologicalComplex.iCycles _ 1) :
    SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2)) δ_zero_simplex₁_arc_eq_δ_one =
      z ≫ HomologicalComplex.homologyπ _ 1 ≫
        SSet.homologyMap (Sph.smallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]).ι A 1 := by
  have hl : (Sph.smallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]).ι.app _
      ((toSmallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]
        (Matrix.cons_val_zero _ _).superset).app _
        (lowerArc p hp)) = (toSSet.obj Sph).δ 0 tri := by
    rw [← NatTrans.comp_app_apply, toSmallSingularSubcomplex_ι, δ_zero_tri]
    -- The inclusion of the complement composed with the corestricted arc is the arc itself.
    exact toSSet_map_app_simplex₁ _ _
  have hu : (Sph.smallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]).ι.app _
      ((toSmallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]
        ((Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)).superset).app _
        (upperArc p hp)) = (toSSet.obj Sph).δ 2 tri := by
    rw [← NatTrans.comp_app_apply, toSmallSingularSubcomplex_ι, δ_two_tri]
    -- As for the lower half-circle.
    exact toSSet_map_app_simplex₁ _ _
  rw [SSet.ιHomology₁_def, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    ← sub_eq_zero, ← Preadditive.sub_comp]
  -- The loop differs from the sum of the two half-circles by the boundary of `-tri`.
  have hb : HomologicalComplex.liftCycles _
        ((toSSet.obj Sph).ιChainComplex (simplex₁ (arc 0 2))) 0 (by simp)
        (by rw [SSet.ιChainComplex_d, Fin.sum_univ_two, δ_zero_simplex₁_arc_eq_δ_one]; simp) -
      z ≫ HomologicalComplex.cyclesMap (SSet.chainComplexMap
        (Sph.smallSingularSubcomplex ![({p}ᶜ : Set Sph), {-p}ᶜ]).ι A) 1 =
      HomologicalComplex.liftCycles _
        ((-(toSSet.obj Sph).ιChainComplex tri) ≫ ((toSSet.obj Sph).chainComplex A).d 2 1) 0
        (by simp) (by rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]) := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 1)]
    simp only [Preadditive.sub_comp, HomologicalComplex.liftCycles_i, Category.assoc,
      HomologicalComplex.cyclesMap_i]
    rw [← reassoc_of% hz]
    simp only [Preadditive.sub_comp, Preadditive.neg_comp,
      SSet.ι_chainComplexMap_f, SSet.ιChainComplex_d, hl, hu, ← δ_one_tri]
    rw [Fin.sum_univ_three]
    simp
    abel
  rw [hb]
  exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _ rfl

/-- The Mayer–Vietoris connecting morphism of the cover by the complements of `p` and `-p` sends
the class of the loop `t ↦ exp(2πit)` to `[1] - [-1]`. -/
private lemma ιHomology₁_arc_mayerVietorisδ :
    SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2)) δ_zero_simplex₁_arc_eq_δ_one ≫
        TopCat.mayerVietorisδ A (X := Sph) isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg one_ne_zero p) 1 0 =
      singularHomology₀Section A (pointOne p hp) -
        singularHomology₀Section A (pointNegOne p hp) := by
  have sq := isPushout_toSSet_inter_smallSingularSubcomplex (X := Sph)
    ({p}ᶜ : Set (sphere (0 : ℂ) 1)) {-p}ᶜ
  obtain ⟨z, hz⟩ := SSet.exists_cycle_of_chain_lifts A sq.toCommSq 0
    (vertexCycle A p hp ≫ HomologicalComplex.iCycles _ 0) _ _
    ((lowerArc_d A p hp).trans (Category.assoc _ _ _).symm)
    ((upperArc_d A p hp).trans (Category.assoc _ _ _).symm)
  rw [ιHomology₁_arc_eq A p hp z hz, Category.assoc, Category.assoc,
    TopCat.homologyMap_ι_comp_mayerVietorisδ A _ _ _ 1 0]
  exact (SSet.homologyπ_mayerVietorisδ_of_chain_lifts A sq 0 z _ _ _ hz (lowerArc_d A p hp)
    (upperArc_d A p hp)).trans (vertexCycle_homologyπ A p hp)

omit hp

/-- The point `I` of the unit circle of `ℂ`: the last vector of the basis `1, I`, and so the pole
at which `TauCeti.reducedSingularHomologySphereIso` takes its suspension isomorphism. -/
private abbrev pole : sphere (0 : ℂ) 1 := ⟨Complex.orthonormalBasisOneI (Fin.last 1), by simp⟩

private lemma coe_pole : (pole : ℂ) = Complex.I := by
  simp [Fin.last]

/-- The radial projection to the equator sends `1` to the remaining basis vector. -/
private lemma equatorHomotopyEquiv_pointOne :
    (equatorHomotopyEquiv pole).toFun (pointOne pole coe_pole) =
      ⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_equatorHomotopyEquiv_apply, OrthonormalBasis.coe_orthogonalLast_apply]
  simp [halfTurn_zero, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, NormedSpace.normalize]

/-- The radial projection to the equator sends `-1` to minus the remaining basis vector. -/
private lemma equatorHomotopyEquiv_pointNegOne :
    (equatorHomotopyEquiv pole).toFun (pointNegOne pole coe_pole) =
      -⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_equatorHomotopyEquiv_apply, coe_neg_sphere, coe_neg_sphere, Submodule.coe_neg,
    OrthonormalBasis.coe_orthogonalLast_apply]
  simp [halfTurn_zero, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, NormedSpace.normalize]

/-- The class of the loop, carried through the suspension isomorphism at `I` and read in the
homology of the equator, is `[b] - [-b]` for the remaining basis vector `b`. -/
private lemma ιHomology₁_arc_comp_suspension :
    SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2)) δ_zero_simplex₁_arc_eq_δ_one ≫
        ((reducedSingularHomologySuccIso A 0).app Sph).inv ≫
        (reducedSingularHomologySphereSuccIso A pole 0).hom ≫
        (reducedSingularHomologyι A 0).app (of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1)) =
      singularHomology₀Section A (X := of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1))
          ⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩ -
        singularHomology₀Section A (X := of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1))
          (-⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩) := by
  rw [reducedSingularHomologySphereSuccIso_hom, ← reducedSingularHomologySuccIso_hom, ← Iso.app_hom]
  simp only [Category.assoc]
  -- The inverse and the inclusion of reduced homology meet across the two forms of `H₁`, hence
  -- `erw`.
  erw [Iso.inv_hom_id_assoc]
  -- From here the goal mixes `singularHomologyFunctor` homology with `toSSet` homology, which
  -- agree only after unfolding, so `rw` fails and the steps are composed as terms.
  refine (congrArg (fun t ↦ SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2))
    δ_zero_simplex₁_arc_eq_δ_one ≫ t) ((Category.assoc _ _ _).trans
      (congrArg (fun t ↦ TopCat.reducedMayerVietorisδ A (X := Sph) isOpen_compl_singleton
        isOpen_compl_singleton (compl_singleton_union_compl_singleton_neg one_ne_zero pole) 0 ≫
          t) ((reducedSingularHomologyι A 0).naturality
            (ofHom (equatorHomotopyEquiv pole).toFun))))).trans ?_
  refine (congrArg (fun t ↦ SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2))
    δ_zero_simplex₁_arc_eq_δ_one ≫ t)
      (TopCat.reducedMayerVietorisδ_comp_ι_assoc A _ _ _ 0 _)).trans ?_
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (ιHomology₁_arc_mayerVietorisδ A pole coe_pole))).trans ?_
  refine (Preadditive.sub_comp _ _ _).trans ?_
  exact congrArg₂ (· - ·)
    ((singularHomology₀Section_naturality A _ _).trans
      (congrArg _ equatorHomotopyEquiv_pointOne))
    ((singularHomology₀Section_naturality A _ _).trans
      (congrArg _ equatorHomotopyEquiv_pointNegOne))

/-- On the unit circle of `ℂ`, the class of the loop `t ↦ exp(2πit)` is minus the generator
selected by `Complex.orientation`. -/
private lemma ιHomology₁_arc :
    SSet.ιHomology₁ A (toSSet.obj Sph) (simplex₁ (arc 0 2)) δ_zero_simplex₁_arc_eq_δ_one =
      -((reducedSingularHomologySphereIsoOfOrientation A Complex.orientation
          Complex.finrank_real_complex).inv ≫ (reducedSingularHomologyι A 1).app Sph) := by
  have hb : Complex.orthonormalBasisOneI.toBasis.orientation = Complex.orientation := by
    rw [Complex.toBasis_orthonormalBasisOneI]
    -- `Complex.orientation` is by definition the orientation of `Complex.basisOneI`.
    rfl
  rw [reducedSingularHomologySphereIsoOfOrientation_eq A _ _ Complex.orthonormalBasisOneI hb,
    reducedSingularHomologySphereIso_succ]
  let Φ := (reducedSingularHomologySuccIso A 0).app Sph
  have hΦ : Φ.hom = (reducedSingularHomologyι A 1).app Sph := by
    simp [Φ, reducedSingularHomologySuccIso_hom]
  -- Both sides are compared after the suspension isomorphism followed by the inclusion of the
  -- reduced homology of the equator in its homology, a monomorphism.
  refine (cancel_mono (Φ.inv ≫ (reducedSingularHomologySphereSuccIso A pole 0).hom ≫
    (reducedSingularHomologyι A 0).app (of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1)))).1 ?_
  have hR : (reducedSingularHomologySphereSuccIso A pole 0 ≪≫
        reducedSingularHomologySphereIso A Complex.orthonormalBasisOneI.orthogonalLast).inv ≫
        (reducedSingularHomologyι A 1).app Sph ≫ Φ.inv ≫
        (reducedSingularHomologySphereSuccIso A pole 0).hom ≫
        (reducedSingularHomologyι A 0).app (of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1)) =
      singularHomology₀Section A (X := of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1))
          (-⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩) -
        singularHomology₀Section A (X := of (sphere (0 : (ℝ ∙ (pole : ℂ))ᗮ) 1))
          ⟨Complex.orthonormalBasisOneI.orthogonalLast 0, by simp⟩ := by
    rw [← hΦ, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    exact reducedSingularHomologySphereIso_inv_ι A _
  exact (ιHomology₁_arc_comp_suspension A).trans
    (((neg_sub _ _).symm.trans (congrArg Neg.neg hR.symm)).trans
      (by rw [Preadditive.neg_comp, Category.assoc]))

end Loop

/-- The counterclockwise loop `Circle.expLoop`, read as a singular `1`-simplex, is closed. -/
theorem δ_zero_simplex₁_expLoop_eq_δ_one :
    (TopCat.toSSet.obj (TopCat.of Circle)).δ 0 (TopCat.simplex₁ expLoop.toContinuousMap) =
      (TopCat.toSSet.obj (TopCat.of Circle)).δ 1 (TopCat.simplex₁ expLoop.toContinuousMap) := by
  rw [TopCat.δ_zero_simplex₁, TopCat.δ_one_simplex₁]
  simp

/-- **The class of the counterclockwise loop is minus the generator of `H₁(Circle)`.** The
homology class of the singular `1`-simplex traced by the loop `t ↦ exp(2πit)` is
`-(Circle.singularHomologyOneIso A).inv`: the sign `ε` in `[expLoop] = ε • generator` is `-1`. -/
theorem ιHomology₁_simplex₁_expLoop :
    SSet.ιHomology₁ A (TopCat.toSSet.obj (TopCat.of Circle))
        (TopCat.simplex₁ expLoop.toContinuousMap) δ_zero_simplex₁_expLoop_eq_δ_one =
      -(singularHomologyOneIso A).inv := by
  rw [singularHomologyOneIso_inv_eq_complexOrientation, ← Category.assoc, ← Preadditive.neg_comp,
    ← ιHomology₁_arc]
  have hs : (TopCat.toSSet.map (TopCat.ofHom
      (homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)))).app _
        (TopCat.simplex₁ (arc 0 2)) = TopCat.simplex₁ expLoop.toContinuousMap := by
    rw [TopCat.toSSet_map_app_simplex₁]
    congr 1
    ext t
    simp only [arc_apply, halfTurn, ContinuousMap.comp_apply, TopCat.hom_ofHom,
      ContinuousMap.coe_ofClass, Homeomorph.symm_apply_apply, Path.coe_toContinuousMap,
      expLoop_apply]
    ring_nf
  refine Eq.trans ?_ (SSet.ιHomology₁_homologyMap A _ _ δ_zero_simplex₁_arc_eq_δ_one).symm
  congr 1
  exact hs.symm

open Simplicial in
/-- **The Hurewicz class of the counterclockwise loop is the generator of `H₁(Circle)`**:
`GenLoop.hurewicz` reads a loop with the opposite sign to its singular `1`-simplex
(`GenLoop.hurewicz_eq_neg_ιHomology₁`). -/
theorem hurewicz_genLoopEquivOfUnique_symm_expLoop :
    GenLoop.hurewicz A ((genLoopEquivOfUnique (Fin 1)).symm expLoop) =
      (singularHomologyOneIso A).inv := by
  have hs : GenLoop.simplex₁ ((genLoopEquivOfUnique (Fin 1)).symm expLoop) =
      TopCat.simplex₁ expLoop.toContinuousMap := by
    rw [GenLoop.simplex₁_eq_topCatSimplex₁, Equiv.apply_symm_apply]
  have he : ∀ (s : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌)
      (_ : s = TopCat.simplex₁ expLoop.toContinuousMap) h,
      SSet.ιHomology₁ A _ s h = SSet.ιHomology₁ A _ _ δ_zero_simplex₁_expLoop_eq_δ_one := by
    rintro _ rfl _
    rfl
  rw [GenLoop.hurewicz_eq_neg_ιHomology₁]
  refine (congrArg Neg.neg
    (?_ : _ = SSet.ιHomology₁ A _ _ δ_zero_simplex₁_expLoop_eq_δ_one)).trans ?_
  · exact he _ hs _
  · rw [ιHomology₁_simplex₁_expLoop]
    exact neg_neg _

end Circle
