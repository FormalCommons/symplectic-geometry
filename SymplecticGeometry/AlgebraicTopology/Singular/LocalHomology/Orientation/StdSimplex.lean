/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.AlgebraicTopology.Singular.Circle
public import SymplecticGeometry.AlgebraicTopology.Singular.RelativeClass
public import SymplecticGeometry.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import SymplecticGeometry.LinearAlgebra.Complex.Orientation
public import TauCeti.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Geometry.Convex.FullSimplex
public import TauCeti.Geometry.Manifold.Orientation.Euclidean

/-!
# The local class of the standard 2-simplex in the plane

Let `p` be a point of the interior of Tau Ceti's full-dimensional standard simplex
`fullSimplex 2 ⊆ ℝ²`, with vertices `0`, `e₀`, `e₁`. Read through
`TauCeti.fullSimplexEquivStdSimplex`, its inclusion is a singular `2`-simplex `σ` of `ℝ²` whose
faces avoid `p` (`TopPair.range_toSSetObjEquiv_δ_fullSimplex_subset`), so it has a class
`[σ] ∈ H₂(ℝ², ℝ² ∖ {p}; ℤ)` (`TopPair.relClass`). This file computes it: `[σ]` is **minus** the
local orientation at `p` selected by the identity chart and the standard orientation of `ℝ²`
(`TopPair.relClass_fullSimplex_eq_neg_localOrientationOfOrientedChart`), which is the local
orientation of the homological orientation of the smooth standard orientation
(`TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`). So the sign `s` with
`[positively oriented simplex] = s • (Tau Ceti's local orientation)` is `s = -1`.

## Proof

The oriented local homology isomorphism of the identity chart at `p`, which sends the local
orientation to `1`, is the connecting morphism of `(ℝ², ℝ² ∖ {p})`, followed by radial projection
about `p` and the generator of the unit circle selected by the orientation. Through the linear
isometry `(x, y) ↦ x + iy` of `ℝ²` with `ℂ`, which preserves orientations, and
`Circle.singularHomologyOneIso_inv_eq_complexOrientation`, it is the connecting morphism followed by
the direction map `ℝ² ∖ {p} → Circle` and `Circle.singularHomologyOneIso`.

The connecting morphism sends `[σ]` to the class of the edge cycle `t₀ - t₁ + t₂`
(`TopPair.relClass_singularHomologyδ_two`), whose edges are the segments from `e₀` to `e₁`, from
`0` to `e₁` and from `0` to `e₀`. Seen from `p` as complex numbers `A`, `B`, `C`, the directions
along these segments have explicit continuous lifts to `ℝ`, through `Complex.arg` of a point of the
segment from `1` to `B / A` (and to `C / B`, `C / A`), which stays in the slit plane since `p` is
not on the edge. The lifts of `t₂` and `t₀` turn by the angles `arg (B / A)` and `arg (C / B)` in
`(0, π)`, that of `t₁` by `arg (C / A)` in `(-π, 0)`, and these add up to a full turn. So the lifts
close up after one turn, and `Circle.liftCycles_simplex₁_exp_comp_homologyπ` identifies the class of
the image of the edge cycle in `Circle` with that of the counterclockwise loop, which is minus the
generator (`Circle.ιHomology₁_simplex₁_expLoop`).

## Main results

* `TopPair.range_toSSetObjEquiv_δ_fullSimplex_subset`: the faces of the standard simplex avoid its
  interior.
* `TopPair.relClass_fullSimplex_eq_neg_localOrientationOfOrientedChart`: the class of the standard
  simplex is minus the local orientation of the identity chart.
* `TopPair.relClass_fullSimplex_eq_neg_toHomologicalOrientation`: the same for the homological
  orientation of `TauCeti.Manifold.Orientation.euclideanSpace 2`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1 (the class of a
  simplex and the long exact sequence of a pair) and Section 3.3 (local orientations).
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti AlgebraicTopology Module Metric Real Simplicial
open scoped unitInterval

namespace TopPair

/-! ### Lifts of the direction of a segment -/

/-- For `ζ` off the real axis, the points `1 + t (ζ - 1)`, `t ∈ [0, 1]`, of the segment from `1`
to `ζ` lie in the slit plane. -/
private lemma one_add_mul_sub_one_mem_slitPlane {ζ : ℂ} (hζ : ζ.im ≠ 0) (t : I) :
    1 + (t : ℝ) * (ζ - 1) ∈ Complex.slitPlane := by
  rcases eq_or_ne (t : ℝ) 0 with ht | ht
  · simp [ht]
  · refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    simpa using mul_ne_zero ht hζ

/-- The continuous lift `t ↦ c + arg (1 + t (ζ - 1))` of the direction of the segment from `1` to
`ζ`, turned by the angle `c`. -/
private def segmentLift (c : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) : C(I, ℝ) where
  toFun t := c + Complex.arg (1 + (t : ℝ) * (ζ - 1))
  continuous_toFun := continuous_const.add <| continuous_iff_continuousAt.2 fun t ↦
    ContinuousAt.comp (g := Complex.arg) (f := fun t : I ↦ 1 + ((t : ℝ) : ℂ) * (ζ - 1))
      (Complex.continuousAt_arg (one_add_mul_sub_one_mem_slitPlane hζ t)) (by fun_prop)

private lemma segmentLift_apply (c : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (t : I) :
    segmentLift c ζ hζ t = c + Complex.arg (1 + (t : ℝ) * (ζ - 1)) :=
  rfl

private lemma segmentLift_zero (c : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) : segmentLift c ζ hζ 0 = c := by
  simp [segmentLift_apply]

private lemma segmentLift_one (c : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    segmentLift c ζ hζ 1 = c + Complex.arg ζ := by
  simp [segmentLift_apply]

/-- If `exp (ic)` is the direction of `A`, then `segmentLift c (B / A)` lifts the direction of the
segment from `A` to `B`. -/
private lemma coe_exp_segmentLift {A B : ℂ} (hA : A ≠ 0) (hζ : (B / A).im ≠ 0) {c : ℝ}
    (hc : (Circle.exp c : ℂ) = A / ‖A‖) (t : I) :
    (Circle.exp (segmentLift c (B / A) hζ t) : ℂ) =
      (A + (t : ℝ) * (B - A)) / ‖A + (t : ℝ) * (B - A)‖ := by
  have hw := Complex.slitPlane_ne_zero (one_add_mul_sub_one_mem_slitPlane hζ t)
  have hAw : A + (t : ℝ) * (B - A) = A * (1 + (t : ℝ) * (B / A - 1)) := by
    field_simp
  rw [segmentLift_apply, Circle.exp_add, Circle.coe_mul, hc, Circle.coe_exp,
    Complex.exp_arg_mul_I hw, hAw, norm_mul, Complex.ofReal_mul]
  field_simp

/-! ### The local homology of the plane read in `Circle` -/

/-- The integer coefficients of Tau Ceti's local homology. -/
private abbrev R : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ULift.{0} ℤ)

/-- The identification `(x, y) ↦ x + iy` of `ℝ²` with `ℂ`, as a linear isometry. -/
private abbrev toComplex : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The direction about `p` of a point of `ℝ² ∖ {p}`, in `Circle`: radial projection about `p`
onto the unit sphere, followed by `toComplex`. -/
private def directionMap (p : EuclideanSpace ℝ (Fin 2)) :
    C(({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2))), Circle) :=
  (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)).comp
    ((⟨toComplex.toLinearIsometry.unitSphereMap,
      toComplex.toLinearIsometry.continuous_unitSphereMap⟩ :
        C(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, sphere (0 : ℂ) 1)).comp
      (complSingletonHomotopyEquivSphere p).toFun)

/-- The direction about `p`, as a map out of the subspace of the pair `(ℝ², ℝ² ∖ {p})`. -/
private abbrev direction (p : EuclideanSpace ℝ (Fin 2)) :
    (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).snd ⟶ TopCat.of Circle :=
  TopCat.ofHom (directionMap p)

private lemma direction_def (p : EuclideanSpace ℝ (Fin 2)) :
    direction p = TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun ≫
      TopCat.ofHom ⟨toComplex.toLinearIsometry.unitSphereMap,
        toComplex.toLinearIsometry.continuous_unitSphereMap⟩ ≫
      TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)) :=
  rfl

/-- The direction about `p` of a point of `ℝ² ∖ {p}`, as a complex number. -/
private lemma coe_directionMap_apply (p : EuclideanSpace ℝ (Fin 2))
    (y : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (directionMap p y : ℂ) = toComplex ((y : EuclideanSpace ℝ (Fin 2)) - p) /
      ‖toComplex ((y : EuclideanSpace ℝ (Fin 2)) - p)‖ := by
  simp only [directionMap, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Circle.coe_homeomorphSphere_symm_apply, LinearIsometry.coe_unitSphereMap_apply,
    coe_complSingletonHomotopyEquivSphere_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    map_smul, LinearIsometryEquiv.norm_map, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

/-- The oriented local homology isomorphism of the identity chart of `ℝ²` at `p` is the connecting
morphism of `(ℝ², ℝ² ∖ {p})`, followed by the direction about `p` and
`Circle.singularHomologyOneIso`. -/
private lemma singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq
    (p : EuclideanSpace ℝ (Fin 2)) :
    (singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))) (x := p) (by simp) (n := 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation finrank_euclideanSpace_fin).hom =
      (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).singularHomologyδ
          R 2 1 rfl ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R).map (direction p) ≫
        (Circle.singularHomologyOneIso R).hom := by
  set H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R
  set H' := reducedSingularHomologyFunctor R 1
  set sC := reducedSingularHomologySphereIsoOfOrientation R Complex.orientation
    Complex.finrank_real_complex
  set h := TopCat.ofHom (Circle.homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle))
  -- The oriented generator of the unit circle of `ℂ`, read in `Circle`.
  have hC : sC.hom = (reducedSingularHomologyι R 1).app _ ≫ H.map h ≫
      (Circle.singularHomologyOneIso R).hom := by
    rw [← cancel_epi sC.inv, Iso.inv_hom_id, ← Category.assoc, ← Category.assoc,
      Category.assoc sC.inv, ← Circle.singularHomologyOneIso_inv_eq_complexOrientation,
      Iso.inv_hom_id]
  have hnat := reducedSingularHomologySphereIsoOfOrientation_hom_naturality R
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation Complex.orientation
    toComplex (by
      rw [← Complex.orientation_map_orthonormalBasisOneI_repr,
        LinearIsometryEquiv.toLinearEquiv_symm, ← Orientation.map_symm, Equiv.symm_apply_apply])
    (finrank_euclideanSpace_fin (n := 2))
  dsimp only at hnat
  refine (singularHomologyComplSingletonIsoOfOrientation_refl_hom _ _ _ _).trans ?_
  rw [direction_def]
  -- The subspace of the pair is `{p}ᶜ` only after unfolding `TopPair.ofSubset`.
  erw [Functor.map_comp, Functor.map_comp]
  rw [← hnat, hC, ← TopPair.reducedSingularHomologyδ_comp_ι]
  erw [(reducedSingularHomologyι R 1).naturality_assoc,
    (reducedSingularHomologyι R 1).naturality_assoc]
  -- The two sides differ by associativity, which `simp` cannot apply since the source of the
  -- radial projection is the subspace of the pair only after unfolding `TopPair.ofSubset`.
  rfl

/-! ### The faces of the standard simplex -/

/-- The inclusion of the full-dimensional standard `2`-simplex into `ℝ²`, as a singular
`2`-simplex. -/
private def stdTri : (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))) _⦋2⦌ :=
  ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
    ((ContinuousMap.subtypeVal (fullSimplex 2)).comp (fullSimplexEquivStdSimplex 2).symm)

/-- A face of the standard simplex is the segment between the vertices it keeps. -/
private lemma δ_stdTri (i : Fin 3) (a b : EuclideanSpace ℝ (Fin 2))
    (h₀ : ∀ w : Convexity.StdSimplex ℝ (Fin 2),
      (w.map i.succAbove).weights 1 = a 0 + w.weights 1 * (b 0 - a 0))
    (h₁ : ∀ w : Convexity.StdSimplex ℝ (Fin 2),
      (w.map i.succAbove).weights 2 = a 1 + w.weights 1 * (b 1 - a 1)) :
    (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i stdTri =
      TopCat.simplex₁ (X := TopCat.of (EuclideanSpace ℝ (Fin 2)))
        (Path.segment a b).toContinuousMap := by
  apply ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).injective
  ext w j
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_simplex₁]
  fin_cases j
  · simpa [stdTri, AffineMap.lineMap_apply_module', add_comm,
      Convexity.StdSimplex.homeomorphI_apply_coe] using h₀ w
  · simpa [stdTri, AffineMap.lineMap_apply_module', add_comm,
      Convexity.StdSimplex.homeomorphI_apply_coe] using h₁ w

private lemma δ_zero_stdTri :
    (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ 0 stdTri =
      TopCat.simplex₁ (X := TopCat.of (EuclideanSpace ℝ (Fin 2)))
        (Path.segment (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)).toContinuousMap := by
  refine δ_stdTri 0 _ _ (fun w ↦ ?_) fun w ↦ ?_
  · rw [show (1 : Fin 3) = Fin.succAbove 0 0 from rfl,
      Convexity.StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective]
    simp only [PiLp.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, PiLp.single_eq_of_ne,
      zero_sub, mul_neg, mul_one]
    linarith [w.total_fin_two]
  · rw [show (2 : Fin 3) = Fin.succAbove 0 1 from rfl,
      Convexity.StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective]
    simp

private lemma δ_one_stdTri :
    (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ 1 stdTri =
      TopCat.simplex₁ (X := TopCat.of (EuclideanSpace ℝ (Fin 2)))
        (Path.segment 0 (EuclideanSpace.single 1 1)).toContinuousMap := by
  refine δ_stdTri 1 _ _ (fun w ↦ ?_) fun w ↦ ?_
  · rw [Convexity.StdSimplex.weights_map_succAbove_self]
    simp
  · rw [show (2 : Fin 3) = Fin.succAbove 1 1 from rfl,
      Convexity.StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective]
    simp

private lemma δ_two_stdTri :
    (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ 2 stdTri =
      TopCat.simplex₁ (X := TopCat.of (EuclideanSpace ℝ (Fin 2)))
        (Path.segment 0 (EuclideanSpace.single 0 1)).toContinuousMap := by
  refine δ_stdTri 2 _ _ (fun w ↦ ?_) fun w ↦ ?_
  · rw [show (1 : Fin 3) = Fin.succAbove 2 1 from rfl,
      Convexity.StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective]
    simp
  · rw [Convexity.StdSimplex.weights_map_succAbove_self]
    simp

/-! ### The edges seen from an interior point -/

/-- Seen from a point `p` of the interior of the standard simplex, the vertices `0`, `e₀`, `e₁`
are nonzero, and they turn counterclockwise from `0` to `e₀` and from `e₀` to `e₁`, and clockwise
from `0` to `e₁`. -/
private lemma vertices_sub {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ interior (fullSimplex 2)) :
    toComplex (0 - p) ≠ 0 ∧ toComplex (EuclideanSpace.single 0 1 - p) ≠ 0 ∧
      0 < (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p)).im ∧
      0 < (toComplex (EuclideanSpace.single 1 1 - p) /
        toComplex (EuclideanSpace.single 0 1 - p)).im ∧
      (toComplex (EuclideanSpace.single 1 1 - p) / toComplex (0 - p)).im < 0 := by
  -- The coordinates of `p` are positive, with sum less than `1`.
  have hint := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.preimage_interior
    (coordinateSimplex (Fin 2))
  rw [ContinuousLinearEquiv.coe_toHomeomorph] at hint
  have hfs : fullSimplex 2 = (EuclideanSpace.equiv (Fin 2) ℝ) ⁻¹' coordinateSimplex (Fin 2) :=
    Set.ext fun x ↦ by simp [mem_coordinateSimplex]
  rw [hfs, ← hint, Set.mem_preimage, interior_coordinateSimplex] at hp
  obtain ⟨hpos, hsum⟩ := hp
  have h0 : 0 < p 0 := hpos 0
  have h1 : 0 < p 1 := hpos 1
  have h2 : p 0 + p 1 < 1 := by simpa [Fin.sum_univ_two] using hsum
  have im_div (z w : ℂ) : (z / w).im = (z.im * w.re - z.re * w.im) / Complex.normSq w := by
    rw [Complex.div_im]
    ring
  -- The coordinates of the vertices seen from `p`.
  have hAre : (toComplex (0 - p)).re = -p 0 := by simp
  have hAim : (toComplex (0 - p)).im = -p 1 := by simp
  have hBre : (toComplex (EuclideanSpace.single 0 1 - p)).re = 1 - p 0 := by simp
  have hBim : (toComplex (EuclideanSpace.single 0 1 - p)).im = -p 1 := by simp
  have hCre : (toComplex (EuclideanSpace.single 1 1 - p)).re = -p 0 := by simp
  have hCim : (toComplex (EuclideanSpace.single 1 1 - p)).im = 1 - p 1 := by simp
  have hA : toComplex (0 - p) ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    rw [hAim, Complex.zero_im] at this
    linarith
  have hB : toComplex (EuclideanSpace.single 0 1 - p) ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    rw [hBim, Complex.zero_im] at this
    linarith
  have hA' := Complex.normSq_pos.2 hA
  have hB' := Complex.normSq_pos.2 hB
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · rw [im_div]
    refine div_pos ?_ hA'
    rw [hAre, hAim, hBre, hBim]
    nlinarith
  · rw [im_div]
    refine div_pos ?_ hB'
    rw [hBre, hBim, hCre, hCim]
    nlinarith
  · rw [im_div]
    refine div_neg_of_neg_of_pos ?_ hA'
    rw [hAre, hAim, hCre, hCim]
    nlinarith

/-- Seen from `p`, the segment from `a` to `b` is the segment between the complex numbers of `a`
and `b`. -/
private lemma toComplex_segment_sub (a b p : EuclideanSpace ℝ (Fin 2)) (t : I) :
    toComplex (Path.segment a b t - p) =
      toComplex (a - p) + (t : ℝ) * (toComplex (b - p) - toComplex (a - p)) := by
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module',
    map_add, map_sub, map_smul, Complex.real_smul]
  ring

/-- A segment along which the direction from `p` turns by less than half a turn avoids `p`. -/
private lemma segment_ne {a b p : EuclideanSpace ℝ (Fin 2)} (hA : toComplex (a - p) ≠ 0)
    (hζ : (toComplex (b - p) / toComplex (a - p)).im ≠ 0) (t : I) : Path.segment a b t ≠ p := by
  intro h
  have hw := Complex.slitPlane_ne_zero (one_add_mul_sub_one_mem_slitPlane hζ t)
  have h0 := toComplex_segment_sub a b p t
  rw [h, sub_self, map_zero] at h0
  refine mul_ne_zero hA hw ?_
  rw [h0]
  field_simp

/-- The segment from `a` to `b`, as a path in `ℝ² ∖ {p}`. -/
private def segmentCompl {a b p : EuclideanSpace ℝ (Fin 2)} (hA : toComplex (a - p) ≠ 0)
    (hζ : (toComplex (b - p) / toComplex (a - p)).im ≠ 0) :
    C(I, (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).snd) :=
  ⟨fun t ↦ (⟨Path.segment a b t, segment_ne hA hζ t⟩ : ({p}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))),
    (Path.segment a b).continuous.subtype_mk _⟩

/-- The segment in `ℝ² ∖ {p}`, followed by the inclusion into `ℝ²`, is the segment of `ℝ²`. -/
private lemma toSSet_map_app_simplex₁_segmentCompl {a b p : EuclideanSpace ℝ (Fin 2)}
    (hA : toComplex (a - p) ≠ 0) (hζ : (toComplex (b - p) / toComplex (a - p)).im ≠ 0) :
    (TopCat.toSSet.map (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map).app _
        (TopCat.simplex₁ (X := (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).snd)
          (segmentCompl hA hζ)) =
      TopCat.simplex₁ (X := TopCat.of (EuclideanSpace ℝ (Fin 2)))
        (Path.segment a b).toContinuousMap := by
  rw [TopCat.toSSet_map_app_simplex₁, ofSubset_map]
  -- `segmentCompl` is `Path.segment a b` with its values in `ℝ² ∖ {p}`.
  rfl

/-- The direction from `p` along the segment from `a` to `b` is lifted by `segmentLift`. -/
private lemma toSSet_map_app_simplex₁_segmentCompl_direction {a b p : EuclideanSpace ℝ (Fin 2)}
    (hA : toComplex (a - p) ≠ 0) (hζ : (toComplex (b - p) / toComplex (a - p)).im ≠ 0) {c : ℝ}
    (hc : (Circle.exp c : ℂ) = toComplex (a - p) / ‖toComplex (a - p)‖) :
    (TopCat.toSSet.map (direction p)).app _
        (TopCat.simplex₁ (X := (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).snd)
          (segmentCompl hA hζ)) =
      TopCat.simplex₁ (Circle.exp.comp (segmentLift c _ hζ)) := by
  rw [TopCat.toSSet_map_app_simplex₁]
  congr 1
  ext t
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, coe_exp_segmentLift hA hζ hc,
    ← toComplex_segment_sub]
  exact coe_directionMap_apply p _

/-- The three edges of the standard simplex, as singular `1`-simplices of `ℝ² ∖ {p}`: from `e₀`
to `e₁`, from `0` to `e₁` and from `0` to `e₀`, the faces `δ₀`, `δ₁`, `δ₂`. -/
private def stdTriEdges {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ interior (fullSimplex 2)) :
    Fin 3 →
      (TopCat.toSSet.obj (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).snd) _⦋1⦌ :=
  ![TopCat.simplex₁ (segmentCompl (vertices_sub hp).2.1 (vertices_sub hp).2.2.2.1.ne'),
    TopCat.simplex₁ (segmentCompl (vertices_sub hp).1 (vertices_sub hp).2.2.2.2.ne),
    TopCat.simplex₁ (segmentCompl (vertices_sub hp).1 (vertices_sub hp).2.2.1.ne')]

/-- The faces of the standard simplex are the images of its edges in `ℝ² ∖ {p}`. -/
private lemma δ_stdTri_eq_stdTriEdges {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ interior (fullSimplex 2)) (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i stdTri =
      (TopCat.toSSet.map (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map).app
        _ (stdTriEdges hp i) := by
  fin_cases i
  · exact δ_zero_stdTri.trans (toSSet_map_app_simplex₁_segmentCompl _ _).symm
  · exact δ_one_stdTri.trans (toSSet_map_app_simplex₁_segmentCompl _ _).symm
  · exact δ_two_stdTri.trans (toSSet_map_app_simplex₁_segmentCompl _ _).symm

/-- The angles at an interior point `p` of the three edges of the standard simplex add up to a
full turn. -/
private lemma arg_div_add_arg_div {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ interior (fullSimplex 2)) :
    Complex.arg (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p)) +
        Complex.arg (toComplex (EuclideanSpace.single 1 1 - p) /
          toComplex (EuclideanSpace.single 0 1 - p)) =
      Complex.arg (toComplex (EuclideanSpace.single 1 1 - p) / toComplex (0 - p)) + 2 * π := by
  obtain ⟨hA, hB, hBA, hCB, hCA⟩ := vertices_sub hp
  have hmul : toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p) *
      (toComplex (EuclideanSpace.single 1 1 - p) / toComplex (EuclideanSpace.single 0 1 - p)) =
        toComplex (EuclideanSpace.single 1 1 - p) / toComplex (0 - p) := by
    field_simp
  rw [← hmul] at hCA ⊢
  -- Both factors lie in the upper half-plane and their product in the lower one.
  have ha := Complex.arg_nonneg_iff.2 hBA.le
  have hb := Complex.arg_nonneg_iff.2 hCB.le
  have hc := Complex.arg_neg_iff.2 hCA
  have hpi : π < Complex.arg (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p)) +
      Complex.arg (toComplex (EuclideanSpace.single 1 1 - p) /
        toComplex (EuclideanSpace.single 0 1 - p)) := by
    by_contra! h
    have := Complex.arg_mul (div_ne_zero hB hA) (fun h ↦ hCB.ne' (by rw [h, Complex.zero_im]))
      ⟨by linarith [Real.pi_pos], h⟩
    linarith
  linarith [Complex.arg_mul_of_pi_lt hpi]

/-! ### The class of the standard simplex -/

/-- The connecting morphism of `(ℝ², ℝ² ∖ {p})`, followed by the direction about `p`, sends the
class of the standard simplex to minus the generator of `H₁(Circle)`: the edge cycle winds once
counterclockwise around `p`. -/
private lemma relClass_stdTri_singularHomologyδ_direction {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ interior (fullSimplex 2))
    (hσ : ∀ i, Set.range ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i stdTri)) ⊆
        Set.range (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map) :
    (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass R stdTri hσ ≫
        (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).singularHomologyδ
          R 2 1 rfl ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj R).map
          (direction p) =
      -(Circle.singularHomologyOneIso R).inv := by
  obtain ⟨hA, hB, hBA, hCB, hCA⟩ := vertices_sub hp
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [relClass_singularHomologyδ_two (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2)))))
    R stdTri hσ (stdTriEdges hp) (δ_stdTri_eq_stdTriEdges hp)]
  -- The map induced by `direction p` on `H₁` is that of the singular simplicial sets.
  change _ ≫ SSet.homologyMap (TopCat.toSSet.map (direction p)) R 1 = _
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  -- The directions along the edges, lifted to `ℝ`.
  have hexpA := (Circle.coe_exp _).trans (Complex.exp_arg_mul_I hA)
  have hexpB : (Circle.exp (Complex.arg (toComplex (0 - p)) +
      Complex.arg (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p))) : ℂ) =
        toComplex (EuclideanSpace.single 0 1 - p) /
          ‖toComplex (EuclideanSpace.single 0 1 - p)‖ := by
    have hnA : (‖toComplex (0 - p)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hA
    have hnB : (‖toComplex (EuclideanSpace.single 0 1 - p)‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.2 hB
    rw [Circle.exp_add, Circle.coe_mul, hexpA, Circle.coe_exp,
      Complex.exp_arg_mul_I (div_ne_zero hB hA), norm_div,
      Complex.ofReal_div]
    field_simp
  -- The edge cycle, pushed forward by the direction about `p`.
  have hchain :
      ((TopCat.toSSet.obj _).ιChainComplex (stdTriEdges hp 0) -
        (TopCat.toSSet.obj _).ιChainComplex (stdTriEdges hp 1) +
        (TopCat.toSSet.obj _).ιChainComplex (stdTriEdges hp 2)) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (direction p)) R).f 1 =
      (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex (R := R)
          (TopCat.simplex₁ (Circle.exp.comp (segmentLift (Complex.arg (toComplex (0 - p)) +
            Complex.arg (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p))) _
              hCB.ne'))) -
        (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex
          (TopCat.simplex₁ (Circle.exp.comp (segmentLift (Complex.arg (toComplex (0 - p))) _
            hCA.ne))) +
        (TopCat.toSSet.obj (TopCat.of Circle)).ιChainComplex
          (TopCat.simplex₁ (Circle.exp.comp (segmentLift (Complex.arg (toComplex (0 - p))) _
            hBA.ne'))) := by
    simp only [stdTriEdges, Preadditive.add_comp, Preadditive.sub_comp, SSet.ι_chainComplexMap_f,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, toSSet_map_app_simplex₁_segmentCompl_direction _ _ hexpB,
      toSSet_map_app_simplex₁_segmentCompl_direction _ _ hexpA]
  refine Eq.trans ?_ (Circle.liftCycles_simplex₁_exp_comp_homologyπ R
    (segmentLift (Complex.arg (toComplex (0 - p)) +
      Complex.arg (toComplex (EuclideanSpace.single 0 1 - p) / toComplex (0 - p))) _ hCB.ne')
    (segmentLift (Complex.arg (toComplex (0 - p))) _ hCA.ne)
    (segmentLift (Complex.arg (toComplex (0 - p))) _ hBA.ne')
    ((segmentLift_zero _ _ _).trans (segmentLift_zero _ _ _).symm)
    ((segmentLift_one _ _ _).trans (segmentLift_zero _ _ _).symm)
    (by rw [segmentLift_one, segmentLift_one]; linarith [arg_div_add_arg_div hp]))
  congr 1
  rw [← cancel_mono (HomologicalComplex.iCycles _ 1)]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  -- The homology instances of the pair's lemma and of `ModuleCat` agree only up to unfolding.
  erw [HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
  exact hchain

/-- **The faces of the standard `2`-simplex avoid its interior.** Read as a singular `2`-simplex
of `ℝ²` through `TauCeti.fullSimplexEquivStdSimplex`, the inclusion of the full-dimensional
standard simplex has each face in `ℝ² ∖ {p}`, for `p` in the interior of the simplex. -/
theorem range_toSSetObjEquiv_δ_fullSimplex_subset {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ interior (fullSimplex 2)) (i : Fin 3) :
    Set.range ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i
        (((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
          ((ContinuousMap.subtypeVal (fullSimplex 2)).comp
            (fullSimplexEquivStdSimplex 2).symm)))) ⊆
      Set.range (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map := by
  have hs := δ_stdTri_eq_stdTriEdges hp i
  rw [stdTri] at hs
  rw [hs]
  rintro _ ⟨w, rfl⟩
  exact ⟨_, rfl⟩

/-- **The local class of the standard `2`-simplex.** Let `p` be a point of the interior of the
full-dimensional standard simplex `fullSimplex 2 ⊆ ℝ²`, with vertices `0`, `e₀`, `e₁`. Read as a
singular `2`-simplex of `ℝ²` through `TauCeti.fullSimplexEquivStdSimplex`, its inclusion has its
faces in `ℝ² ∖ {p}`, so it has a class in `H₂(ℝ², ℝ² ∖ {p}; ℤ)` (`TopPair.relClass`). This class
is **minus** the local orientation at `p` that the identity chart selects for the standard
orientation of `ℝ²`: the sign `s` with `[σ] = s • (local orientation)` is `-1`. -/
theorem relClass_fullSimplex_eq_neg_localOrientationOfOrientedChart
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ interior (fullSimplex 2))
    (hσ : ∀ i : Fin 3, Set.range ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i
        (((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
          ((ContinuousMap.subtypeVal (fullSimplex 2)).comp
            (fullSimplexEquivStdSimplex 2).symm)))) ⊆
      Set.range (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map) :
    (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1)
        (((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
          ((ContinuousMap.subtypeVal (fullSimplex 2)).comp (fullSimplexEquivStdSimplex 2).symm))
        hσ 1 =
      -((OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))).localOrientationOfOrientedChart
        (x := p) (by simp) (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
        finrank_euclideanSpace_fin).val := by
  have key : (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass R stdTri hσ =
      -(singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))) (x := p) (by simp) (n := 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
          finrank_euclideanSpace_fin).inv := by
    rw [← cancel_mono (singularHomologyComplSingletonIsoOfOrientation R
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))) (x := p) (by simp) (n := 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation finrank_euclideanSpace_fin).hom,
      Preadditive.neg_comp, Iso.inv_hom_id,
      singularHomologyComplSingletonIsoOfOrientation_refl_hom_eq p]
    have h := relClass_stdTri_singularHomologyδ_direction hp hσ
    have h' := congrArg (· ≫ (Circle.singularHomologyOneIso R).hom) h
    simp only [Category.assoc, Preadditive.neg_comp, Iso.inv_hom_id] at h'
    exact h'
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  -- `stdTri` and `R` are the simplex and the coefficients of the statement, and the negative of
  -- a linear map is evaluated pointwise.
  exact ConcreteCategory.congr_hom key 1

/-- **The local class of the standard `2`-simplex, for the smooth orientation of `ℝ²`.** For `p` in
the interior of `fullSimplex 2`, the class in `H₂(ℝ², ℝ² ∖ {p}; ℤ)` of the inclusion of the
standard simplex is minus the local orientation at `p` of the homological orientation of the
standard orientation of `ℝ²` (`TauCeti.Manifold.Orientation.euclideanSpace`). -/
theorem relClass_fullSimplex_eq_neg_toHomologicalOrientation
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ interior (fullSimplex 2))
    (hσ : ∀ i : Fin 3, Set.range ((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin 2)))).δ i
        (((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
          ((ContinuousMap.subtypeVal (fullSimplex 2)).comp
            (fullSimplexEquivStdSimplex 2).symm)))) ⊆
      Set.range (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).map) :
    (ofSubset ({p}ᶜ : Set (TopCat.of (EuclideanSpace ℝ (Fin 2))))).relClass
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (n := 1)
        (((TopCat.of (EuclideanSpace ℝ (Fin 2))).toSSetObjEquiv _).symm
          ((ContinuousMap.subtypeVal (fullSimplex 2)).comp (fullSimplexEquivStdSimplex 2).symm))
        hσ 1 =
      -((Manifold.Orientation.euclideanSpace 2).toHomologicalOrientation
        finrank_euclideanSpace_fin p).val := by
  rw [relClass_fullSimplex_eq_neg_localOrientationOfOrientedChart hp hσ,
    Manifold.Orientation.toHomologicalOrientation_apply_eq_localOrientationOfOrientedChart
      finrank_euclideanSpace_fin _ finrank_euclideanSpace_fin
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin 2))) (by simp)
      (ContinuousLinearEquiv.refl ℝ _) ?_ ?_]
  · simpa using hasFDerivAt_id (𝕜 := ℝ) p
  · rw [show ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)) :
        EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) = LinearEquiv.refl ℝ _ from
        LinearEquiv.ext fun _ ↦ rfl, Orientation.map_refl]
    exact Manifold.Orientation.orientationAt_euclideanSpace 2 p

end TopPair
