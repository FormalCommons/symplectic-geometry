/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.Genus
public import SymplecticGeometry.Geometry.Manifold.Instances.Surface.TorusWedge
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.GroupTheory.SurfaceGroup.Free
import SymplecticGeometry.Topology.Instances.AddCircle.Icc
import TauCeti.Topology.Homotopy.PuncturedStarConvex
import TauCeti.Topology.Homotopy.Quotient

/-!
# The punctured torus retracts onto its two circles through `0`

The torus `SymplecticGeometry.EuclideanTorus`, punctured at the centre `([1 / 2], [1 / 2])` of the
coordinate ball `SymplecticGeometry.EuclideanTorus.ball` along which it is summed, deforms onto
the union `SymplecticGeometry.EuclideanTorus.circles` of its two circles `{x | x i = 0}` through
`0`, keeping these circles fixed. So the inclusion of the two circles is a homotopy equivalence,
and it induces an isomorphism of fundamental groups at `0`.

Read in Tau Ceti's torus `Fin 2 → AddCircle 1` through
`SymplecticGeometry.EuclideanTorus.diffeomorph`, the two circles are
`SymplecticGeometry.torusCircles`, whose fundamental group is free on `Fin 2`
(`SymplecticGeometry.torusCirclesFundamentalGroupMulEquiv`). Matching its generators with `a 0`
and `b 0` in Tau Ceti's `TauCeti.SurfaceGroup.Orientable.equivFreeGroup 1 0` identifies the
fundamental group of the punctured torus with the surface group
`TauCeti.SurfaceGroup.Orientable 1 1` of the torus with one boundary circle, the loops
`t ↦ ([t], 0)` and `t ↦ (0, [t])` going to `a 0` and `b 0`.

The torus is the image of the unit square `[0, 1]²` of `ℝ × ℝ` under `z ↦ ([z.1], [z.2])`, the
covering map `SymplecticGeometry.EuclideanTorus.cover` read on `ℝ × ℝ`, a continuous surjection
from a compact space onto a Hausdorff one; its centre `(1 / 2, 1 / 2)` goes to the puncture, its
boundary onto the two circles, and only boundary points are identified. In the sup norm of
`ℝ × ℝ` the square is the closed ball of radius `1 / 2` about the centre (Mathlib's
`closedBall_prod_same`), and its boundary is the sphere (`sphere_prod`), so Tau Ceti's
`StarConvex.radialHomotopy` deforms the punctured square onto its boundary, keeping the boundary
fixed. Since it fixes the points that the map identifies, it descends to the punctured torus,
along the restriction of the map to the punctured square, which is closed and hence a quotient
map: the retraction by Mathlib's `Topology.IsQuotientMap.lift`, and the homotopy by Tau Ceti's
`Topology.IsQuotientMap.liftHomotopy`. The argument follows that of the private `deform` and
`retraction` of Tau Ceti's `TauCeti.TwoCellAttachment`
(`AlgebraicTopology/FundamentalGroup/TwoCellAttachment.lean`), which descend Tau Ceti's
`unitInterval.radialPush` to the complement of the centres of attached 2-cells; here the
deformation of the punctured square itself is used, so that the homotopy stays in the punctured
torus.

## Main definitions

* `SymplecticGeometry.EuclideanTorus.circles`: the two circles of the torus through `0`.
* `SymplecticGeometry.EuclideanTorus.circlesInclusion`: their inclusion into the punctured torus.
* `SymplecticGeometry.EuclideanTorus.circlesRetraction`: the retraction of the punctured torus
  onto them.
* `SymplecticGeometry.EuclideanTorus.circlesHomotopyRel`: a homotopy, fixed on the two circles,
  from the retraction followed by the inclusion to the identity of the punctured torus.
* `SymplecticGeometry.EuclideanTorus.circlesHomotopyEquiv`: the inclusion, as a homotopy
  equivalence.
* `SymplecticGeometry.EuclideanTorus.circlesFundamentalGroupMulEquiv`: the isomorphism of
  fundamental groups at `0` induced by the inclusion.
* `SymplecticGeometry.EuclideanTorus.circlesHomeomorph`: the two circles, as
  `SymplecticGeometry.torusCircles`.
* `SymplecticGeometry.EuclideanTorus.circleLoop i`: the loop `t ↦ Pi.single i [t]` of the
  punctured torus.
* `SymplecticGeometry.EuclideanTorus.puncturedFundamentalGroupMulEquiv`: the fundamental group of
  the punctured torus at `0` is `TauCeti.SurfaceGroup.Orientable 1 1`.

## Main results

* `SymplecticGeometry.EuclideanTorus.circlesRetraction_comp_circlesInclusion`: the retraction is a
  left inverse of the inclusion.
* `SymplecticGeometry.EuclideanTorus.diffeomorph_circlesHomotopyRel_apply`,
  `SymplecticGeometry.EuclideanTorus.diffeomorph_circlesRetraction_apply`: the homotopy and the
  retraction in the coordinates of the square.
* `SymplecticGeometry.EuclideanTorus.puncturedFundamentalGroupMulEquiv_circleLoop_zero`,
  `SymplecticGeometry.EuclideanTorus.puncturedFundamentalGroupMulEquiv_circleLoop_one`: it sends
  the two circle loops to the generators `a 0` and `b 0`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (the punctured torus
  deforms onto the wedge of two circles).
-/

public section

noncomputable section

open Set Metric Topology TauCeti unitInterval
open scoped ContinuousMap

namespace SymplecticGeometry

namespace EuclideanTorus

/-- The **two circles** `{x | x 0 = 0}` and `{x | x 1 = 0}` of the torus through its base point
`0`, a wedge of two circles. -/
def circles : Set EuclideanTorus := {x | diffeomorph x 0 = 0} ∪ {x | diffeomorph x 1 = 0}

/-- A point lies on the two circles when one of its coordinates is `0`. -/
theorem mem_circles_iff {x : EuclideanTorus} :
    x ∈ circles ↔ diffeomorph x 0 = 0 ∨ diffeomorph x 1 = 0 :=
  Iff.rfl

/-- The base point `0` lies on the two circles. -/
theorem zero_mem_circles : (0 : EuclideanTorus) ∈ circles :=
  Or.inl (by rw [mem_ofPred_eq, diffeomorph_zero, Pi.zero_apply])

/-- The two circles miss the puncture, the centre of the coordinate ball of the torus. -/
theorem circles_subset_puncture : circles ⊆ ConnectedSum.puncture ball := by
  intro x hx
  rw [SetLike.mem_coe, ConnectedSum.mem_puncture]
  rintro rfl
  rcases hx with hx | hx
  · exact disjoint_left.1 (disjoint_closure_range_ball 0) (subset_closure ⟨0, rfl⟩) hx
  · exact disjoint_left.1 (disjoint_closure_range_ball 1) (subset_closure ⟨0, rfl⟩) hx

/-- The base point `0` of the torus is not the puncture. -/
theorem zero_mem_puncture : (0 : EuclideanTorus) ∈ ConnectedSum.puncture ball :=
  circles_subset_puncture zero_mem_circles

/-! ### The unit square -/

/-- The centre `(1 / 2, 1 / 2)` of the unit square of `ℝ × ℝ`. -/
private def centre : ℝ × ℝ := (1 / 2, 1 / 2)

/-- The unit square of `ℝ × ℝ`. -/
private def square : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

/-- In the sup norm of `ℝ × ℝ`, the unit square is the closed ball of radius `1 / 2` about its
centre. -/
private theorem square_eq_closedBall : square = closedBall centre (1 / 2) := by
  rw [centre, ← closedBall_prod_same, Real.closedBall_eq_Icc, square]
  norm_num

private theorem starConvex_square : StarConvex ℝ centre square :=
  square_eq_closedBall ▸ (convex_closedBall _ _).starConvex (mem_closedBall_self (by norm_num))

private theorem sphere_subset_square : sphere centre (1 / 2) ⊆ square :=
  square_eq_closedBall ▸ sphere_subset_closedBall

/-- A point of the square lies on the sphere of radius `1 / 2` about the centre, in the sup norm,
exactly when one of its coordinates is `0` or `1`. -/
private theorem mem_sphere_centre_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    z ∈ sphere centre (1 / 2) ↔ (z.1 = 0 ∨ z.1 = 1) ∨ (z.2 = 0 ∨ z.2 = 1) := by
  rw [square_eq_closedBall, centre, ← closedBall_prod_same] at hz
  rw [sphere_prod, centre, Real.sphere_eq_pair _ (by norm_num)]
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, hz.1, hz.2, and_true,
    true_and]
  norm_num

/-- The map `z ↦ ([z.1], [z.2])` of `ℝ × ℝ` onto the torus, the covering map read on `ℝ × ℝ`. -/
private def squareMap (z : ℝ × ℝ) : EuclideanTorus :=
  cover (WithLp.toLp 2 ![z.1, z.2])

private theorem diffeomorph_squareMap_zero (z : ℝ × ℝ) :
    diffeomorph (squareMap z) 0 = z.1 := by
  simp [squareMap]

private theorem diffeomorph_squareMap_one (z : ℝ × ℝ) :
    diffeomorph (squareMap z) 1 = z.2 := by
  simp [squareMap]

private theorem continuous_squareMap : Continuous squareMap :=
  isLocalHomeomorph_cover.continuous.comp ((PiLp.continuous_toLp _ _).comp (by fun_prop))

private theorem squareMap_eq_iff {z w : ℝ × ℝ} :
    squareMap z = squareMap w ↔
      (z.1 : AddCircle (1 : ℝ)) = w.1 ∧ (z.2 : AddCircle (1 : ℝ)) = w.2 := by
  refine ⟨fun h ↦ ?_, fun h ↦
    EquivLike.injective diffeomorph (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))⟩
  · rw [← diffeomorph_squareMap_zero, ← diffeomorph_squareMap_one, h, diffeomorph_squareMap_zero,
      diffeomorph_squareMap_one]
    exact ⟨rfl, rfl⟩
  · rw [diffeomorph_squareMap_zero, diffeomorph_squareMap_zero, h.1]
  · rw [diffeomorph_squareMap_one, diffeomorph_squareMap_one, h.2]

/-- Every point of the torus is the image of a point of the square. -/
private theorem exists_mem_square_squareMap_eq (x : EuclideanTorus) :
    ∃ z ∈ square, squareMap z = x := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (diffeomorph x 0)
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective (diffeomorph x 1)
  refine ⟨(Int.fract a, Int.fract b), ⟨⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩,
    ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩⟩,
    EquivLike.injective diffeomorph (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))⟩
  · rw [diffeomorph_squareMap_zero]
    exact (AddCircle.coe_fract a).trans ha
  · rw [diffeomorph_squareMap_one]
    exact (AddCircle.coe_fract b).trans hb

/-- The map sends the centre of the square, and no other point of it, to the puncture. -/
private theorem squareMap_eq_ball_zero_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    squareMap z = ball 0 ↔ z = centre := by
  have hc : squareMap centre = ball 0 :=
    EquivLike.injective diffeomorph (funext (Fin.forall_fin_two.2
      ⟨by rw [diffeomorph_squareMap_zero, diffeomorph_ball_zero, centre],
        by rw [diffeomorph_squareMap_one, diffeomorph_ball_zero, centre]⟩))
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hc⟩
  have hm : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (0 + 1) := ⟨by norm_num, by norm_num⟩
  obtain ⟨h₁, h₂⟩ := squareMap_eq_iff.1 (h.trans hc.symm)
  have k {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (h : (a : AddCircle (1 : ℝ)) = (1 / 2 : ℝ)) :
      a = 1 / 2 := by
    rcases (AddCircle.coe_eq_coe_iff_of_mem_Icc (by rwa [zero_add]) hm).1 h with
      h | ⟨-, h⟩ | ⟨-, h⟩ <;> norm_num at h
    exact h
  exact Prod.ext (k hz.1 h₁) (k hz.2 h₂)

/-- The map sends a point of the square to the two circles exactly when it lies on the boundary
of the square. -/
private theorem squareMap_mem_circles_iff {z : ℝ × ℝ} (hz : z ∈ square) :
    squareMap z ∈ circles ↔ z ∈ sphere centre (1 / 2) := by
  rw [mem_sphere_centre_iff hz, mem_circles_iff, diffeomorph_squareMap_zero,
    diffeomorph_squareMap_one, AddCircle.coe_eq_zero_iff_of_mem_Icc hz.1,
    AddCircle.coe_eq_zero_iff_of_mem_Icc hz.2]

/-- Two points of the square with the same image are equal, or both on its boundary. -/
private theorem eq_or_mem_sphere_of_squareMap_eq {z w : ℝ × ℝ} (hz : z ∈ square)
    (hw : w ∈ square) (h : squareMap z = squareMap w) :
    z = w ∨ (z ∈ sphere centre (1 / 2) ∧ w ∈ sphere centre (1 / 2)) := by
  obtain ⟨h₁, h₂⟩ := squareMap_eq_iff.1 h
  rw [mem_sphere_centre_iff hz, mem_sphere_centre_iff hw]
  have k {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
      (h : (a : AddCircle (1 : ℝ)) = b) : a = b ∨ ((a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1)) := by
    rw [AddCircle.coe_eq_coe_iff_of_mem_Icc (a := 0) (by rwa [zero_add]) (by rwa [zero_add]),
      zero_add] at h
    tauto
  rcases k hz.1 hw.1 h₁ with e₁ | ⟨e₁, e₁'⟩
  · rcases k hz.2 hw.2 h₂ with e₂ | ⟨e₂, e₂'⟩
    · exact Or.inl (Prod.ext e₁ e₂)
    · exact Or.inr ⟨Or.inr e₂, Or.inr e₂'⟩
  · exact Or.inr ⟨Or.inl e₁, Or.inl e₁'⟩

/-! ### The deformation of the punctured square onto its boundary -/

/-- The square punctured at its centre. -/
private abbrev PuncturedSquare : Type := ↥(square \ {centre})

/-- The radial deformation of the punctured square onto its boundary, Tau Ceti's
`StarConvex.radialHomotopy`, from the radial projection to the identity. -/
private def squareHomotopy :=
  starConvex_square.radialHomotopy (by norm_num : (0 : ℝ) < 1 / 2) sphere_subset_square

/-- The deformation fixes the boundary of the square. -/
private theorem squareHomotopy_apply_of_mem_sphere (t : I) {z : PuncturedSquare}
    (hz : (z : ℝ × ℝ) ∈ sphere centre (1 / 2)) : squareHomotopy (t, z) = z := by
  refine Subtype.ext ?_
  rw [squareHomotopy, StarConvex.coe_radialHomotopy_apply, ← dist_eq_norm, mem_sphere.1 hz,
    div_self (by norm_num)]
  simp

/-- At time `0` the deformation sends the punctured square to its boundary. -/
private theorem squareHomotopy_zero_mem_sphere (z : PuncturedSquare) :
    (squareHomotopy (0, z) : ℝ × ℝ) ∈ sphere centre (1 / 2) := by
  rw [ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply,
    coe_sphereInclusionDiffSingleton_apply]
  exact Subtype.property _

private theorem squareMap_mem_puncture (z : PuncturedSquare) :
    squareMap z ∈ ConnectedSum.puncture ball :=
  ConnectedSum.mem_puncture.2 fun h ↦ z.property.2 (mem_singleton_iff.2 ((squareMap_eq_ball_zero_iff
    z.property.1).1 h))

/-- The map `z ↦ ([z.1], [z.2])` of the punctured square onto the punctured torus. -/
private def puncturedSquareMap : C(PuncturedSquare, ConnectedSum.puncture ball) :=
  ⟨fun z ↦ ⟨squareMap z, squareMap_mem_puncture z⟩,
    (continuous_squareMap.comp continuous_subtypeVal).subtype_mk _⟩

private theorem coe_puncturedSquareMap (z : PuncturedSquare) :
    (puncturedSquareMap z : EuclideanTorus) = squareMap z :=
  (rfl)

private theorem puncturedSquareMap_surjective : Function.Surjective puncturedSquareMap := by
  intro x
  obtain ⟨z, hz, hzx⟩ := exists_mem_square_squareMap_eq x
  refine ⟨⟨z, hz, fun h ↦ ConnectedSum.mem_puncture.1 x.property ?_⟩, Subtype.ext hzx⟩
  rw [← hzx, squareMap_eq_ball_zero_iff hz]
  exact h

/-- The map of the punctured square onto the punctured torus is closed: the image of a closed set
is the trace on the punctured torus of the image of a compact subset of the square. -/
private theorem isClosedMap_puncturedSquareMap : IsClosedMap puncturedSquareMap := by
  intro C hC
  obtain ⟨C', hC', rfl⟩ := IsInducing.subtypeVal.isClosed_iff.1 hC
  have hK : IsCompact (C' ∩ square) := (isCompact_Icc.prod isCompact_Icc).inter_left hC'
  refine IsInducing.subtypeVal.isClosed_iff.2
    ⟨squareMap '' (C' ∩ square), (hK.image continuous_squareMap).isClosed, ?_⟩
  ext x
  constructor
  · rintro ⟨w, ⟨hwC, hwK⟩, hw⟩
    refine ⟨⟨w, hwK, fun h ↦ ConnectedSum.mem_puncture.1 x.property ?_⟩, hwC, Subtype.ext hw⟩
    rw [← hw, squareMap_eq_ball_zero_iff hwK]
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz, z.property.1⟩, coe_puncturedSquareMap z⟩

private theorem isQuotientMap_puncturedSquareMap : IsQuotientMap puncturedSquareMap :=
  isClosedMap_puncturedSquareMap.isQuotientMap puncturedSquareMap.continuous
    puncturedSquareMap_surjective

/-- The radial deformation of the punctured square, followed by its map to the punctured torus. -/
private def squareDeform :=
  (ContinuousMap.Homotopy.refl puncturedSquareMap).comp squareHomotopy

private theorem squareDeform_apply (p : I × PuncturedSquare) :
    squareDeform p = puncturedSquareMap (squareHomotopy p) := by
  simp [squareDeform]

/-- The deformation of the punctured square, carried to the punctured torus, is constant on the
fibres of the map: the points that the map identifies lie on the boundary of the square, which the
deformation fixes. -/
private theorem squareDeform_eq_of_eq (t : I) (z w : PuncturedSquare)
    (h : puncturedSquareMap z = puncturedSquareMap w) :
    squareDeform (t, z) = squareDeform (t, w) := by
  rw [squareDeform_apply, squareDeform_apply]
  rcases eq_or_mem_sphere_of_squareMap_eq z.property.1 w.property.1 (congrArg Subtype.val h) with
    h' | ⟨h₁, h₂⟩
  · rw [Subtype.ext h']
  · rw [squareHomotopy_apply_of_mem_sphere t h₁, squareHomotopy_apply_of_mem_sphere t h₂, h]

/-! ### The deformation of the punctured torus onto the two circles -/

/-- The end of the radial deformation, descended to the punctured torus. -/
private def retract : C(ConnectedSum.puncture ball, ConnectedSum.puncture ball) :=
  isQuotientMap_puncturedSquareMap.lift (squareDeform.curry 0) fun z w h ↦ by
    simpa only [ContinuousMap.Homotopy.curry_apply] using squareDeform_eq_of_eq 0 z w h

private theorem retract_comp_puncturedSquareMap :
    retract.comp puncturedSquareMap = squareDeform.curry 0 :=
  IsQuotientMap.lift_comp _ _ _

private theorem retract_puncturedSquareMap (z : PuncturedSquare) :
    retract (puncturedSquareMap z) = puncturedSquareMap (squareHomotopy (0, z)) := by
  rw [← ContinuousMap.comp_apply, retract_comp_puncturedSquareMap,
    ContinuousMap.Homotopy.curry_apply, squareDeform_apply]

private theorem retract_mem_circles (x : ConnectedSum.puncture ball) :
    (retract x : EuclideanTorus) ∈ circles := by
  obtain ⟨z, rfl⟩ := puncturedSquareMap_surjective x
  rw [retract_puncturedSquareMap, coe_puncturedSquareMap,
    squareMap_mem_circles_iff (squareHomotopy (0, z)).property.1]
  exact squareHomotopy_zero_mem_sphere z

/-- The inclusion of the two circles of the torus through `0` into the punctured torus. -/
-- Exposed so that its value `⟨0, _⟩` at `0`, the base point of the fundamental groups that it
-- relates, holds by `rfl` in the statements of this and other files.
@[expose] def circlesInclusion : C(circles, ConnectedSum.puncture ball) :=
  ⟨fun x ↦ ⟨x, circles_subset_puncture x.property⟩, continuous_subtypeVal.subtype_mk _⟩

/-- The inclusion does not move points. -/
@[simp]
theorem coe_circlesInclusion_apply (x : circles) :
    (circlesInclusion x : EuclideanTorus) = x :=
  (rfl)

/-- The **retraction of the punctured torus onto its two circles through `0`**: the radial
deformation of the punctured square `[0, 1]²` onto its boundary, at its end, carried to the
torus by `z ↦ ([z.1], [z.2])`. It is a left inverse of the inclusion
(`SymplecticGeometry.EuclideanTorus.circlesRetraction_comp_circlesInclusion`), and its composite
with the inclusion is homotopic to the identity relative to the two circles
(`SymplecticGeometry.EuclideanTorus.circlesHomotopyRel`). -/
def circlesRetraction : C(ConnectedSum.puncture ball, circles) :=
  ⟨fun x ↦ ⟨retract x, retract_mem_circles x⟩,
    (continuous_subtypeVal.comp retract.continuous).subtype_mk _⟩

private theorem circlesInclusion_circlesRetraction (x : ConnectedSum.puncture ball) :
    circlesInclusion (circlesRetraction x) = retract x :=
  (rfl)

/-- The radial deformation of the punctured square, descended to the punctured torus by Tau Ceti's
`Topology.IsQuotientMap.liftHomotopy`. -/
private def deform :
    (circlesInclusion.comp circlesRetraction).Homotopy (ContinuousMap.id _) :=
  isQuotientMap_puncturedSquareMap.liftHomotopy squareDeform squareDeform_eq_of_eq
    (fun z ↦ by
      rw [ContinuousMap.comp_apply, circlesInclusion_circlesRetraction, retract_puncturedSquareMap,
        ContinuousMap.Homotopy.apply_zero]
      simp only [ContinuousMap.comp_apply])
    (fun z ↦ by simp)

private theorem deform_puncturedSquareMap (t : I) (z : PuncturedSquare) :
    deform (t, puncturedSquareMap z) = puncturedSquareMap (squareHomotopy (t, z)) :=
  (isQuotientMap_puncturedSquareMap.liftHomotopy_apply _ _ _ _ t z).trans (squareDeform_apply _)

private theorem deform_of_mem_circles (t : I) {x : ConnectedSum.puncture ball}
    (hx : (x : EuclideanTorus) ∈ circles) : deform (t, x) = x := by
  obtain ⟨z, rfl⟩ := puncturedSquareMap_surjective x
  rw [coe_puncturedSquareMap, squareMap_mem_circles_iff z.property.1] at hx
  rw [deform_puncturedSquareMap, squareHomotopy_apply_of_mem_sphere t hx]

/-- The retraction fixes the two circles. -/
@[simp]
theorem circlesRetraction_circlesInclusion (x : circles) :
    circlesRetraction (circlesInclusion x) = x := by
  refine Subtype.ext ?_
  rw [← coe_circlesInclusion_apply (circlesRetraction _), ← ContinuousMap.comp_apply,
    ← deform.apply_zero, deform_of_mem_circles 0 x.property, coe_circlesInclusion_apply]

/-- The retraction is a left inverse of the inclusion. -/
theorem circlesRetraction_comp_circlesInclusion :
    circlesRetraction.comp circlesInclusion = ContinuousMap.id circles :=
  ContinuousMap.ext circlesRetraction_circlesInclusion

/-- The **deformation of the punctured torus onto its two circles through `0`**: a homotopy from
the retraction onto the two circles, followed by their inclusion, to the identity of the
punctured torus, which fixes the points of the two circles. It is the radial deformation of the
punctured square `[0, 1]²` onto its boundary, carried to the torus by `z ↦ ([z.1], [z.2])`. -/
def circlesHomotopyRel :
    (circlesInclusion.comp circlesRetraction).HomotopyRel (ContinuousMap.id _)
      (Subtype.val ⁻¹' circles) where
  toHomotopy := deform
  prop' t x hx := (deform_of_mem_circles t hx).trans
    ((deform.apply_zero x).symm.trans (deform_of_mem_circles 0 hx)).symm

private theorem circlesHomotopyRel_apply (p : I × ConnectedSum.puncture ball) :
    circlesHomotopyRel p = deform p :=
  (rfl)

/-- The homotopy in coordinates: at time `t`, the point `([a], [b])` of the punctured torus, with
`a`, `b` in `[0, 1]`, moves to `([1 / 2 + c (a - 1 / 2)], [1 / 2 + c (b - 1 / 2)])` along the
ray from the centre of the square, where `c = (1 - t) / (2 m) + t` and `m` is the sup-norm
distance `max |a - 1 / 2| |b - 1 / 2|` from `(a, b)` to the centre. -/
theorem diffeomorph_circlesHomotopyRel_apply (t : I) (x : ConnectedSum.puncture ball) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hx : diffeomorph (x : EuclideanTorus) = ![(a : AddCircle (1 : ℝ)), b]) :
    diffeomorph (circlesHomotopyRel (t, x) : EuclideanTorus) =
      ![((1 / 2 + ((1 - t) * (1 / 2 / max |a - 1 / 2| |b - 1 / 2|) + t) * (a - 1 / 2) : ℝ) :
          AddCircle (1 : ℝ)),
        ((1 / 2 + ((1 - t) * (1 / 2 / max |a - 1 / 2| |b - 1 / 2|) + t) * (b - 1 / 2) : ℝ) :
          AddCircle (1 : ℝ))] := by
  have hxz : (x : EuclideanTorus) = squareMap (a, b) :=
    EquivLike.injective diffeomorph (hx.trans (funext (Fin.forall_fin_two.2
      ⟨by simp [squareMap], by simp [squareMap]⟩)))
  have hz : (a, b) ∈ square \ {centre} := ⟨⟨ha, hb⟩, fun h ↦ ConnectedSum.mem_puncture.1 x.property
    (hxz.trans ((squareMap_eq_ball_zero_iff ⟨ha, hb⟩).2 h))⟩
  obtain rfl : x = puncturedSquareMap ⟨(a, b), hz⟩ := Subtype.ext hxz
  rw [circlesHomotopyRel_apply, deform_puncturedSquareMap, coe_puncturedSquareMap]
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · rw [diffeomorph_squareMap_zero, squareHomotopy, StarConvex.coe_radialHomotopy_apply]
    simp [centre, Prod.norm_def]
  · rw [diffeomorph_squareMap_one, squareHomotopy, StarConvex.coe_radialHomotopy_apply]
    simp [centre, Prod.norm_def]

/-- The retraction in coordinates: the point `([a], [b])` of the punctured torus, with `a`, `b` in
`[0, 1]`, goes to `([1 / 2 + (a - 1 / 2) / (2 m)], [1 / 2 + (b - 1 / 2) / (2 m)])`, its radial
projection from the centre of the square onto its boundary, where `m` is the sup-norm distance
`max |a - 1 / 2| |b - 1 / 2|` from `(a, b)` to the centre. -/
theorem diffeomorph_circlesRetraction_apply (x : ConnectedSum.puncture ball) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hx : diffeomorph (x : EuclideanTorus) = ![(a : AddCircle (1 : ℝ)), b]) :
    diffeomorph (circlesRetraction x : EuclideanTorus) =
      ![((1 / 2 + 1 / 2 / max |a - 1 / 2| |b - 1 / 2| * (a - 1 / 2) : ℝ) : AddCircle (1 : ℝ)),
        ((1 / 2 + 1 / 2 / max |a - 1 / 2| |b - 1 / 2| * (b - 1 / 2) : ℝ) : AddCircle (1 : ℝ))] := by
  rw [← coe_circlesInclusion_apply, ← ContinuousMap.comp_apply, ← circlesHomotopyRel.apply_zero,
    diffeomorph_circlesHomotopyRel_apply 0 x ha hb hx]
  simp

/-- The two circles of the torus through `0` are a strong deformation retract of the punctured
torus: their inclusion is a homotopy equivalence, with the retraction
`SymplecticGeometry.EuclideanTorus.circlesRetraction` as its inverse. -/
def circlesHomotopyEquiv : circles ≃ₕ ConnectedSum.puncture ball where
  toFun := circlesInclusion
  invFun := circlesRetraction
  left_inv := circlesRetraction_comp_circlesInclusion ▸ ContinuousMap.Homotopic.refl _
  right_inv := ⟨circlesHomotopyRel.toHomotopy⟩

@[simp]
theorem coe_circlesHomotopyEquiv : ⇑circlesHomotopyEquiv = circlesInclusion :=
  (rfl)

@[simp]
theorem coe_circlesHomotopyEquiv_symm : ⇑circlesHomotopyEquiv.symm = circlesRetraction :=
  (rfl)

/-- The **fundamental group of the punctured torus** at `0` is that of its two circles through
`0`: the isomorphism induced by their inclusion. -/
def circlesFundamentalGroupMulEquiv :
    FundamentalGroup circles ⟨0, zero_mem_circles⟩ ≃*
      FundamentalGroup (ConnectedSum.puncture ball) ⟨0, zero_mem_puncture⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map circlesInclusion ⟨0, zero_mem_circles⟩)
    (circlesHomotopyEquiv.fundamentalGroup_map_bijective _)

/-- The isomorphism maps the class of a loop in the two circles to that of the same loop in the
punctured torus. -/
@[simp]
theorem circlesFundamentalGroupMulEquiv_apply (a : FundamentalGroup circles ⟨0, zero_mem_circles⟩) :
    circlesFundamentalGroupMulEquiv a = FundamentalGroup.map circlesInclusion _ a :=
  (rfl)

/-! ### The fundamental group of the punctured torus as a surface group -/

/-- The two circles of the torus through `0`, carried to Tau Ceti's torus `Fin 2 → AddCircle 1`
by the identity `SymplecticGeometry.EuclideanTorus.diffeomorph`: the restriction of that
diffeomorphism, as a homeomorphism onto `SymplecticGeometry.torusCircles`. -/
def circlesHomeomorph : circles ≃ₜ torusCircles :=
  diffeomorph.toHomeomorph.subtype fun x ↦ by
    rw [mem_circles_iff, mem_torusCircles_iff, Diffeomorph.coe_toHomeomorph]

/-- The homeomorphism is `diffeomorph` on points. -/
@[simp]
theorem coe_circlesHomeomorph_apply (x : circles) :
    (circlesHomeomorph x : Fin 2 → AddCircle (1 : ℝ)) = diffeomorph (x : EuclideanTorus) := by
  rw [circlesHomeomorph, Homeomorph.subtype_apply_coe, Diffeomorph.coe_toHomeomorph]

/-- Its inverse is `diffeomorph.symm` on points. -/
@[simp]
theorem coe_circlesHomeomorph_symm_apply (y : torusCircles) :
    (circlesHomeomorph.symm y : EuclideanTorus) =
      diffeomorph.symm (y : Fin 2 → AddCircle (1 : ℝ)) := by
  rw [circlesHomeomorph, Homeomorph.subtype_symm_apply_coe, Diffeomorph.coe_toHomeomorph_symm]

/-- The homeomorphism keeps the base point `0`. -/
theorem circlesHomeomorph_zero :
    circlesHomeomorph ⟨0, zero_mem_circles⟩ = ⟨0, zero_mem_torusCircles⟩ :=
  Subtype.ext ((coe_circlesHomeomorph_apply _).trans diffeomorph_zero)

/-- The loop `t ↦ Pi.single i [t]` of the punctured torus at `0`, once around the `i`-th circle
through `0`: for `i = 0` the loop `t ↦ ([t], 0)`, for `i = 1` the loop `t ↦ (0, [t])`. It is
`SymplecticGeometry.torusCircleLoop i`, carried to the punctured torus. -/
def circleLoop (i : Fin 2) :
    Path (⟨0, zero_mem_puncture⟩ : ConnectedSum.puncture ball) ⟨0, zero_mem_puncture⟩ :=
  ((torusCircleLoop i).map
    (circlesInclusion.comp (circlesHomeomorph.symm : C(torusCircles, circles))).continuous).cast
    (Subtype.ext (by simp)) (Subtype.ext (by simp))

/-- The loop in the coordinates of `Fin 2 → AddCircle 1`. -/
@[simp]
theorem diffeomorph_circleLoop_apply (i : Fin 2) (t : I) :
    diffeomorph (circleLoop i t : EuclideanTorus) =
      Pi.single i ((t : ℝ) : AddCircle (1 : ℝ)) := by
  simp [circleLoop]

/-- The generators `0` and `1` of the free group on `Fin 2`, matched with the generators `a 0` and
`b 0` of Tau Ceti's `TauCeti.SurfaceGroup.Orientable.equivFreeGroup 1 0`. -/
private def generatorEquiv : Fin 2 ≃ Fin 1 ⊕ Fin 1 ⊕ Fin 0 :=
  (finSumFinEquiv (m := 1) (n := 1)).symm.trans
    (Equiv.sumCongr (.refl _) (Equiv.sumEmpty _ _).symm)

private theorem generatorEquiv_zero : generatorEquiv 0 = .inl 0 :=
  (rfl)

private theorem generatorEquiv_one : generatorEquiv 1 = .inr (.inl 0) :=
  (rfl)

/-- The **fundamental group of the punctured torus** at `0` is Tau Ceti's orientable surface group
`TauCeti.SurfaceGroup.Orientable 1 1`: the composite of the isomorphism with the group of its two
circles through `0`, of that group with the free group on `Fin 2`, and of Tau Ceti's
`TauCeti.SurfaceGroup.Orientable.equivFreeGroup 1 0`, the generators `0` and `1` going to
`a 0` and `b 0`. -/
def puncturedFundamentalGroupMulEquiv :
    FundamentalGroup (ConnectedSum.puncture ball) ⟨0, zero_mem_puncture⟩ ≃*
      SurfaceGroup.Orientable 1 1 :=
  circlesFundamentalGroupMulEquiv.symm.trans <|
    (FundamentalGroup.homeomorphMulEquivOfEq circlesHomeomorph circlesHomeomorph_zero).trans <|
      torusCirclesFundamentalGroupMulEquiv.trans <|
        (FreeGroup.freeGroupCongr generatorEquiv).trans
          (SurfaceGroup.Orientable.equivFreeGroup 1 0).symm

/-- The class of `circleLoop i` in the punctured torus, read in the two circles of
`Fin 2 → AddCircle 1`, is that of `torusCircleLoop i`. -/
private theorem homeomorphMulEquivOfEq_symm_circleLoop (i : Fin 2) :
    FundamentalGroup.homeomorphMulEquivOfEq circlesHomeomorph circlesHomeomorph_zero
        (circlesFundamentalGroupMulEquiv.symm
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop i)))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusCircleLoop i)) := by
  rw [← MulEquiv.eq_symm_apply, MulEquiv.symm_apply_eq, circlesFundamentalGroupMulEquiv_apply,
    FundamentalGroup.homeomorphMulEquivOfEq_symm_apply, ← FundamentalGroup.mapOfEq_rfl,
    FundamentalGroup.mapOfEq_comp, FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, circleLoop]
  -- `FundamentalGroup.fromPath` is the abbreviation `CategoryTheory.End.of`.
  rfl

/-- The isomorphism sends the class of `circleLoop i` to the image of the generator
`generatorEquiv i` under Tau Ceti's `TauCeti.SurfaceGroup.Orientable.equivFreeGroup 1 0`. -/
private theorem puncturedFundamentalGroupMulEquiv_circleLoop (i : Fin 2) :
    puncturedFundamentalGroupMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop i))) =
      (SurfaceGroup.Orientable.equivFreeGroup 1 0).symm (FreeGroup.of (generatorEquiv i)) := by
  rw [puncturedFundamentalGroupMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    homeomorphMulEquivOfEq_symm_circleLoop, MulEquiv.trans_apply,
    torusCirclesFundamentalGroupMulEquiv_torusCircleLoop, MulEquiv.trans_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]

/-- The isomorphism sends the class of the loop `t ↦ ([t], 0)` to the generator `a 0`. -/
@[simp]
theorem puncturedFundamentalGroupMulEquiv_circleLoop_zero :
    puncturedFundamentalGroupMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop 0))) =
      SurfaceGroup.Orientable.a 1 1 0 := by
  rw [puncturedFundamentalGroupMulEquiv_circleLoop, generatorEquiv_zero,
    SurfaceGroup.Orientable.equivFreeGroup_symm_of_inl]

/-- The isomorphism sends the class of the loop `t ↦ (0, [t])` to the generator `b 0`. -/
@[simp]
theorem puncturedFundamentalGroupMulEquiv_circleLoop_one :
    puncturedFundamentalGroupMulEquiv
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop 1))) =
      SurfaceGroup.Orientable.b 1 1 0 := by
  rw [puncturedFundamentalGroupMulEquiv_circleLoop, generatorEquiv_one,
    SurfaceGroup.Orientable.equivFreeGroup_symm_of_inr_inl]

end EuclideanTorus

end SymplecticGeometry

end
